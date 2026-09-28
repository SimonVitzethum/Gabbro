#!/usr/bin/env bash
# instrumente/pruefe-kernelmodul.sh -- a Gabbro unit AS A LINUX KERNEL MODULE,
# built and LOADED, in QEMU only (server lane, TODO section 0e K4/K5).
#
# THE QUESTION: does a Gabbro program with a bounded heap become a Linux kernel
# module that loads, allocates, hits refuse-on-full where the program says so,
# reports it, and unloads with no oops and no warning?
#
# IN QEMU ONLY, and that is a hard rule of this machine (`~/claude-lane/REGELN.md`):
# nothing built here is ever `insmod`ed into the host kernel. The harness boots
# a copy of this host's kernel (`~/claude-lane/vm/vmlinuz`, 6.8.0-139-generic)
# with a busybox initramfs, loads the module there, reads `dmesg`, unloads, and
# powers the machine off.
#
# THE RECIPE:
#   1. `gabbro emit` the unit;
#   2. build the module against the host's kernel headers: the emitted C, the
#      program's OWN foreign bodies, `laufzeit/kmodul/kmodul.c` (the driver,
#      not generated -- the unit's names arrive as -D macros) and
#      `laufzeit/kmodul/arena.c` (the bounded heap);
#   3. boot QEMU, `insmod` with a PROVISION smaller than the program's declared
#      ceiling, `rmmod`, and hold the kernel log against the expected lines.
#
# WHAT MAKES A GREEN RUN A MEASUREMENT -- the Sprechprobe (speech test) of this
# instrument:
# `--gift N` mutates the harness and the run must turn RED. The mutations are listed in `gifte()` below; `--gift all`
# runs every one of them and reports how many were caught.
#
# Missing `qemu-system-x86_64`, `busybox`, `cpio`, the kernel headers or the VM
# kernel prints `KERNELMODUL: NOT RUN` with the reason -- never a pass line.
#
# Usage: instrumente/pruefe-kernelmodul.sh [--gift N|all] [--keep]
set -u

W="$(cd "$(dirname "$0")/.." && pwd)"
GIFT=""
KEEP=0
while [ $# -gt 0 ]; do
    case "$1" in
        --gift) shift; GIFT="$1" ;;
        --keep) KEEP=1 ;;
        *) echo "pruefe-kernelmodul.sh: unknown argument '$1'" >&2; exit 2 ;;
    esac
    shift
done

# -- what the probe expects, in one place -------------------------------------
#
# `messung/proben/kmodul/halde-treiber.gab` declares `arena Knoten capacity
# 2 .. 4 max 4096 of Wert` (8-byte slots) and grows it three times by 1024. The
# whole-run upper bound is 4 + 3072 = 3076 slots, below the ceiling, so `N426`
# admits all three. The PROVISION below is 24 KiB = 3072 slots' worth minus a
# little: two grows fit (4 + 2048 = 2052 slots = 16416 bytes), the third does
# not (3076 slots = 24608 bytes > 24576). So the third `grow` is refused BELOW
# the ceiling and the program's `else` runs -- refuse-on-full, deliberately
# reached, not hoped for.
QUELLE="$W/messung/proben/kmodul/halde-treiber.gab"
FREMD="$W/messung/proben/kmodul/melde.c"
MODUL=gabbro_halde
INIT=laden
EXIT=entladen
# **The arenas are NOT named here.** The emitted unit carries its own list
# (`#define GABBRO_ARENEN &Knoten_desc`, emitter, 2026-09-28) -- a harness that
# repeated it would be the second register over one fact, and the one nobody
# reads is the one that drifts (`W7`).
VORRAT_KIB=24
# The kernel lines the run must show, in this order. `k=2 v=33` is the read-back
# (11 + 22 through the arena), `k=3 v=3` is the THIRD grow refusing.
ERWARTET="gabbro-halde: k=1 v=0
gabbro-halde: k=2 v=33
gabbro-halde: k=3 v=3
gabbro-halde: k=9 v=0"

KERNVERSION="$(uname -r)"
KBUILD="/lib/modules/$KERNVERSION/build"
VMLINUZ="${GABBRO_VMLINUZ:-$HOME/claude-lane/vm/vmlinuz}"

nicht_gelaufen() {
    echo "KERNELMODUL: NOT RUN -- $1"
    exit 2
}

for werkzeug in qemu-system-x86_64 busybox cpio make gzip; do
    command -v "$werkzeug" >/dev/null 2>&1 || nicht_gelaufen "no $werkzeug on this machine"
done
[ -d "$KBUILD" ]  || nicht_gelaufen "no kernel headers at $KBUILD"
[ -r "$VMLINUZ" ] || nicht_gelaufen "no VM kernel at $VMLINUZ (set GABBRO_VMLINUZ)"
[ -f "$QUELLE" ]  || nicht_gelaufen "no probe source at $QUELLE"

# **Which binary, and is it newer than the sources?** One register, one file:
# `instrumente/binaer.sh` -- and this instrument is one of the three the trap bit.
. "$(dirname "$0")/binaer.sh"
GABBRO="$(gabbro_binaer "$W")" || nicht_gelaufen "$GABBRO"

# -- the mutations (`--gift`) --------------------------------------------------
#
# Each one is a change to the HARNESS or to what it feeds the kernel, and each
# one must turn the run red. They are chosen so that no two are caught by the
# same check:
#
#   1 the expected read-back value moves (33 -> 34): does the run really read
#     the kernel log, or does it only look at insmod's exit code?
#   2 the provision is raised past the third grow (24 -> 64 KiB): the refusal
#     line `k=3 v=3` must then be MISSING -- does the run notice a line that
#     did not come, or only lines that did?
#   3 the module's unload line is dropped from the expectation's check by
#     rmmod'ing nothing: does the run see an unload that did not happen?
#   4 the emitted C is replaced by one whose arena ceiling is 4 (below the
#     grows the program makes): every `grow` is then past `max`, which is a
#     fail-stop and not a branch, and the load must refuse.
#     *This gift found something.* The first time it ran, `insmod` SUCCEEDED:
#     the runtime set its load error and returned false, the program's `else`
#     ran, the unit answered 0, and `module_init` -- which read the load error
#     only BEFORE calling the unit -- let the module in. A fail-stop that does
#     not reach the loader is not a fail-stop. `laufzeit/kmodul/kmodul.c` now
#     reads it again after the unit's init, and the gift is caught at
#     `insmod` as well as in the log.
gifte() { echo "1 2 3 4"; }

lauf_einmal() {   # $1 = gift number or "", echoes the QEMU output; returns build rc
    local gift="$1"
    local arb="$2"
    local vorrat="$VORRAT_KIB"
    local rmmod_zeile="/bin/busybox rmmod $MODUL && echo \"HARNESS: rmmod ok\" || echo \"HARNESS: rmmod FAILED\""

    # **The module is built by `gabbro build`, not by this harness** (server lane,
    # 2026-09-28). Until today the Kbuild, the runtime copies and the `-D`s stood HERE, in
    # shell, and `gabbro build` could not make a kernel module at all -- two registers over
    # one artefact, and the one in the shell is the one a user never gets (`W7`). The
    # manifest below is the whole of what this harness now knows about building: two paths
    # and the two calls the kernel makes.
    mkdir -p "$arb"
    cat > "$arb/manifest" <<EOF
-- written by instrumente/pruefe-kernelmodul.sh
compiler cc -std=c11 -Wall -Wextra -Werror
out $arb/bau
kmod $W/laufzeit/kmodul $KBUILD
unit $MODUL module $INIT $EXIT
  $QUELLE
  $FREMD
EOF
    if ! "$GABBRO" build "$arb/manifest" > "$arb/bau.log" 2>&1; then
        echo "HARNESS: gabbro build FAILED"
        tail -25 "$arb/bau.log" >&2
        return 0
    fi
    if [ "$gift" = 4 ]; then
        # **A ceiling of 4 slots: every `grow` is past it**, so the runtime fail-stops and
        # `module_init` must refuse the load. The mutation is on the EMITTED C inside the
        # build directory `gabbro build` left behind, and the module is re-made with the
        # `Kbuild` the build wrote -- so this gift carries no second copy of the recipe
        # either. (Mutating the SOURCE would be refused by `N426` one door earlier, and
        # then the fail-stop never runs.)
        local kdir="$arb/bau/$MODUL.kmod"
        sed -i 's/(uint32_t)(4096)/(uint32_t)(4)/' "$kdir/einheit.c"
        sed -i 's/_Static_assert((4) <= (4096)/_Static_assert((4) <= (4)/' "$kdir/einheit.c"
        rm -f "$kdir/$MODUL.ko" "$kdir"/*.o
        if ! make -C "$KBUILD" "M=$(cd "$kdir" && pwd)" modules > "$arb/make.log" 2>&1; then
            echo "HARNESS: the mutated module did not build"
            tail -20 "$arb/make.log" >&2
            return 0
        fi
        cp "$kdir/$MODUL.ko" "$arb/bau/$MODUL.ko"
    fi

    [ "$gift" = 2 ] && vorrat=64
    [ "$gift" = 3 ] && rmmod_zeile="echo \"HARNESS: rmmod ok\""

    rm -rf "$arb/initrd"
    mkdir -p "$arb/initrd/bin" "$arb/initrd/proc" "$arb/initrd/sys"
    cp "$(command -v busybox)" "$arb/initrd/bin/busybox"
    ( cd "$arb/initrd/bin" && for a in sh mount insmod rmmod dmesg grep; do ln -sf busybox "$a"; done )
    cp "$arb/bau/$MODUL.ko" "$arb/initrd/"
    cat > "$arb/initrd/init" <<EOF
#!/bin/sh
/bin/busybox mount -t proc none /proc
/bin/busybox mount -t sysfs none /sys
echo "HARNESS: begin"
/bin/busybox insmod /$MODUL.ko vorrat_kib=$vorrat && echo "HARNESS: insmod ok" || echo "HARNESS: insmod FAILED"
$rmmod_zeile
/bin/busybox dmesg | /bin/busybox grep -E "gabbro|Oops|BUG:|WARNING:"
echo "HARNESS: end"
/bin/busybox poweroff -f
EOF
    chmod +x "$arb/initrd/init"
    ( cd "$arb/initrd" && find . | cpio -o -H newc 2>/dev/null | gzip -9 > "$arb/initrd.gz" )

    timeout 600 qemu-system-x86_64 -kernel "$VMLINUZ" -initrd "$arb/initrd.gz" \
        -append "console=ttyS0 quiet panic=1" -nographic -m 512 -no-reboot \
        2>&1 | tr -d '\r'
}

# -- the verdict over one run --------------------------------------------------
beurteile() {   # $1 = output file, $2 = gift number or ""
    local aus="$1" gift="$2" fehler=0
    local erwartet="$ERWARTET"
    [ "$gift" = 1 ] && erwartet="$(echo "$erwartet" | sed 's/v=33/v=34/')"

    grep -q "HARNESS: end" "$aus" || { echo "RED: the harness never reached its end (boot or QEMU)"; fehler=$((fehler+1)); }
    grep -q "HARNESS: insmod ok" "$aus" || { echo "RED: insmod did not succeed"; fehler=$((fehler+1)); }
    grep -q "HARNESS: rmmod ok" "$aus" || { echo "RED: rmmod did not succeed"; fehler=$((fehler+1)); }

    # Every expected kernel line, in order, and nothing missing.
    local vorher=0 zeile n
    while IFS= read -r zeile; do
        [ -z "$zeile" ] && continue
        n=$(grep -n -F -- "$zeile" "$aus" | head -1 | cut -d: -f1)
        if [ -z "$n" ]; then
            echo "RED: the kernel log is missing: $zeile"
            fehler=$((fehler+1))
        elif [ "$n" -le "$vorher" ]; then
            echo "RED: out of order: $zeile"
            fehler=$((fehler+1))
        else
            vorher="$n"
        fi
    done <<EOF
$erwartet
EOF

    # No oops, no warning, no BUG -- the module left the kernel as it found it.
    if grep -qE "Oops|BUG:|WARNING:|general protection|kernel NULL pointer" "$aus"; then
        echo "RED: the kernel complained:"
        grep -E "Oops|BUG:|WARNING:|general protection|kernel NULL pointer" "$aus" | head -5
        fehler=$((fehler+1))
    fi
    echo "FEHLER=$fehler"
}

ARB="$(mktemp -d "${TMPDIR:-/tmp}/gabbro-kmod.XXXXXX")"
if [ "$KEEP" = 0 ]; then trap 'rm -rf "$ARB"' EXIT; fi

if [ -z "$GIFT" ]; then
    echo "== a Gabbro unit as a Linux kernel module, in QEMU =="
    echo "   source      $QUELLE"
    echo "   kernel      $VMLINUZ ($KERNVERSION headers)"
    echo "   provision   vorrat_kib=$VORRAT_KIB (the program's ceiling is max 4096 slots)"
    lauf_einmal "" "$ARB" > "$ARB/aus.txt"
    grep -E "HARNESS:|gabbro" "$ARB/aus.txt" | sed 's/^/   /'
    echo
    ergebnis="$(beurteile "$ARB/aus.txt" "")"
    echo "$ergebnis" | grep -v '^FEHLER=' || true
    n="$(echo "$ergebnis" | sed -n 's/^FEHLER=//p')"
    if [ "$n" = 0 ]; then
        echo "GREEN: loaded, allocated, refused on full, reported, unloaded clean."
        exit 0
    fi
    echo "RED: $n finding(s)."
    exit 1
fi

# -- the poison runs -----------------------------------------------------------
if [ "$GIFT" = all ]; then
    LISTE="$(gifte)"
else
    LISTE="$GIFT"
fi
gefangen=0
gesamt=0
for g in $LISTE; do
    gesamt=$((gesamt+1))
    arb="$ARB/g$g"
    mkdir -p "$arb"
    lauf_einmal "$g" "$arb" > "$arb/aus.txt"
    ergebnis="$(beurteile "$arb/aus.txt" "$g")"
    n="$(echo "$ergebnis" | sed -n 's/^FEHLER=//p')"
    if [ "$n" = 0 ]; then
        echo "GIFT $g: NOT CAUGHT -- the harness stayed green under the mutation"
    else
        echo "GIFT $g: caught ($n finding(s))"
        echo "$ergebnis" | grep '^RED' | head -3 | sed 's/^/    /'
        gefangen=$((gefangen+1))
    fi
done
echo
echo "gifts: $gefangen of $gesamt caught"
[ "$gefangen" = "$gesamt" ]
