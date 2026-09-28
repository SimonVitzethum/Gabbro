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
#      not generated -- the unit's names arrive as -D macros),
#      `laufzeit/kmodul/arena.c` (the bounded heap) and
#      `laufzeit/kmodul/sperre.h` over the generated `sperren.h` (the locks: a
#      `masks irqs` lock becomes `raw_spin_lock_irqsave`);
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

# -- the two probes, and what each expects, in one place ----------------------
#
# THREE PROBES, because the module target answers three questions and one
# program cannot ask them all. `halde` is the bounded heap (acceptance point 3);
# `takt` is `masks irqs` (K3); `atomar` is a Gabbro `atomic` lowered onto the
# kernel's own memory model (K6, acceptance point 4b). They share everything
# below this block -- one build recipe, one initramfs shape, one verdict
# function.
#
# `halde` -- `messung/proben/kmodul/halde-treiber.gab` declares `arena Knoten
# capacity 2 .. 4 max 4096 of Wert` (8-byte slots) and grows it three times by
# 1024. The whole-run upper bound is 4 + 3072 = 3076 slots, below the ceiling,
# so `N426` admits all three. The PROVISION is 24 KiB = 3072 slots' worth minus
# a little: two grows fit (4 + 2048 = 2052 slots = 16416 bytes), the third does
# not (3076 slots = 24608 bytes > 24576). So the third `grow` is refused BELOW
# the ceiling and the program's `else` runs -- refuse-on-full, deliberately
# reached, not hoped for.
#
# `takt` -- `messung/proben/kmodul/sperre-takt.gab` holds a `masks irqs` lock
# across a 4096-slot traversal, 64 times over, while the program's own C runs a
# 50 us hardirq timer whose body takes the same lock. `landed=0` says no
# interrupt ever arrived on a core that was holding it; `ticks` says the timer
# fired at all, WITHOUT WHICH `landed=0` measures nothing. Both are checked.
#
# `atomar` -- `messung/proben/kmodul/atomar-faeden.gab` declares TWO CONCURRENT
# ROOTS and four atomics. `gabbro build` writes the roots into `wurzeln.h` and
# the module runtime starts one `kthread` per root, joining both before the
# unload function reports. The four numbers the run must show are exact and each
# one is a different row of the mapping: a saturating counter bumped 256 times
# by each root (the bounded CAS loop -> `try_cmpxchg_relaxed`, answer 512), how
# often the release/acquire flag was seen set (`smp_store_release` /
# `smp_load_acquire`; > 0, or the run measured nothing), how often it was seen
# set over a payload that was still 0 (must be 0), and a bit word each root ORs
# its own bit into (one `atomic_fetch_or_explicit` -> the fully ordered
# `try_cmpxchg`, answer 3).
#
# **A green run of this probe does not measure the BARRIERS**, and the file says
# so: on x86 acquire and release are free, so no run here could tell a correct
# mapping from one that dropped them. That is what the mapping stage below is
# for -- it expands every (form, ordering) pair and holds it against the
# primitive the row requires, and gift 8 is a deliberately too-weak mapping.
#
# **The arenas, the locks and the roots are NOT named here.** The emitted unit
# carries its own arena list (`#define GABBRO_ARENEN`, emitter) and `gabbro build`
# writes the lock list and the root list beside it (`sperren.h`, `wurzeln.h`, out
# of the same walk the hosted and the bare-metal driver read) -- a harness that
# repeated any of them would be a second register over one fact, and the one
# nobody reads is the one that drifts (`W7`).
PROBEN="halde takt atomar"

probe_waehle() {   # $1 = probe name; sets QUELLE FREMD MODUL INIT EXIT PARAM ERWARTET FRIST
    # **Every per-probe variable is cleared first.** Without this line `TICKS_MIN`
    # survived from one probe into the next and `halde` -- which has no timer --
    # was RED for a tick count it never claimed to have. *A selector that only
    # ever sets is a selector that carries the last probe's answer.*
    unset TICKS_MIN GESEHEN_MIN ABBILDUNG
    QUELLE=""; FREMD=""; MODUL=""; INIT=""; EXIT=""; PARAM=""; ERWARTET=""; FRIST=600
    # One vCPU unless the probe needs two; TCG is slow and a second core costs
    # boot time that only the concurrent probe has a use for.
    SMP=1
    case "$1" in
        halde)
            QUELLE="$W/messung/proben/kmodul/halde-treiber.gab"
            FREMD="$W/messung/proben/kmodul/melde.c"
            MODUL=gabbro_halde
            INIT=laden
            EXIT=entladen
            PARAM="vorrat_kib=24"
            # The kernel lines the run must show, in this order. `k=2 v=33` is
            # the read-back (11 + 22 through the arena), `k=3 v=3` is the THIRD
            # grow refusing.
            ERWARTET="gabbro-halde: k=1 v=0
gabbro-halde: k=2 v=33
gabbro-halde: k=3 v=3
gabbro-halde: k=9 v=0"
            ;;
        takt)
            QUELLE="$W/messung/proben/kmodul/sperre-takt.gab"
            FREMD="$W/messung/proben/kmodul/takt.c"
            MODUL=gabbro_takt
            INIT=laden
            EXIT=entladen
            PARAM=""
            # A run of this probe finishes in about five seconds; the poison run
            # that takes the lock UNMASKED does not finish at all (the timer body
            # waits for the core it interrupted). 45 s is far past the first and
            # far short of an hour.
            FRIST=45
            ERWARTET="gabbro-takt: k=1 v=0
landed=0
gabbro-takt: k=9 v=0"
            # A run whose timer never fired reports a clean `landed` and has
            # measured nothing (`W1`): the verdict below demands this many ticks.
            TICKS_MIN=5
            ;;
        atomar)
            QUELLE="$W/messung/proben/kmodul/atomar-faeden.gab"
            FREMD="$W/messung/proben/kmodul/atomar.c"
            MODUL=gabbro_atomar
            INIT=laden
            EXIT=entladen
            PARAM=""
            # Two vCPUs, so the two declared roots really run at the same time.
            # With one, a lost update in the CAS loop would need a preemption to
            # show at all -- the answer would be 512 either way and the run would
            # measure the counter's arithmetic, not its atomicity.
            SMP=2
            FRIST=120
            # The four numbers, exact, in the order the unload function writes
            # them. `k=2 v=512` is the counter (256 rounds x 2 roots), `k=4 v=0`
            # the payload check, `k=5 v=3` the two bits.
            ERWARTET="gabbro-atomar: k=1 v=0
gabbro-atomar: k=2 v=512
gabbro-atomar: k=4 v=0
gabbro-atomar: k=5 v=3
gabbro-atomar: k=9 v=0"
            # `k=3` is NOT in the list above, because it is not a constant: how
            # often the consumer saw the flag set depends on the scheduling. A
            # run in which it was never seen reports a clean `k=4 v=0` and has
            # measured NOTHING about the flag (`W1`), so the verdict demands a
            # minimum instead of a value -- the same shape `takt` gives `ticks`.
            GESEHEN_MIN=1
            # And the mapping itself is checked where the module was BUILT: the
            # rows are expanded and held against the primitives they require.
            ABBILDUNG=1
            ;;
        *) echo "pruefe-kernelmodul.sh: no such probe '$1'" >&2; exit 2 ;;
    esac
}

# -- the mapping, measured by EXPANDING it (server lane, TODO section 0e K6) ---
#
# THE PROBLEM THIS SOLVES. `atomic` in a kernel module is lowered by
# `laufzeit/kmodul/include/stdatomic.h`: one row per (call form, ordering), each
# row at least as strong as the C11 operation it replaces. A row that was
# quietly too weak -- acquire as `READ_ONCE`, release as `WRITE_ONCE` -- would
# compile, load, run and answer every expected number, BECAUSE THIS IS x86:
# acquire and release are free there, and the barriers the mapping owes a
# weak-memory architecture leave no trace in a green run on this machine.
# *A measurement that cannot fail is not a measurement* (`W1`).
#
# So the mapping is measured where it can fail: in the PREPROCESSOR. Each row is
# expanded on its own line and held against the primitive it must use. The
# expansion is of the header IN THE BUILD DIRECTORY -- the copy the `.ko` was
# actually built from -- so this is not a reading of the tree but of the
# artefact, and gift 8 (a deliberately too-weak mapping) is caught here.
#
# The kernel's own headers are STUBBED OUT, empty, and that is what makes the
# check readable: `READ_ONCE` and `smp_load_acquire` then stay as tokens instead
# of expanding into inline assembly. What is measured is which primitive the row
# selects, which is exactly the claim the named assumption (M11) rests on.
#
# The table below is a SPECIFICATION and the header is its implementation, so
# the two are not a second register over one fact: this is the shape of a poison
# probe, not of a duplicated list.
abbildung_pruefe() {   # $1 = the module build dir (its `inc/` holds stdatomic.h)
    local kdir="$1" arb="$1/abbildung" befunde=0 zeile marke muss text
    rm -rf "$arb"; mkdir -p "$arb/stubs/linux"
    : > "$arb/stubs/linux/compiler.h"
    : > "$arb/stubs/linux/atomic.h"
    : > "$arb/stubs/linux/types.h"
    cat > "$arb/rows.c" <<'EOF'
#include <stdatomic.h>
_Atomic unsigned int A;
void f(void) {
Z01 atomic_load_explicit(&A, memory_order_relaxed);
Z02 atomic_load_explicit(&A, memory_order_acquire);
Z03 atomic_load_explicit(&A, memory_order_seq_cst);
Z04 atomic_store_explicit(&A, 1u, memory_order_relaxed);
Z05 atomic_store_explicit(&A, 1u, memory_order_release);
Z06 atomic_store_explicit(&A, 1u, memory_order_seq_cst);
Z07 atomic_fetch_add_explicit(&A, 1u, memory_order_relaxed);
Z08 atomic_fetch_add_explicit(&A, 1u, memory_order_acq_rel);
Z09 atomic_fetch_add_explicit(&A, 1u, memory_order_seq_cst);
Z10 atomic_fetch_or_explicit(&A, 1u, memory_order_relaxed);
Z11 atomic_compare_exchange_weak_explicit(&A, &A, 1u, memory_order_relaxed, memory_order_relaxed);
Z12 atomic_compare_exchange_strong_explicit(&A, &A, 1u, memory_order_release, memory_order_acquire);
Z13 atomic_compare_exchange_weak_explicit(&A, &A, 1u, memory_order_seq_cst, memory_order_seq_cst);
}
EOF
    if ! cc -E -P -nostdinc -I "$arb/stubs" -I "$kdir/inc" "$arb/rows.c" \
            > "$arb/rows.i" 2> "$arb/rows.err"; then
        echo "HARNESS: mapping FAILED -- the header did not preprocess"
        sed 's/^/    /' "$arb/rows.err" | head -5
        return 0
    fi
    # marker | what the row MUST select | the row in words
    while IFS='|' read -r marke muss was; do
        [ -z "$marke" ] && continue
        # One source line expands to one output line -- a macro expansion never
        # introduces a newline -- so a row is exactly the line its marker opens.
        text="$(grep -m1 "^$marke" "$arb/rows.i")"
        if [ -z "$text" ]; then
            echo "HARNESS: mapping FAILED -- the row $was ($marke) did not survive preprocessing"
            befunde=$((befunde+1))
            continue
        fi
        if ! printf '%s' "$text" | grep -qE "$muss"; then
            echo "HARNESS: mapping FAILED -- $was does not select $muss"
            befunde=$((befunde+1))
        fi
    done <<'EOF'
Z01|READ_ONCE|load relaxed
Z02|smp_load_acquire|load acquire
Z03|smp_mb.*smp_load_acquire.*smp_mb|load seq_cst
Z04|WRITE_ONCE|store relaxed
Z05|smp_store_release|store release
Z06|smp_mb.*smp_store_mb|store seq_cst
Z07|try_cmpxchg_relaxed|fetch_add relaxed
Z08|try_cmpxchg[^_]|fetch_add acq_rel (the unsuffixed, fully ordered form)
Z09|smp_mb.*try_cmpxchg[^_].*smp_mb|fetch_add seq_cst
Z10|try_cmpxchg_relaxed|fetch_or relaxed
Z11|try_cmpxchg_relaxed|compare-exchange (relaxed, relaxed)
Z12|try_cmpxchg_release.*smp_mb|compare-exchange (release, acquire) with its failure fence
Z13|smp_mb.*try_cmpxchg[^_].*smp_mb|compare-exchange (seq_cst, seq_cst)
EOF
    if [ "$befunde" = 0 ]; then
        echo "HARNESS: mapping ok (13 rows expanded and held against their primitive)"
    fi
}

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
for p in $PROBEN; do
    probe_waehle "$p"
    [ -f "$QUELLE" ] || nicht_gelaufen "no probe source at $QUELLE"
    [ -f "$FREMD" ]  || nicht_gelaufen "no probe C body at $FREMD"
done

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
#
# The `takt` probe's three (K3, and 5 is the one that is about the LOWERING and
# not about the harness):
#
#   5 the generated lock list (`sperren.h`) is edited from `F(TAKT, MASKED)` to
#     `F(TAKT, PLAIN)` and the module re-made with the `Kbuild` the build wrote:
#     the lock then takes `raw_spin_lock` instead of `raw_spin_lock_irqsave`, the
#     hardirq timer body lands inside a critical section on the core that holds
#     it, and waits for that core. *The run does not finish* -- exactly what the
#     bare-metal harness sees for the same mutation (`pruefe-metall.sh`, image
#     `metall59-gift`). This is the poison probe of the masking itself: without
#     it, GREEN would only say that nothing bad happened to be observed.
#   6 the timer period is raised past the whole run (50 us -> 50 s) in the
#     program's own C: the timer then never fires, `ticks=0`, and the run must be
#     RED because it measured NOTHING -- a clean `landed=0` over zero
#     opportunities is not a measurement (`W1`).
#   7 the expected `landed=0` moves to `landed=1`: does the run read the kernel
#     log, or only the exit codes? (The `halde` twin of this is gift 1.)
#
# The `atomar` probe's three (K6, and 8 is the one that is about the LOWERING
# and not about the harness):
#
#   8 the ATOMIC MAPPING is made deliberately too weak in the copy the module
#     was built from (`inc/stdatomic.h`): acquire becomes `READ_ONCE` and
#     release becomes `WRITE_ONCE`. **On x86 the run would still answer every
#     expected number** -- acquire and release are free there -- so a harness
#     that only booted the module would call this green, and the barriers a
#     weak-memory architecture is owed would be gone in silence. It is caught by
#     the mapping stage, which expands the rows and holds each against the
#     primitive it must select. *This gift is the reason that stage exists.*
#   9 a PLAIN ACCESS replaces one of the calls in the emitted C
#     (`atomic_load_explicit(&NUTZLAST, …)` becomes `NUTZLAST`). On a C11
#     `_Atomic` object that would still be an atomic operation; in the module
#     target `_Atomic` is `volatile`, so it is an unordered access that compiles
#     without a word. Caught by `instrumente/pruefe-atomar-zugriffe.py` over the
#     emitted C in the build directory.
#  10 the expected counter moves (512 -> 513): does the run read the kernel log?
#     (The `halde` twin is gift 1, the `takt` twin gift 7.)
gifte() { echo "1 2 3 4 5 6 7 8 9 10"; }

# Which probe a gift belongs to -- a gift is a mutation OF a run, and a run is
# of one probe.
gift_probe() {
    case "$1" in
        1|2|3|4)  echo halde ;;
        5|6|7)    echo takt ;;
        8|9|10)   echo atomar ;;
        *) echo "pruefe-kernelmodul.sh: no such gift '$1'" >&2; exit 2 ;;
    esac
}

lauf_einmal() {   # $1 = gift number or "", $2 = work dir, $3 = probe
    local gift="$1"
    local arb="$2"
    probe_waehle "$3"
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
    if [ "$gift" = 5 ] || [ "$gift" = 6 ]; then
        # **The two `takt` mutations that need a re-make**, both on what the build
        # left behind, so neither carries a second copy of the recipe:
        #   5 the lock loses its mask in the unit's OWN list -- the lowering poison;
        #   6 the timer period is raised past the run in the program's OWN C, so the
        #     timer never fires and the run measures nothing.
        local kdir="$arb/bau/$MODUL.kmod"
        if [ "$gift" = 5 ]; then
            # The lock list is a GENERATED file beside the emitted C (`sperren.h`, written by
            # `gabbro build` out of the same walk the other two drivers read). *It stood in
            # `einheit.c` for one afternoon, and when it moved this mutation stopped applying
            # and the gift read NOT CAUGHT -- a gift that does not apply looks exactly like a
            # pass, and here the instrument said so itself.*
            grep -q 'F(TAKT, MASKED)' "$kdir/sperren.h" || {
                echo "HARNESS: gift 5 does not apply -- no F(TAKT, MASKED) in sperren.h"
                return 0
            }
            sed -i 's/F(TAKT, MASKED)/F(TAKT, PLAIN)/' "$kdir/sperren.h"
        else
            sed -i 's/GABBRO_TAKT_NS 50000ull/GABBRO_TAKT_NS 50000000000ull/' "$kdir/gabbro_fremd0.c"
        fi
        rm -f "$kdir/$MODUL.ko" "$kdir"/*.o
        if ! make -C "$KBUILD" "M=$(cd "$kdir" && pwd)" modules > "$arb/make.log" 2>&1; then
            echo "HARNESS: the mutated module did not build"
            tail -20 "$arb/make.log" >&2
            return 0
        fi
        cp "$kdir/$MODUL.ko" "$arb/bau/$MODUL.ko"
    fi
    if [ "$gift" = 8 ] || [ "$gift" = 9 ]; then
        # **The two `atomar` mutations that need a re-make**, both on what the build
        # left behind, so neither carries a second copy of the recipe:
        #   8 the mapping is made too weak in the copy the module is built from;
        #   9 a plain access replaces one of the nine calls in the emitted C.
        local kdir="$arb/bau/$MODUL.kmod"
        if [ "$gift" = 8 ]; then
            # **The two rows are matched WHOLE and by fixed string**, and both
            # before and after. A looser pattern (`smp_load_acquire(P)`) also
            # stands in the seq_cst row, so the "did it apply?" question would
            # have answered NO over a mutation that had applied perfectly --
            # and a gift that does not apply is reported as such below, never
            # as a catch.
            local zeile_a='    ({ GABBRO_KMOD_ATOMAR_TYP(P); smp_load_acquire(P); })'
            local zeile_r='    ({ GABBRO_KMOD_ATOMAR_TYP(P); smp_store_release(P, (V)); })'
            local h="$kdir/inc/stdatomic.h"
            grep -Fq "$zeile_a" "$h" && grep -Fq "$zeile_r" "$h" || {
                echo "HARNESS: gift 8 does not apply -- the acquire/release rows are not where it looks"
                return 0
            }
            sed -i 's/({ GABBRO_KMOD_ATOMAR_TYP(P); smp_load_acquire(P); })/({ GABBRO_KMOD_ATOMAR_TYP(P); READ_ONCE(*(P)); })/' "$h"
            sed -i 's/({ GABBRO_KMOD_ATOMAR_TYP(P); smp_store_release(P, (V)); })/({ GABBRO_KMOD_ATOMAR_TYP(P); WRITE_ONCE(*(P), (V)); })/' "$h"
            if grep -Fq "$zeile_a" "$h" || grep -Fq "$zeile_r" "$h"; then
                echo "HARNESS: gift 8 does not apply -- a row did not change"
                return 0
            fi
        else
            grep -q 'atomic_load_explicit(&NUTZLAST, memory_order_relaxed)' "$kdir/einheit.c" || {
                echo "HARNESS: gift 9 does not apply -- no relaxed load of NUTZLAST in einheit.c"
                return 0
            }
            sed -i 's/atomic_load_explicit(&NUTZLAST, memory_order_relaxed)/NUTZLAST/' "$kdir/einheit.c"
        fi
        rm -f "$kdir/$MODUL.ko" "$kdir"/*.o
        if ! make -C "$KBUILD" "M=$(cd "$kdir" && pwd)" modules > "$arb/make.log" 2>&1; then
            echo "HARNESS: the mutated module did not build"
            tail -20 "$arb/make.log" >&2
            return 0
        fi
        cp "$kdir/$MODUL.ko" "$arb/bau/$MODUL.ko"
    fi

    # **The two STATIC checks over what was built**, for the probe that asks for
    # them. They run after every mutation above, on the build directory itself --
    # so what they measure is the artefact the kernel loaded and not the tree.
    if [ -n "${ABBILDUNG:-}" ]; then
        abbildung_pruefe "$arb/bau/$MODUL.kmod"
        if "$W/instrumente/pruefe-atomar-zugriffe.py" "$arb/bau/$MODUL.kmod/einheit.c" \
                > "$arb/zugriffe.log" 2>&1; then
            echo "HARNESS: atomic accesses ok"
        else
            echo "HARNESS: atomic accesses FAILED"
            grep -A2 '^RED' "$arb/zugriffe.log" | head -3
        fi
    fi

    [ "$gift" = 2 ] && PARAM="vorrat_kib=64"
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
/bin/busybox insmod /$MODUL.ko $PARAM && echo "HARNESS: insmod ok" || echo "HARNESS: insmod FAILED"
$rmmod_zeile
/bin/busybox dmesg | /bin/busybox grep -E "gabbro|Oops|BUG:|WARNING:"
echo "HARNESS: end"
/bin/busybox poweroff -f
EOF
    chmod +x "$arb/initrd/init"
    ( cd "$arb/initrd" && find . | cpio -o -H newc 2>/dev/null | gzip -9 > "$arb/initrd.gz" )

    timeout "$FRIST" qemu-system-x86_64 -kernel "$VMLINUZ" -initrd "$arb/initrd.gz" \
        -append "console=ttyS0 quiet panic=1" -nographic -m 512 -no-reboot \
        -smp "$SMP" 2>&1 | tr -d '\r'
}

# -- the verdict over one run --------------------------------------------------
beurteile() {   # $1 = output file, $2 = gift number or "", $3 = probe
    local aus="$1" gift="$2" fehler=0
    probe_waehle "$3"
    local erwartet="$ERWARTET"
    [ "$gift" = 1 ]  && erwartet="$(echo "$erwartet" | sed 's/v=33/v=34/')"
    [ "$gift" = 7 ]  && erwartet="$(echo "$erwartet" | sed 's/landed=0/landed=1/')"
    [ "$gift" = 10 ] && erwartet="$(echo "$erwartet" | sed 's/k=2 v=512/k=2 v=513/')"

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

    # **Did the probe get the chance to measure anything?** For `takt` the answer
    # is a number and not a line: `landed=0` over a run in which the timer never
    # fired says nothing at all (`W1` -- a run that measured nothing is not a run
    # that passed). Gift 6 is exactly this case.
    if [ -n "${TICKS_MIN:-}" ]; then
        local ticks
        ticks="$(sed -n 's/.*gabbro-takt: ticks=\([0-9]*\) .*/\1/p' "$aus" | head -1)"
        if [ -z "$ticks" ]; then
            echo "RED: no tick count in the kernel log -- the run reported no opportunities"
            fehler=$((fehler+1))
        elif [ "$ticks" -lt "$TICKS_MIN" ]; then
            echo "RED: the hardirq timer fired $ticks time(s), fewer than $TICKS_MIN -- a clean landed= over that many opportunities is not a measurement"
            fehler=$((fehler+1))
        fi
    fi

    # **Did the consumer ever see the flag set?** The same question `ticks` asks
    # for `takt`: a run in which it never did reports a clean `k=4 v=0` about a
    # branch it never entered, and that is not a measurement (`W1`).
    if [ -n "${GESEHEN_MIN:-}" ]; then
        local gesehen
        gesehen="$(sed -n 's/.*gabbro-atomar: k=3 v=\([0-9]*\).*/\1/p' "$aus" | head -1)"
        if [ -z "$gesehen" ]; then
            echo 'RED: no k=3 line in the kernel log -- the run reported no flag observations'
            fehler=$((fehler+1))
        elif [ "$gesehen" -lt "$GESEHEN_MIN" ]; then
            echo "RED: the consumer saw the flag set $gesehen time(s), fewer than $GESEHEN_MIN -- a clean payload check over that many observations is not a measurement"
            fehler=$((fehler+1))
        fi
    fi

    # **The two static checks over the built artefact** (K6): the mapping's rows
    # and every access going through them. Their answers travel in the run's own
    # output as `HARNESS:` lines, so this reads them the same way it reads
    # `insmod ok`.
    if [ -n "${ABBILDUNG:-}" ]; then
        grep -q "HARNESS: mapping ok" "$aus" || {
            echo "RED: the atomic mapping did not hold:"
            grep "HARNESS: mapping FAILED" "$aus" | head -4 | sed 's/^/     /'
            fehler=$((fehler+1))
        }
        grep -q "HARNESS: atomic accesses ok" "$aus" || {
            echo "RED: an access to an atomic stands beside the mapping:"
            grep -A3 "HARNESS: atomic accesses FAILED" "$aus" | head -4 | sed 's/^/     /'
            fehler=$((fehler+1))
        }
    fi

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
    echo "== Gabbro units as Linux kernel modules, in QEMU =="
    echo "   kernel      $VMLINUZ ($KERNVERSION headers)"
    gesamt_fehler=0
    for p in $PROBEN; do
        probe_waehle "$p"
        echo
        echo "-- probe $p: $MODUL"
        echo "   source      $QUELLE"
        echo "   own C       $FREMD"
        [ -n "$PARAM" ] && echo "   insmod      $PARAM (the program's ceiling is max 4096 slots)"
        mkdir -p "$ARB/$p"
        lauf_einmal "" "$ARB/$p" "$p" > "$ARB/$p/aus.txt"
        grep -E "HARNESS:|gabbro" "$ARB/$p/aus.txt" | sed 's/^/   /'
        ergebnis="$(beurteile "$ARB/$p/aus.txt" "" "$p")"
        echo "$ergebnis" | grep -v '^FEHLER=' || true
        n="$(echo "$ergebnis" | sed -n 's/^FEHLER=//p')"
        gesamt_fehler=$((gesamt_fehler + n))
    done
    echo
    if [ "$gesamt_fehler" = 0 ]; then
        echo "GREEN: halde  -- loaded, allocated, refused on full, reported, unloaded clean."
        echo "GREEN: takt   -- a masks-irqs lock held across a long section, a hardirq timer"
        echo "                 taking the same lock, and 0 arrivals on a holding core."
        echo "GREEN: atomar -- two DECLARED roots as kthreads, a counter that answers 512"
        echo "                 exactly, a release/acquire flag seen set, a payload never"
        echo "                 stale, two bits ORed to 3; and the mapping's 13 rows expanded"
        echo "                 and held against their kernel primitive."
        exit 0
    fi
    echo "RED: $gesamt_fehler finding(s)."
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
    p="$(gift_probe "$g")"
    lauf_einmal "$g" "$arb" "$p" > "$arb/aus.txt"
    ergebnis="$(beurteile "$arb/aus.txt" "$g" "$p")"
    n="$(echo "$ergebnis" | sed -n 's/^FEHLER=//p')"
    # **A gift that did not APPLY is not a gift that was caught** (server lane,
    # 2026-09-28). A mutation whose target has moved leaves the run with no QEMU
    # boot at all, and every line of the expectation is then missing -- which
    # reads as a fat catch and measures nothing. *Gift 8 did exactly this the
    # first time it ran: 11 findings, and not one of them about the mapping.*
    # The twin trap is already recorded (a gift that does not apply looks like a
    # pass, gift 5, session 4); this is the same fact from the other side.
    if grep -q "does not apply" "$arb/aus.txt"; then
        echo "GIFT $g: DOES NOT APPLY -- the mutation found nothing to change, so nothing was measured"
        grep "does not apply" "$arb/aus.txt" | head -1 | sed 's/^/    /'
    elif [ "$n" = 0 ]; then
        echo "GIFT $g: NOT CAUGHT -- the harness stayed green under the mutation"
    else
        echo "GIFT $g: caught ($n finding(s))"
        # The indented lines belong to the `RED` above them -- a verdict that
        # printed only the headline would hide WHICH row of the mapping moved.
        echo "$ergebnis" | grep -E '^RED|^     ' | head -5 | sed 's/^/    /'
        gefangen=$((gefangen+1))
    fi
done
echo
echo "gifts: $gefangen of $gesamt caught"
[ "$gefangen" = "$gesamt" ]
