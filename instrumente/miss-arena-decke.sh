#!/usr/bin/env bash
# **Does the ceiling cost anything? (`AUFTRAG-1` H4, TODO section 0e)**
#
# A dynamic arena declares `max M` -- address reserved, storage not touched. The
# promise of that shape is that `M` is a NUMBER and not a SIZE: nothing in the
# translation, in the emitted C or in the linked binary may grow with it. No
# static array of `M` slots, no `memset` of the reservation, no per-element
# unrolling.
#
# This instrument measures the promise on two twins that differ in `M` alone
# (`messung/proben/arena-h4/ceiling-10mib.gab` = 1 310 720 slots of `u64`,
# `ceiling-32gib.gab` = 4 294 967 295 slots -- the largest `M` the `uint32_t`
# slot counters admit). For each it reports:
#
#   * translation time (best of N runs of `gabbro emit`, wall clock),
#   * the emitted C in bytes and in lines,
#   * the linked binary in bytes, and its `.bss` + `.data` in bytes.
#
# A PASS needs all four to agree within the stated tolerance, and the two
# emitted C files to differ only in the ceiling literals and the module name.
#
# The planted defect: `--gift` emits the small twin but links it against a
# driver that declares a real `uint64_t buf[M]` for the SMALL ceiling. If the
# measurement can be fooled by a static array, the gift run must still turn the
# instrument red -- that is what makes the green run a measurement.
#
# Usage: instrumente/miss-arena-decke.sh [--gift] [--runs N]
set -u

W="$(cd "$(dirname "$0")/.." && pwd)"
GIFT=0
RUNS=5
while [ $# -gt 0 ]; do
    case "$1" in
        --gift) GIFT=1 ;;
        --runs) shift; RUNS="$1" ;;
        *) echo "miss-arena-decke.sh: unknown argument '$1'" >&2; exit 2 ;;
    esac
    shift
done

# **Which binary, and is it newer than the sources?** One register, one file
# (`instrumente/binaer.sh`). This instrument was the third one the trap bit on
# 2026-09-28: it measured the emitted C of an emitter that no longer existed and
# printed GREEN over the wrong bytes.
. "$(dirname "$0")/binaer.sh"
if ! GABBRO="$(gabbro_binaer "$W")"; then
    echo "ABORT: $GABBRO" >&2
    echo "       (an instrument that measures nothing must say so, not print zeroes)" >&2
    exit 2
fi

ARB="$(mktemp -d)"
trap 'rm -rf "$ARB"' EXIT

KLEIN="$W/messung/proben/arena-h4/ceiling-10mib.gab"
GROSS="$W/messung/proben/arena-h4/ceiling-32gib.gab"
for f in "$KLEIN" "$GROSS"; do
    [ -f "$f" ] || { echo "ABORT: missing twin $f" >&2; exit 2; }
done

CC="${CC:-cc}"

# The driver: reserve at load, run the body once, print. Identical for both
# twins -- the only text that differs between the two builds is the emitted C.
treiber() {
    cat <<EOF
#include <stdio.h>
#include "$1"
#include "arena_laufzeit.c"
#include "linux_bind.c"
$2
int main(void) {
    gabbro_arena_reserve(&Puffer_desc);
    printf("%llu\n", (unsigned long long)fuellen());
    return 0;
}
EOF
}

# **The runtime and the PROGRAM's binding beside it** (server lane, 2026-09-28, K8).
# Since `laufzeit/arena_dyn.c` calls no operating-system function of its own, the six
# names it does call are declarations (`laufzeit/bindung.h`) that the program defines --
# `bibliothek/linux/linux.c` is the usual POSIX set, and this harness takes it off the
# shelf exactly as a program would. *The measured claim of this instrument does not move
# for it:* what is timed and sized is the EMITTED C and the binary, and the binding is the
# same file in both twins.
# **Since 2026-09-30 (C-free lane) neither is a handwritten file**: the runtime is the text
# the hosted driver writes (`gabbro runtime arena`, template `arena.dyn`) and the binding's
# storage and report calls are Gabbro (`bibliothek/linux/linux.gab`), emitted beside it.
"$GABBRO" runtime arena > "$ARB/arena_laufzeit.c" || exit 2
"$GABBRO" emit "$W/bibliothek/linux/linux.gab" > "$ARB/linux_bind.c" || exit 2

# -- one twin: emit, time, compile, measure -----------------------------------
mess() {   # $1 = tag, $2 = source, $3 = extra driver text
    local tag="$1" quelle="$2" extra="$3"
    local c="$ARB/$tag.c" drv="$ARB/$tag-treiber.c" bin="$ARB/$tag.bin"
    local best="" t0 t1 d i

    for i in $(seq 1 "$RUNS"); do
        t0=$(date +%s%N)
        "$GABBRO" emit "$quelle" > "$c" 2>"$ARB/$tag.err" || {
            echo "ABORT: gabbro emit failed on $quelle" >&2
            cat "$ARB/$tag.err" >&2
            exit 2
        }
        t1=$(date +%s%N)
        d=$(( (t1 - t0) / 1000000 ))
        if [ -z "$best" ] || [ "$d" -lt "$best" ]; then best="$d"; fi
    done

    treiber "$tag.c" "$extra" > "$drv"
    ( cd "$ARB" && "$CC" -O2 -std=c11 -o "$bin" "$drv" ) 2>"$ARB/$tag.cc.err" || {
        echo "ABORT: cc failed on $tag" >&2
        cat "$ARB/$tag.cc.err" >&2
        exit 2
    }

    local cbytes clines binbytes bss data out
    cbytes=$(wc -c < "$c" | tr -d ' ')
    clines=$(wc -l < "$c" | tr -d ' ')
    binbytes=$(wc -c < "$bin" | tr -d ' ')
    bss=$(size -A "$bin" 2>/dev/null | awk '$1==".bss"{print $2}')
    data=$(size -A "$bin" 2>/dev/null | awk '$1==".data"{print $2}')
    [ -n "$bss" ] || bss=0
    [ -n "$data" ] || data=0
    out=$("$bin")

    echo "$best $cbytes $clines $binbytes $bss $data $out"
}

EXTRA_KLEIN=""
EXTRA_GROSS=""
if [ "$GIFT" = 1 ]; then
    # **The planted defect.** The SMALL twin drags a static array of its own
    # ceiling into the binary -- exactly the shape "the ceiling costs nothing"
    # forbids. A measurement that cannot see it is not a measurement.
    EXTRA_KLEIN='static volatile unsigned long long gift_statisch[1310720];
unsigned long long gift_lesen(void) { return gift_statisch[0]; }'
fi

read -r KT KC KL KB KBSS KD KOUT <<<"$(mess klein "$KLEIN" "$EXTRA_KLEIN")"
read -r GT GC GL GB GBSS GD GOUT <<<"$(mess gross "$GROSS" "$EXTRA_GROSS")"

echo "== the ceiling against the cost (H4) =="
echo "                        max 1310720 (10 MiB)   max 4294967295 (32 GiB)"
printf "translate (ms, best of %-2s)  %14s %25s\n" "$RUNS" "$KT" "$GT"
printf "emitted C (bytes)         %14s %25s\n" "$KC" "$GC"
printf "emitted C (lines)         %14s %25s\n" "$KL" "$GL"
printf "binary (bytes)            %14s %25s\n" "$KB" "$GB"
printf "binary .bss (bytes)       %14s %25s\n" "$KBSS" "$GBSS"
printf "binary .data (bytes)      %14s %25s\n" "$KD" "$GD"
printf "run answer                %14s %25s\n" "$KOUT" "$GOUT"

# -- the verdict ---------------------------------------------------------------
#
# Tolerances, and why each is what it is:
#   * emitted C: the two files differ in the ceiling LITERAL (7 digits vs 10)
#     and in the module name, so a handful of bytes is expected and 64 is
#     generous; the LINE count must be identical -- a per-element unrolling
#     would move it by millions.
#   * binary: same code, same data; 512 bytes covers the literal and the
#     section padding. `.bss` and `.data` must be EQUAL to the byte: a static
#     array of `M` slots lands in exactly those two.
#   * translation time: a per-element loop over `M` would be seconds, not
#     milliseconds; 250 ms of slack is far below that and far above jitter.
FEHLER=0
melde() { echo "RED: $1"; FEHLER=$((FEHLER + 1)); }

d() { local a=$1 b=$2; if [ "$a" -gt "$b" ]; then echo $((a - b)); else echo $((b - a)); fi; }

[ "$(d "$KC" "$GC")" -le 64 ]   || melde "emitted C differs by $(d "$KC" "$GC") bytes (> 64)"
[ "$KL" = "$GL" ]               || melde "emitted C line counts differ ($KL vs $GL)"
[ "$(d "$KB" "$GB")" -le 512 ]  || melde "binary differs by $(d "$KB" "$GB") bytes (> 512)"
[ "$KBSS" = "$GBSS" ]           || melde ".bss differs ($KBSS vs $GBSS) -- storage grew with the ceiling"
[ "$KD" = "$GD" ]               || melde ".data differs ($KD vs $GD) -- storage grew with the ceiling"
[ "$(d "$KT" "$GT")" -le 250 ]  || melde "translation time differs by $(d "$KT" "$GT") ms (> 250)"
[ "$KOUT" = "$GOUT" ]           || melde "the two twins answer differently ($KOUT vs $GOUT)"
[ "$KOUT" = "33" ]              || melde "the answer is $KOUT, not 33 (10 + 11 + 12)"

echo
if [ "$FEHLER" = 0 ]; then
    if [ "$GIFT" = 1 ]; then
        echo "GIFT NOT CAUGHT -- the instrument stayed green with a static array of the"
        echo "ceiling linked in. It measures nothing; repair it before believing a green run."
        exit 1
    fi
    echo "GREEN: the ceiling costs nothing -- $RUNS runs each, numbers above."
    exit 0
else
    if [ "$GIFT" = 1 ]; then
        echo "GIFT CAUGHT ($FEHLER finding(s)) -- the instrument sees a ceiling that costs."
        exit 0
    fi
    echo "RED: $FEHLER finding(s)."
    exit 1
fi
