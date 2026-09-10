#!/usr/bin/env bash
# WITNESS z17-ifdef-gnuc -- C2 form `#if defined(__GNUC__)` (5 sites).
#
# Every `__builtin_unreachable()` stands behind `#if defined(__GNUC__)`: the
# emitter refuses to speak GNU to a non-GNU compiler. The guard is
# preprocessor -- it selects code at compile time and emits no instruction.
# Note the census subtlety: the five `#if` in the corpus are all this guard,
# so the permitted `#if`-out-of-`when` form is never emitted and the emitted
# form was never permitted.
#
# Gabbro side: same construct as z16, beispiele/08-bereiche.gab lines
# 106-113 (exhaustive match epilogue).
# Emitter: guarded-unreachable epilogue.
# Expected C (emitted shape):
#   #if defined(__GNUC__)
#       __builtin_unreachable();
#   #endif
# Behaviour: print which preprocessor branch the toolchain took. Under cc
# (GCC) the GNUC branch must win at every opt level; on a non-GNU compiler
# this witness FAILS loudly -- that is the pinned assumption speaking, and
# it must be loud, not silent.
# Atomic safety: YES -- preprocessor selection; no run-time step exists.
#
# Run: ./z17-ifdef-gnuc.sh
#      GABBRO_BIN=/path/to/gabbro ./z17-ifdef-gnuc.sh   (also re-emits 08-bereiche.gab, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z17-ifdef-gnuc] loudly.
set -u
FORM="z17-ifdef-gnuc"
TOKEN="defined(__GNUC__)"
EXPECTED="gnuc 1"
STD="c11"
SRC="../../beispiele/08-bereiche.gab"
FAILS=0
D="$(cd "$(dirname "$0")" && pwd)"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
say() { printf '%s\n' "$*"; }
fail() { say "FAIL[$FORM]: $*"; FAILS=$((FAILS + 1)); }

if [ -n "${GABBRO_BIN:-}" ] && [ -x "${GABBRO_BIN:-}" ] && [ -f "$D/$SRC" ]; then
    if "${GABBRO_BIN}" emit "$D/$SRC" > "$T/e.c" 2> "$T/emit.log"; then
        if grep -qF "$TOKEN" "$T/e.c"; then
            say "EMIT[$FORM]: PASS -- 08-bereiche.gab emits [$TOKEN]"
        else
            fail "emission of $SRC lacks [$TOKEN]"
        fi
    else
        fail "gabbro emit refused $SRC:"; cat "$T/emit.log"
    fi
else
    say "EMIT[$FORM]: SKIP -- needs GABBRO_BIN=path/to/gabbro and $SRC; authoring-time result: emits [#if defined(__GNUC__)], 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdio.h>
int main(void) {
#if defined(__GNUC__)
    printf("gnuc %d\n", 1);
#else
    printf("gnuc %d\n", 0);
#endif
    return 0;
}
C_EOF
REF=""
for OPT in O0 O2 Os; do
    if ! cc -std=${STD} -Wall -Wextra "-$OPT" -o "$T/w-$OPT" "$T/w.c" 2> "$T/cc-$OPT.log"; then
        fail "cc -$OPT refused the program:"; cat "$T/cc-$OPT.log"; continue
    fi
    OUT="$("$T/w-$OPT")"; CODE=$?
    [ $CODE -eq 0 ] || fail "cc -$OPT exit code $CODE, want 0"
    [ "$OUT" = "$EXPECTED" ] || fail "cc -$OPT output [$OUT], want [$EXPECTED] (non-GNU toolchain?)"
    if [ -z "$REF" ]; then REF="$OUT"; elif [ "$OUT" != "$REF" ]; then fail "-$OPT output [$OUT] disagrees with -O0 [$REF]"; fi
done

say "ATOMIC-SAFE[$FORM]: YES -- decided before compilation; nothing executes."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: ifdef-gnuc behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
