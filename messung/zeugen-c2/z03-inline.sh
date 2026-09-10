#!/usr/bin/env bash
# WITNESS z03-inline -- C2 form `inline` (440 census sites).
#
# Every device-register accessor and every format validity function is
# `static inline`: the emitter wants header-shape code without paying a call.
# `inline` promises nothing about atomicity -- it is a code-shape hint, and a
# reader who takes it for "runs as one step" is misreading C.
#
# Gabbro side: construct in beispiele/09-ohne-zeiger.gab, `transition
# wurzel_setzen { GCMD.SRTP: 0 -> 1 }` (line ~109), emitted as
# `static inline __attribute__((unused)) void Vtd_wurzel_setzen(Vtd *d)`.
# Emitter: transition/register lowering (emit.rs ~lines 3719-3846, 4133).
# Expected C (emitted shape):
#   static inline __attribute__((unused)) void Vtd_wurzel_setzen(Vtd *d) {
#       uint32_t _s = (*(volatile uint32_t *)(d->basis + 28));
#       ...
#   }
# Behaviour: a static inline accumulator called 100 times; the sum must be
# identical at -O0/-O2/-Os (inlining decisions must not move the value).
# Atomic safety: NO -- inline is a hint about calls, not a claim about steps;
# the call is still a call and no atomicity is promised.
#
# Run: ./z03-inline.sh
#      GABBRO_BIN=/path/to/gabbro ./z03-inline.sh   (also re-emits 09-ohne-zeiger.gab, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z03-inline] loudly.
set -u
FORM="z03-inline"
TOKEN="static inline"
EXPECTED="inline 5050"
STD="c11"
SRC="../../beispiele/09-ohne-zeiger.gab"
FAILS=0
D="$(cd "$(dirname "$0")" && pwd)"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
say() { printf '%s\n' "$*"; }
fail() { say "FAIL[$FORM]: $*"; FAILS=$((FAILS + 1)); }

if [ -n "${GABBRO_BIN:-}" ] && [ -x "${GABBRO_BIN:-}" ] && [ -f "$D/$SRC" ]; then
    if "${GABBRO_BIN}" emit "$D/$SRC" > "$T/e.c" 2> "$T/emit.log"; then
        if grep -qF "$TOKEN" "$T/e.c"; then
            say "EMIT[$FORM]: PASS -- 09-ohne-zeiger.gab emits [$TOKEN]"
        else
            fail "emission of $SRC lacks [$TOKEN]"
        fi
    else
        fail "gabbro emit refused $SRC:"; cat "$T/emit.log"
    fi
else
    say "EMIT[$FORM]: SKIP -- needs GABBRO_BIN=path/to/gabbro and $SRC; authoring-time result: emits [static inline __attribute__((unused)) void Vtd_wurzel_setzen], 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdint.h>
#include <stdio.h>
static inline __attribute__((unused)) uint64_t add_u64(uint64_t a, uint64_t b) { return a + b; }
int main(void) {
    uint64_t s = 0;
    for (uint64_t i = 1; i <= 100; i++) s = add_u64(s, i);
    printf("inline %llu\n", (unsigned long long)s);
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
    [ "$OUT" = "$EXPECTED" ] || fail "cc -$OPT output [$OUT], want [$EXPECTED]"
    if [ -z "$REF" ]; then REF="$OUT"; elif [ "$OUT" != "$REF" ]; then fail "-$OPT output [$OUT] disagrees with -O0 [$REF]"; fi
done

say "ATOMIC-SAFE[$FORM]: NO -- inline hints at call shape; it promises no single step, no indivisibility."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: inline behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
