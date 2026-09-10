#!/usr/bin/env bash
# WITNESS z07-tilde -- C2 form `~` bitwise complement (98 census sites).
#
# Device bit-moves lower to clear-then-set: `(_s & ~mask) | mask`. `~` is a
# pure function of its operand -- but the idiom it serves is read-modify-write
# on a register, and that sequence is not one step.
#
# Gabbro side: construct in beispiele/09-ohne-zeiger.gab, `transition
# wurzel_setzen { GCMD.SRTP: 0 -> 1 }` (line ~109), emitted as
# `(_s & (uint32_t)~(uint32_t)1073741824u) | (uint32_t)1073741824u`.
# Emitter: transition bit-move lowering.
# Expected C (emitted shape):
#   (*(volatile uint32_t *)(d->basis + 24)) = (uint32_t)((_s & (uint32_t)~(uint32_t)1073741824u) | (uint32_t)1073741824u);
# Behaviour: the clear-then-set idiom over a fixed word plus `~0u`; both
# values must agree at -O0/-O2/-Os. Expected values computed independently
# with python3 (2026-09-10): 1379161720 and 4294967295.
# Atomic safety: NO -- `~` itself is pure, but its emitted use is
# read-modify-write on shared state, which is not atomic.
#
# Run: ./z07-tilde.sh
#      GABBRO_BIN=/path/to/gabbro ./z07-tilde.sh   (also re-emits 09-ohne-zeiger.gab, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z07-tilde] loudly.
set -u
FORM="z07-tilde"
TOKEN="~"
EXPECTED="tilde 1379161720 4294967295"
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
    say "EMIT[$FORM]: SKIP -- needs GABBRO_BIN=path/to/gabbro and $SRC; authoring-time result: emits [(uint32_t)~(uint32_t)1073741824u], 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdint.h>
#include <stdio.h>
int main(void) {
    uint32_t s = 0x12345678u;
    uint32_t out = (uint32_t)((s & (uint32_t)~(uint32_t)1073741824u) | (uint32_t)1073741824u);
    printf("tilde %u %u\n", out, (uint32_t)~(uint32_t)0u);
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

say "ATOMIC-SAFE[$FORM]: NO -- pure as a value, but emitted as read-modify-write on shared registers."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: tilde behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
