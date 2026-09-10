#!/usr/bin/env bash
# WITNESS z10-sizeof -- C2 form `sizeof` (27 census sites).
#
# Table traversals bound themselves by declaration, not by magic number:
# `sizeof(q->slots) / sizeof(q->slots[0])`. The bound falls out of the type,
# so growing the table cannot desynchronise the loop.
#
# Gabbro side: construct in beispiele/04-schleifen.gab, `faellige_wecken`
# (`traverse eintrag over slots of q by unvisited`, line 33), emitted as
# `for (uint32_t eintrag = 0; eintrag < (uint32_t)(sizeof(q->slots) / sizeof(q->slots[0])); eintrag++)`.
# Emitter: traverse-over-slots bound lowering.
# Expected C (emitted shape):
#   for (uint32_t eintrag = 0; eintrag < (uint32_t)(sizeof(q->slots) / sizeof(q->slots[0])); eintrag++) {
# Behaviour: element count by sizeof quotient plus a sizeof-driven fill loop;
# count, visits and element size must agree at -O0/-O2/-Os.
# Atomic safety: YES -- sizeof is a compile-time constant; its operand is not
# evaluated and no step happens at run time.
#
# Run: ./z10-sizeof.sh
#      GABBRO_BIN=/path/to/gabbro ./z10-sizeof.sh   (also re-emits 04-schleifen.gab, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z10-sizeof] loudly.
set -u
FORM="z10-sizeof"
TOKEN="sizeof("
EXPECTED="sizeof 8 8 8"
STD="c11"
SRC="../../beispiele/04-schleifen.gab"
FAILS=0
D="$(cd "$(dirname "$0")" && pwd)"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
say() { printf '%s\n' "$*"; }
fail() { say "FAIL[$FORM]: $*"; FAILS=$((FAILS + 1)); }

if [ -n "${GABBRO_BIN:-}" ] && [ -x "${GABBRO_BIN:-}" ] && [ -f "$D/$SRC" ]; then
    if "${GABBRO_BIN}" emit "$D/$SRC" > "$T/e.c" 2> "$T/emit.log"; then
        if grep -qF "$TOKEN" "$T/e.c"; then
            say "EMIT[$FORM]: PASS -- 04-schleifen.gab emits [$TOKEN]"
        else
            fail "emission of $SRC lacks [$TOKEN]"
        fi
    else
        fail "gabbro emit refused $SRC:"; cat "$T/emit.log"
    fi
else
    say "EMIT[$FORM]: SKIP -- needs GABBRO_BIN=path/to/gabbro and $SRC; authoring-time result: emits [sizeof(q->slots) / sizeof(q->slots[0])], 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdint.h>
#include <stdio.h>
typedef struct { uint64_t kopf; } Slot;
int main(void) {
    Slot slots[8];
    uint32_t n = (uint32_t)(sizeof(slots) / sizeof(slots[0]));
    uint32_t seen = 0;
    for (uint32_t e = 0; e < (uint32_t)(sizeof(slots) / sizeof(slots[0])); e++) { slots[e].kopf = e; seen++; }
    printf("sizeof %u %u %u\n", n, seen, (unsigned)sizeof(Slot));
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

say "ATOMIC-SAFE[$FORM]: YES -- compile-time constant; no evaluation, no access, no step."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: sizeof behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
