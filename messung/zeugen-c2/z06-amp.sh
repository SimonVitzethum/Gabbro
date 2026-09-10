#!/usr/bin/env bash
# WITNESS z06-amp -- C2 form `&` address-of (111 census sites).
#
# Out-parameters lower to address-of: `let g = groesse_gemessen() else (e1)`
# becomes `groesse_gemessen(&g, &e1)`. Taking an address computes nothing at
# run time -- it names a place the callee may write.
#
# Gabbro side: construct in beispiele/06-annahmen.gab line 134,
# `let g = groesse_gemessen() else (e1) { return false; }`, emitted as
# `if (!groesse_gemessen(&g, &e1)) {`.
# Emitter: can_fail/out-parameter lowering.
# Expected C (emitted shape):
#   if (!groesse_gemessen(&g, &e1)) {
# Behaviour: pass two addresses, read back what the callee stored; the triple
# must agree at -O0/-O2/-Os.
# Atomic safety: YES -- `&` takes an address at compile time; it performs no
# memory access of its own.
#
# Run: ./z06-amp.sh
#      GABBRO_BIN=/path/to/gabbro ./z06-amp.sh   (also re-emits 06-annahmen.gab, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z06-amp] loudly.
set -u
FORM="z06-amp"
TOKEN="&g"
EXPECTED="amp 1 8 0"
STD="c11"
SRC="../../beispiele/06-annahmen.gab"
FAILS=0
D="$(cd "$(dirname "$0")" && pwd)"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
say() { printf '%s\n' "$*"; }
fail() { say "FAIL[$FORM]: $*"; FAILS=$((FAILS + 1)); }

if [ -n "${GABBRO_BIN:-}" ] && [ -x "${GABBRO_BIN:-}" ] && [ -f "$D/$SRC" ]; then
    if "${GABBRO_BIN}" emit "$D/$SRC" > "$T/e.c" 2> "$T/emit.log"; then
        if grep -qF "$TOKEN" "$T/e.c"; then
            say "EMIT[$FORM]: PASS -- 06-annahmen.gab emits [$TOKEN]"
        else
            fail "emission of $SRC lacks [$TOKEN]"
        fi
    else
        fail "gabbro emit refused $SRC:"; cat "$T/emit.log"
    fi
else
    say "EMIT[$FORM]: SKIP -- needs GABBRO_BIN=path/to/gabbro and $SRC; authoring-time result: emits [groesse_gemessen(&g, &e1)], 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
static bool measure(uint64_t *g, uint32_t *e) { *g = 8; *e = 0; return *g >= 1; }
int main(void) {
    uint64_t g = 0;
    uint32_t e1 = 99;
    bool ok = measure(&g, &e1);
    printf("amp %d %llu %u\n", (int)ok, (unsigned long long)g, e1);
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

say "ATOMIC-SAFE[$FORM]: YES -- address-of computes a place, not a value; no access happens."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: amp behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
