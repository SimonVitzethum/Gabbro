#!/usr/bin/env bash
# WITNESS z16-builtin-unreachable -- C2 form `__builtin_unreachable` (5 sites).
#
# An exhaustive `match` over a tagged type hands the after-end decision to the
# C compiler: `#if defined(__GNUC__)` / `__builtin_unreachable();` / `#endif`
# / `return 0;`. The builtin is a promise that control never arrives -- and a
# promise the compiler trusts absolutely: if it IS reached, the program has no
# meaning left, so no safety claim can rest on it.
#
# Gabbro side: construct in beispiele/08-bereiche.gab lines 106-113,
# `match m { Leer => ... Kurz(k) => ... Lang(p) => ... Antwort(f) => ... }`,
# an exhaustive match whose emission ends in the unreachable epilogue.
# Emitter: exhaustive-match epilogue (the adjacent-return rule deletes four
# of the five sites; one stays load-bearing at -O0 only).
# Expected C (emitted shape):
#   #if defined(__GNUC__)
#       __builtin_unreachable();
#   #endif
#       return 0;
# Behaviour: the two covered arms return their mapped values and the
# epilogue shape compiles; results must agree at -O0/-O2/-Os. The
# unreachable itself is never executed -- executing it would void the test.
# Atomic safety: NO -- reaching it is undefined behaviour; a safety claim
# needs defined behaviour to stand on.
#
# Run: ./z16-builtin-unreachable.sh
#      GABBRO_BIN=/path/to/gabbro ./z16-builtin-unreachable.sh   (also re-emits 08-bereiche.gab, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z16-builtin-unreachable] loudly.
set -u
FORM="z16-builtin-unreachable"
TOKEN="__builtin_unreachable"
EXPECTED="unreachable 0 1"
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
    say "EMIT[$FORM]: SKIP -- needs GABBRO_BIN=path/to/gabbro and $SRC; authoring-time result: emits [__builtin_unreachable();] under [defined(__GNUC__)], 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdint.h>
#include <stdio.h>
static uint32_t narrow2(uint32_t raw) {
    switch (raw) {
        case 0: return 0;
        case 1: return 1;
        default: break;
    }
#if defined(__GNUC__)
    __builtin_unreachable();
#endif
    return 0;
}
int main(void) { printf("unreachable %u %u\n", narrow2(0), narrow2(1)); return 0; }
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

say "ATOMIC-SAFE[$FORM]: NO -- if reached, behaviour is undefined; no safety claim survives UB."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: builtin-unreachable behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
