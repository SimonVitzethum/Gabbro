#!/usr/bin/env bash
# WITNESS z08-break -- C2 form `break` (51 census sites, still open at ruling time).
#
# `break` has four emission lines: the retry watchdog (emit.rs:7367), the
# descendants-walk exit (8537), and two switch-case terminators (8909, 8971).
# The switch pair is the bulk: every `match` arm ends `} break;`, which is why
# this witness pins the match shape, not the loop shape.
#
# Gabbro side: construct in beispiele/01-tabelle.gab lines 170-175,
# `match o.slots[obj].art { Speicher(p) => ... Endpunkt(e) => ... }`, emitted as
# `case ObjektArt_Speicher: { ... } break;` per arm.
# Emitter: match/switch lowering (emit.rs ~8909, 8971); walk exit at 8537.
# Expected C (emitted shape):
#   case ObjektArt_Speicher: {
#       uint64_t p = o->slots[obj].art.last.Speicher;
#       speicher_freigeben(p);
#   } break;
# Behaviour: a counted loop exited by break plus a switch with a break per
# arm; both results must agree at -O0/-O2/-Os.
# Atomic safety: YES -- break transfers control inside one thread; it touches
# no shared state and admits no interleaving of its own.
#
# Run: ./z08-break.sh
#      GABBRO_BIN=/path/to/gabbro ./z08-break.sh   (also re-emits 01-tabelle.gab, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z08-break] loudly.
set -u
FORM="z08-break"
TOKEN="} break;"
EXPECTED="break 7 30"
STD="c11"
SRC="../../beispiele/01-tabelle.gab"
FAILS=0
D="$(cd "$(dirname "$0")" && pwd)"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
say() { printf '%s\n' "$*"; }
fail() { say "FAIL[$FORM]: $*"; FAILS=$((FAILS + 1)); }

if [ -n "${GABBRO_BIN:-}" ] && [ -x "${GABBRO_BIN:-}" ] && [ -f "$D/$SRC" ]; then
    if "${GABBRO_BIN}" emit "$D/$SRC" > "$T/e.c" 2> "$T/emit.log"; then
        if grep -qF "$TOKEN" "$T/e.c"; then
            say "EMIT[$FORM]: PASS -- 01-tabelle.gab emits [$TOKEN]"
        else
            fail "emission of $SRC lacks [$TOKEN]"
        fi
    else
        fail "gabbro emit refused $SRC:"; cat "$T/emit.log"
    fi
else
    say "EMIT[$FORM]: SKIP -- needs GABBRO_BIN=path/to/gabbro and $SRC; authoring-time result: emits [} break;] per match arm, 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdint.h>
#include <stdio.h>
int main(void) {
    uint32_t n = 0;
    for (;;) { if (n >= 7) break; n++; }
    uint32_t tag = 2, val = 0;
    switch (tag) {
        case 0: { val = 10; } break;
        case 1: { val = 20; } break;
        case 2: { val = 30; } break;
        default: { val = 99; } break;
    }
    printf("break %u %u\n", n, val);
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

say "ATOMIC-SAFE[$FORM]: YES -- intra-thread control transfer; no shared-state step."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: break behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
