#!/usr/bin/env bash
# WITNESS z19-static-assert -- C2 form `_Static_assert` (1 census site).
#
# The single site guards an `entrust` handover: the space handed to the guest
# must be a declared, complete type. A static assertion is the cheapest
# possible check -- it runs at compile time, emits no instruction, and fails
# the build instead of the program.
#
# Gabbro side: construct in beispiele/25-entrust.gab line 32,
# `entrust jitpuffer at Gastbild arch x86_64 { ... }`, emitted as
# `_Static_assert(sizeof(Gastbild) > 0, "the space an entrust hands over must
# be a declared, complete type");` ahead of the handover prototype.
# Emitter: entrust-handover lowering.
# Expected C (emitted shape):
#   _Static_assert(sizeof(Gastbild) > 0,
#       "the space an `entrust` hands over must be a declared, complete type");
# Behaviour: two static assertions (completeness, width) plus a sizeof print;
# the assertions enforce themselves -- a violation fails compilation, which
# this script reports as FAIL, not as silence. Values must agree at
# -O0/-O2/-Os.
# Atomic safety: YES -- compile-time only; nothing executes.
#
# Run: ./z19-static-assert.sh
#      GABBRO_BIN=/path/to/gabbro ./z19-static-assert.sh   (also re-emits 25-entrust.gab, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z19-static-assert] loudly.
set -u
FORM="z19-static-assert"
TOKEN="_Static_assert"
EXPECTED="static-assert 8"
STD="c11"
SRC="../../beispiele/25-entrust.gab"
FAILS=0
D="$(cd "$(dirname "$0")" && pwd)"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
say() { printf '%s\n' "$*"; }
fail() { say "FAIL[$FORM]: $*"; FAILS=$((FAILS + 1)); }

if [ -n "${GABBRO_BIN:-}" ] && [ -x "${GABBRO_BIN:-}" ] && [ -f "$D/$SRC" ]; then
    if "${GABBRO_BIN}" emit "$D/$SRC" > "$T/e.c" 2> "$T/emit.log"; then
        if grep -qF "$TOKEN" "$T/e.c"; then
            say "EMIT[$FORM]: PASS -- 25-entrust.gab emits [$TOKEN]"
        else
            fail "emission of $SRC lacks [$TOKEN]"
        fi
    else
        fail "gabbro emit refused $SRC:"; cat "$T/emit.log"
    fi
else
    say "EMIT[$FORM]: SKIP -- needs GABBRO_BIN=path/to/gabbro and $SRC; authoring-time result: emits [_Static_assert(sizeof(Gastbild) > 0, ...)], 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdint.h>
#include <stdio.h>
typedef struct { uint64_t kopf; } Slot;
_Static_assert(sizeof(Slot) > 0, "a handed-over space must be a declared, complete type");
_Static_assert(sizeof(uint64_t) == 8, "u64 is eight octets on this target");
int main(void) { printf("static-assert %u\n", (unsigned)sizeof(Slot)); return 0; }
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

say "ATOMIC-SAFE[$FORM]: YES -- compile-time only; nothing executes."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: static-assert behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
