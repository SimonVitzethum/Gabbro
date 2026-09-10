#!/usr/bin/env bash
# WITNESS z05-star -- C2 form `*` dereference (141 census sites).
#
# Every MMIO register read is a dereference through a volatile cast:
# `(*(volatile uint32_t *)(d->basis + 28))`. A plain dereference is one load;
# under concurrent access it can tear -- atomicity needs `_Atomic`, and a `*`
# alone never gives it.
#
# Gabbro side: construct in beispiele/09-ohne-zeiger.gab, register read inside
# `transition wurzel_setzen` (line ~109), emitted as
# `uint32_t _s = (*(volatile uint32_t *)(d->basis + 28));`.
# Emitter: device-register read lowering.
# Expected C (emitted shape):
#   uint32_t _s = (*(volatile uint32_t *)(d->basis + 28));
# Behaviour: write through a pointer, read back through a dereference; the
# value must survive -O0/-O2/-Os unchanged.
# Atomic safety: NO -- a plain `*` load/store may tear under concurrent
# access; only _Atomic (or a lock) makes it indivisible.
#
# Run: ./z05-star.sh
#      GABBRO_BIN=/path/to/gabbro ./z05-star.sh   (also re-emits 09-ohne-zeiger.gab, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z05-star] loudly.
set -u
FORM="z05-star"
TOKEN="*(volatile"
EXPECTED="star 42"
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
    say "EMIT[$FORM]: SKIP -- needs GABBRO_BIN=path/to/gabbro and $SRC; authoring-time result: emits [(*(volatile uint32_t *)(d->basis + 28))], 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdint.h>
#include <stdio.h>
int main(void) {
    uint64_t cell = 0;
    uint64_t *p = &cell;
    *p = 6u * 7u;
    printf("star %llu\n", (unsigned long long)*p);
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

say "ATOMIC-SAFE[$FORM]: NO -- dereference is a plain load/store; concurrent access may tear it."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: star behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
