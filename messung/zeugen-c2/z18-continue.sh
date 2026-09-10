#!/usr/bin/env bash
# WITNESS z18-continue -- C2 form `continue` (3 census sites).
#
# Ruled in messung/CFORM-REGEL-CONTINUE.md (admit with price): exactly one
# emitter line writes it (emit.rs:8536), inside the descendants post-order
# walk skeleton. User code cannot emit it -- Gabbro `leave`/`next` lower to
# `goto`, never to break/continue -- so every `continue` in emitted C is the
# skeleton's own, and the wrong-loop error class cannot pass through it.
#
# Gabbro side: construct in beispiele/01-tabelle.gab line 136,
# `traverse opfer over descendants of c.slots[s] by consuming`, emitted as
# `if (!_h1 && ...) { ...; continue; }` inside `for (;;)`.
# Emitter: descendants-walk skeleton (emit.rs:8536; sibling `break` at 8537).
# Expected C (emitted shape):
#   for (;;) {
#       if (!_h1 && c->slots[_k1].erstes_kind != 4096u) { _k1 = c->slots[_k1].erstes_kind; _h1 = false; continue; }
#       if (_k1 == _r1) break;
# Behaviour: skip negatives with continue, sum the rest; the sum must agree
# at -O0/-O2/-Os (the ruling measured the nested form folds to the same
# instructions at -O2/-Os and costs 2 at -O0).
# Atomic safety: YES -- like break: intra-thread control transfer, no
# shared-state step.
#
# Run: ./z18-continue.sh
#      GABBRO_BIN=/path/to/gabbro ./z18-continue.sh   (also re-emits 01-tabelle.gab, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z18-continue] loudly.
set -u
FORM="z18-continue"
TOKEN="continue;"
EXPECTED="continue 14"
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
    say "EMIT[$FORM]: SKIP -- needs GABBRO_BIN=path/to/gabbro and $SRC; authoring-time result: emits [...; continue;] from the walk skeleton, 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdint.h>
#include <stdio.h>
int main(void) {
    int32_t a[] = {3, -1, 4, -1, 5, -9, 2};
    int32_t s = 0;
    uint32_t n = (uint32_t)(sizeof(a) / sizeof(a[0]));
    for (uint32_t i = 0; i < n; i++) { if (a[i] < 0) continue; s += a[i]; }
    printf("continue %d\n", (int)s);
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
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: continue behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
