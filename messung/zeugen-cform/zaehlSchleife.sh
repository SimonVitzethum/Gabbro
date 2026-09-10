#!/usr/bin/env bash
# zaehlSchleife — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:236: "counting loop over a bounded
# range").
#
# Gabbro fragment class: `traverse` over the slots of a table, e.g.
#   traverse eintrag over slots of h by unvisited
#       touches writes h.slots
#   {
#       h.slots[eintrag].benutzt = true;
#   }
# (emitter site emit.rs:8635, second shape at emit.rs:8715). Measured
# 2026-09-10 with `gabbro emit`: the fragment lowers to
#   for (uint32_t eintrag = 0; eintrag < (uint32_t)(sizeof(h->slots) / sizeof(h->slots[0])); eintrag++) {
#       h->slots[eintrag].benutzt = true;
#   }
# The bound is the declared array length, not a computed quantity, so the
# loop visits exactly the bounded range and nothing else.
# Expected C (the form under test): the counting `for` below, in the
# emitter's spelling with the `sizeof`-derived bound.
# Expected behaviour: stdout holds `28` at every optimisation level —
# the loop visits indices 0..7 exactly once each (0+1+...+7 = 28).
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="zaehlSchleife"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

typedef struct {
    uint32_t seen;
} Slot;

typedef struct {
    Slot slots[8];
} Halde;

static uint32_t summe(const Halde *h) {
    uint32_t s = 0;
    for (uint32_t eintrag = 0; eintrag < (uint32_t)(sizeof(h->slots) / sizeof(h->slots[0])); eintrag++) {
        s = s + h->slots[eintrag].seen;
    }
    return s;
}

int main(void) {
    Halde h;
    for (uint32_t k = 0; k < 8u; k++) {
        h.slots[k].seen = k;
    }
    printf("%u\n", summe(&h));
    return 0;
}
C_EOF

printf '28\n' > "$SCRATCH/expected.txt"

FAIL=0
for OPT in O0 O2; do
    if ! cc -std=c11 -Wall -Wextra -"$OPT" -o "$SCRATCH/wit-$OPT" "$SCRATCH/wit.c" 2> "$SCRATCH/cc-$OPT.log"; then
        echo "FAIL $FORM at -$OPT: compile error:"
        cat "$SCRATCH/cc-$OPT.log"
        FAIL=1
        continue
    fi
    "$SCRATCH/wit-$OPT" > "$SCRATCH/actual-$OPT.txt"
    if ! diff -u "$SCRATCH/expected.txt" "$SCRATCH/actual-$OPT.txt"; then
        echo "FAIL $FORM at -$OPT: output mismatch (diff above)"
        FAIL=1
    else
        echo "PASS $FORM at -$OPT: output $(cat "$SCRATCH/actual-$OPT.txt")"
    fi
done

if [ "$FAIL" -ne 0 ]; then
    echo "RESULT $FORM: FAIL"
    exit 1
fi
echo "RESULT $FORM: PASS (-O0 -O2)"
