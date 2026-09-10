#!/usr/bin/env bash
# beschraenkt — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:246 with `beschraenktPreis`
# (Erhaltung.lean:219): "exports the effects-promise into C UB rules; only
# where the benchmark buys it").
#
# Gabbro fragment class: a table pointer parameter, e.g.
#   impl fn markiere(h : ptr<normal, rw> Halde)
# (emitter site emit.rs:5983: `restrict` is written where `darf_restrict`
# holds). Measured 2026-09-10 with `gabbro emit`: the parameter lowers to
#   Halde *restrict h
# The qualifier exports the caller's exclusive-access promise into C's
# aliasing rules — that export is the priced part of this ruling, and it
# is only written where the checker earned it.
# Expected C (the form under test): the `*restrict` parameter below, in
# the emitter's spelling. The caller keeps no alias across the call, so
# the promise holds and the program is defined.
# Expected behaviour: stdout holds `8` at every optimisation level — all
# eight slots are marked through the restricted pointer.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="beschraenkt"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>

typedef struct {
    bool benutzt;
    uint32_t naechst;
} Halde_slot;

typedef struct {
    Halde_slot slots[8];
} Halde;

static void markiere(Halde *restrict h) {
    for (uint32_t eintrag = 0; eintrag < (uint32_t)(sizeof(h->slots) / sizeof(h->slots[0])); eintrag++) {
        h->slots[eintrag].benutzt = true;
    }
}

int main(void) {
    Halde h;
    for (uint32_t k = 0; k < 8u; k++) {
        h.slots[k].benutzt = false;
        h.slots[k].naechst = k;
    }
    markiere(&h);
    uint32_t n = 0;
    for (uint32_t k = 0; k < 8u; k++) {
        if (h.slots[k].benutzt) {
            n = n + 1;
        }
    }
    printf("%u\n", n);
    return 0;
}
C_EOF

printf '8\n' > "$SCRATCH/expected.txt"

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
