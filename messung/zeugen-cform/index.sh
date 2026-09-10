#!/usr/bin/env bash
# index — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:243: "index over the declared range;
# pointer-index is NOT this").
#
# Gabbro fragment class: an index into a declared array member, e.g.
# `h.slots[eintrag]` where `slots` is `[Slot; 8]` (emitter site
# `ausdruck`, emit.rs:10139, `ExprArt::Ort` arm at emit.rs:9212).
# Measured 2026-09-10 with `gabbro emit`: the fragment lowers to
#   h->slots[eintrag].benutzt = true;
# The index stays inside the declared range by construction (an `index
# into T` carries its bound); indexing a bare POINTER is a different,
# unruled form (`zeigerIndex`) and is not exercised here.
# Expected C (the form under test): the member-array index below, in the
# emitter's spelling — array member, variable index, in-range constants.
# Expected behaviour: stdout holds `60` at every optimisation level —
# indices 0..3 read back exactly what was stored (10+20+30 = 60 comes
# from slots 0, 1 and 3; slot 2 holds 0).
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="index"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

typedef struct {
    uint32_t wert;
} Slot;

typedef struct {
    Slot slots[4];
} Halde;

int main(void) {
    Halde h;
    h.slots[0].wert = 10;
    h.slots[1].wert = 20;
    h.slots[2].wert = 0;
    h.slots[3].wert = 30;
    uint32_t i = 1;
    uint32_t s = h.slots[0].wert + h.slots[i].wert + h.slots[3].wert;
    printf("%u\n", s);
    return 0;
}
C_EOF

printf '60\n' > "$SCRATCH/expected.txt"

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
