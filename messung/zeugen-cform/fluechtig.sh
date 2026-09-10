#!/usr/bin/env bash
# fluechtig — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:247 with `fluechtigPreis`
# (Erhaltung.lean:224): "axiom, named; seL4 excludes exactly this").
#
# Gabbro fragment class: a read of a device register, e.g.
#   return g.fertig;
# where `g : ptr<mmio, r> Statusregister` (emitter site `geraetelesung`,
# emit.rs:3520). Measured 2026-09-10 with `gabbro emit`: the read lowers
# to
#   return (*(volatile uint32_t *)(g->basis + 0));
# A register read must not be optimised away or merged — that is what
# `volatile` stands for — and two reads of the same register are two
# values, since the device may change it between them.
# Expected C (the form under test): the volatile load below, in the
# emitter's spelling (`*(volatile <w> *)` over `basis + offset`). A RAM
# buffer stands in for device memory; the shape is the MMIO one.
# Expected behaviour: stdout holds `42` then `43` at every optimisation
# level — each volatile read observes the current buffer content,
# including the store between the two reads that a non-volatile load
# would be free to ignore. Little-endian byte order, measured on x86-64.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="fluechtig"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

typedef struct { volatile uint8_t *basis; } Statusregister;

static uint8_t speicher[8] = { 42, 0, 0, 0, 0, 0, 0, 0 };

int main(void) {
    Statusregister g;
    g.basis = speicher;
    uint32_t w = (*(volatile uint32_t *)(g.basis + 0));
    printf("%u\n", w);
    speicher[0] = 43;
    w = (*(volatile uint32_t *)(g.basis + 0));
    printf("%u\n", w);
    return 0;
}
C_EOF

printf '42\n43\n' > "$SCRATCH/expected.txt"

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
        echo "PASS $FORM at -$OPT"
    fi
done

if [ "$FAIL" -ne 0 ]; then
    echo "RESULT $FORM: FAIL"
    exit 1
fi
echo "RESULT $FORM: PASS (-O0 -O2)"
