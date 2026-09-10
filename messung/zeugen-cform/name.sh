#!/usr/bin/env bash
# name — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:241: "identifier read; no implicit
# conversion at the read").
#
# Gabbro fragment class: a read of a bound name, e.g.
#   let x = ZAEHLER;
# (emitter site `ausdruck`, emit.rs:10139, `ExprArt::Ort` arm at
# emit.rs:9212). Measured 2026-09-10 with `gabbro emit`: the fragment
# lowers to
#   uint32_t x = ZAEHLER;
# naming the place and nothing else — the type was fixed at the
# declaration, so the read converts nothing.
# Expected C (the form under test): the two identifier reads below, in
# the emitter's spelling.
# Expected behaviour: stdout holds `41 41` at every optimisation level —
# each read carries the stored value unchanged.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="name"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

static uint32_t ZAEHLER __attribute__((unused)) = 0;

int main(void) {
    ZAEHLER = 41;
    uint32_t x = ZAEHLER;
    uint32_t y = x;
    printf("%u %u\n", x, y);
    return 0;
}
C_EOF

printf '41 41\n' > "$SCRATCH/expected.txt"

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
