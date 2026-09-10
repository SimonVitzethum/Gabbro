#!/usr/bin/env bash
# literal — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:240: "constant of a named type").
#
# Gabbro fragment class: an integer literal at a named type, e.g. `41`
# where a `u32` is expected, or the option sentinel `Halde_NONE` the
# emitter defines as `(8)` (emitter site `zahltext`, emit.rs:5055).
# Measured 2026-09-10 with `gabbro emit`: literals lower to plain decimal
# text (`41`, `0`, `72`) with no suffix — the TYPE comes from the named
# declaration around them, never from the spelling.
# Expected C (the form under test): the decimal constants below, in the
# emitter's unsuffixed spelling, folded and printed at a named type.
# Expected behaviour: stdout holds `41 0 42` at every optimisation level —
# the constants carry the values they spell.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="literal"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

int main(void) {
    uint32_t a = 41;
    uint32_t b = 0;
    uint32_t c = 6 * 7;
    printf("%u %u %u\n", a, b, c);
    return 0;
}
C_EOF

printf '41 0 42\n' > "$SCRATCH/expected.txt"

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
