#!/usr/bin/env bash
# ?: — C1 witness pair (used and on the never list).
#
# Gabbro fragment class: merge-max / merge-min lowering to the single line
#   z = (z > v) ? z : v;
# out of one emission site (MergeOp::Max / Min, emit.rs:2091-2092).
# Census: 8 sites. This is the worked ruling template of
# messung/CFORM-ABARBEITUNG.md section 3: only `?:`, `&&` and `||`
# evaluate conditionally.
# Expected C (the forbidden form under test): the max line verbatim as the
# emitter writes it, plus the mirrored min line.
# Expected behaviour: stdout holds `9 5` at every optimisation level.
# Atomic-safe verdict: YES as a single store — `z = c ? a : b` performs
# one store to `z` (only the taken arm is read), the same single-access
# class as the plain-assign rows of messung/TEARING-INVENTAR.md. The
# conditional read is not a second access to `z`.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0, -O2 and -Os, runs all three binaries
# and diffs each run against the expected output. Any mismatch fails
# loudly: unified diff on stdout, nonzero exit. All three levels run even
# if one fails, so the report answers which levels fail, not just that
# one does (no set -e over the loop, on purpose).

set -uo pipefail

FORM="ternary"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

int main(void) {
    uint32_t z = 5u, v = 9u;
    z = (z > v) ? z : v;
    uint32_t a = 5u, b = 9u;
    a = (a > b) ? b : a;
    printf("%u %u\n", z, a);
    return 0;
}
C_EOF

printf '9 5\n' > "$SCRATCH/expected.txt"

FAIL=0
for OPT in O0 O2 Os; do
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
echo "RESULT $FORM: PASS (-O0 -O2 -Os)"
