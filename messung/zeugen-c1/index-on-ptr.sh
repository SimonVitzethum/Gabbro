#!/usr/bin/env bash
# Index on a pointer — C1 witness pair (used and on the never list).
#
# Gabbro fragment class: slot field access such as `c.slots[s].objekt`
# lowering to `c->slots[s].objekt` (emitter note at emit.rs:622; census:
# 156 sites). `p[i]` is `*(p + i)` by definition of C, so this form is
# pointer arithmetic with a dereference on top.
# Expected C (the forbidden form under test): `p[0]`, `p[2]`, `p[3]`
# where `p` is a plain `uint32_t *`, not an array name.
# Expected behaviour: stdout holds `7 21 28` at every optimisation level.
# Atomic-safe verdict: YES as a single access — each `p[i]` evaluation is
# one narrow aligned load, the same single-access class as the plain-assign
# rows of messung/TEARING-INVENTAR.md. A read-modify-write through `p[i]`
# would be a sequence and is not covered by this verdict.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0, -O2 and -Os, runs all three binaries
# and diffs each run against the expected output. Any mismatch fails
# loudly: unified diff on stdout, nonzero exit. All three levels run even
# if one fails, so the report answers which levels fail, not just that
# one does (no set -e over the loop, on purpose).

set -uo pipefail

FORM="index-on-ptr"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

int main(void) {
    uint32_t v[4] = {7, 14, 21, 28};
    uint32_t *p = v;
    printf("%u %u %u\n", p[0], p[2], p[3]);
    return 0;
}
C_EOF

printf '7 21 28\n' > "$SCRATCH/expected.txt"

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
