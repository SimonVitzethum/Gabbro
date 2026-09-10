#!/usr/bin/env bash
# enum — C1 witness pair (used and on the never list).
#
# Gabbro fragment class: a reason declaration lowering to
#   typedef enum { ... } Color;
# (emitter site emit.rs:2315; the list asks for enum-free constants).
# Census: 28 sites.
# Expected C (the forbidden form under test): the `Color` enumeration
# below, with one enumerator read through a variable and one directly.
# Expected behaviour: stdout holds `1 2` at every optimisation level.
# Atomic-safe verdict: YES, vacuously — compile-time constants emitting
# no runtime access at all. Feeds messung/TEARING-INVENTAR.md as a
# non-access: no new table row.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0, -O2 and -Os, runs all three binaries
# and diffs each run against the expected output. Any mismatch fails
# loudly: unified diff on stdout, nonzero exit. All three levels run even
# if one fails, so the report answers which levels fail, not just that
# one does (no set -e over the loop, on purpose).

set -uo pipefail

FORM="enum"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>

typedef enum {
    RED = 0,
    GREEN = 1,
    BLUE = 2
} Color;

int main(void) {
    Color c = GREEN;
    printf("%d %d\n", (int)c, (int)BLUE);
    return 0;
}
C_EOF

printf '1 2\n' > "$SCRATCH/expected.txt"

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
