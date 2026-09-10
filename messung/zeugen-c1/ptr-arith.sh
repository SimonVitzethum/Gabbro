#!/usr/bin/env bash
# Pointer arithmetic — C1 witness pair (used and on the never list).
#
# Gabbro fragment class: device register access lowering to
#   *(volatile uint8_t *)(basis + off)
# (census: dokumente/BEWEIS.md line 807, `d->basis + 8`, 491 sites;
# contradicts the old inventory row 2 claim of no pointer arithmetic).
# Expected C (the forbidden form under test): `basis + 2`, `basis + 4`
# and the pointer difference `(basis + 8) - basis`.
# Expected behaviour: stdout holds `4 5 8` at every optimisation level.
# Atomic-safe verdict: YES, vacuously — address computation performs no
# load and no store, so there is nothing to tear. Tearing applies only to
# the dereference built on top of it (see index-on-ptr.sh). Feeds
# messung/TEARING-INVENTAR.md as a non-access: no new table row.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0, -O2 and -Os, runs all three binaries
# and diffs each run against the expected output. Any mismatch fails
# loudly: unified diff on stdout, nonzero exit. All three levels run even
# if one fails, so the report answers which levels fail, not just that
# one does (no set -e over the loop, on purpose).

set -uo pipefail

FORM="ptr-arith"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

int main(void) {
    uint8_t bytes[8] = {3, 1, 4, 1, 5, 9, 2, 6};
    uint8_t *basis = bytes;
    uint8_t a = *(basis + 2);
    uint8_t b = *(basis + 4);
    uint8_t n = (uint8_t)((basis + 8) - basis);
    printf("%u %u %u\n", a, b, n);
    return 0;
}
C_EOF

printf '4 5 8\n' > "$SCRATCH/expected.txt"

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
