#!/usr/bin/env bash
# zuweisung — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:233: "E2: assignment is not an
# expression, one effect per statement").
#
# Gabbro fragment class: a plain store to a place, e.g.
#   ZAEHLER = 41;
# (emitter site `StmtArt::Zuweisung`, emit.rs:6791). Measured 2026-09-10
# with `gabbro emit`: the fragment lowers to the statement
#   ZAEHLER = 41;
# in statement position — never nested inside an expression (E2).
# Expected C (the form under test): the two assignment statements below,
# in the emitter's unsuffixed spelling.
# Expected behaviour: stdout holds `41 42` at every optimisation level —
# each store lands before the read that follows it.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="zuweisung"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

static uint32_t ZAEHLER __attribute__((unused)) = 0;

int main(void) {
    ZAEHLER = 41;
    printf("%u", ZAEHLER);
    ZAEHLER = ZAEHLER + 1;
    printf(" %u\n", ZAEHLER);
    return 0;
}
C_EOF

printf '41 42\n' > "$SCRATCH/expected.txt"

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
