#!/usr/bin/env bash
# sprungAlsSchleifenende — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:238: "goto ONLY as a generated loop
# exit; counted, target unchecked").
#
# Gabbro fragment class: `leave` out of a named loop, e.g.
#   forever schleife
#       per_pass bounded 64 ops
#       on_exceeded zeitablauf
#       effects { pure }
#       progress tickt
#   {
#       leave schleife;
#   }
# (emitter site emit.rs:7531). Measured 2026-09-10 with `gabbro emit`:
# the fragment lowers to
#   for (;;) {
#       goto schleife_ende;
#   }
#   schleife_ende: ;
# A `break` would always leave the INNERMOST loop, so the emitter writes
# a named `goto` instead; the label is the loop exit and nothing else.
# Expected C (the form under test): the `goto <mark>_ende;` jump and its
# `<mark>_ende: ;` target below, in the emitter's spelling. The counter
# around them only makes the exit observable — the form under test is the
# jump and its label.
# Expected behaviour: stdout holds `3` at every optimisation level — the
# loop runs three passes and the generated exit fires exactly once.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="sprungAlsSchleifenende"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>

int main(void) {
    int n = 0;
    for (;;) {
        n = n + 1;
        if (n >= 3) {
            goto schleife_ende;
        }
    }
    schleife_ende: ;
    printf("%d\n", n);
    return 0;
}
C_EOF

printf '3\n' > "$SCRATCH/expected.txt"

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
