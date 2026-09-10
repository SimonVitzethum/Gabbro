#!/usr/bin/env bash
# rueckgabe — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:237: "single return of the declared
# type").
#
# Gabbro fragment class: `return` of a value of the declared result type,
# e.g.
#   return k;
# (emitter site `StmtArt::Return`, emit.rs:6665). Measured 2026-09-10 with
# `gabbro emit`: the fragment lowers to
#   return k;
# carrying the declared type out of the body and nothing else.
# Expected C (the form under test): the two `return` lines below — the
# early arm return and the single trailing return of the declared type.
# Expected behaviour: stdout holds `100 7` at every optimisation level —
# each call returns exactly one value of the declared type.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="rueckgabe"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

static uint32_t begrenze(uint32_t v) {
    if (v > 100) {
        return 100;
    }
    return v;
}

int main(void) {
    printf("%u %u\n", begrenze(250), begrenze(7));
    return 0;
}
C_EOF

printf '100 7\n' > "$SCRATCH/expected.txt"

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
