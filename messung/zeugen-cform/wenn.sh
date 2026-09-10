#!/usr/bin/env bash
# wenn — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:234: "two-sided branch; no
# fall-through").
#
# Gabbro fragment class: a two-sided conditional, e.g.
#   if x == 41 { putchar(65); } else { putchar(66); }
# (emitter site `StmtArt::Wenn`, emit.rs:7484). Measured 2026-09-10 with
# `gabbro emit`: the fragment lowers to
#   if (x == 41) {
#       ...
#   } else {
#       ...
#   }
# Expected C (the form under test): the two-sided `if` below — both arms
# present, each arm ending in `return`, so control never falls through.
# Expected behaviour: stdout holds `1 0` at every optimisation level —
# the taken arm and the untaken arm each answer once.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="wenn"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

static uint32_t ast(uint32_t x) {
    if (x == 41) {
        return 1;
    } else {
        return 0;
    }
}

int main(void) {
    printf("%u %u\n", ast(41), ast(7));
    return 0;
}
C_EOF

printf '1 0\n' > "$SCRATCH/expected.txt"

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
