#!/usr/bin/env bash
# extern — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:232: "foreign body; the null-spelling
# boundary lives here").
#
# Gabbro fragment class: a foreign declaration, e.g.
#   extern fn putchar(c : i32) -> i32 effects { writes output } costs <= 8 ops;
# (emitter site `prototyp_kern`, emit.rs:5930). Measured 2026-09-10 with
# `gabbro emit`: the fragment lowers to the bare prototype
#   int32_t putchar(int32_t c);
# with no `extern` keyword and no body — the foreign body lives outside
# the translation unit.
# Expected C (the form under test): the prototype line below, in the
# emitter's spelling. The signature must be C's own (`i32`, not `u32`,
# since C declares `int putchar(int)`).
# Expected behaviour: stdout holds `Hi` at every optimisation level —
# the foreign body runs and the declared signature calls it correctly.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="extern"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

int32_t putchar(int32_t c);

int main(void) {
    putchar(72);
    putchar(105);
    putchar(10);
    return 0;
}
C_EOF

printf 'Hi\n' > "$SCRATCH/expected.txt"

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
