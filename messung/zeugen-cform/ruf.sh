#!/usr/bin/env bash
# ruf — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:239: "call to a declared or foreign
# body").
#
# Gabbro fragment class: a call in statement or expression position, e.g.
#   putchar(65);
# (emitter site `fn ruf`, emit.rs:9641; statement position emit.rs:7105).
# Measured 2026-09-10 with `gabbro emit`: the fragment lowers to
#   putchar(65);
# naming the callee the declaration names, with the arguments in order.
# Expected C (the form under test): the two calls below — one to a
# declared body (`verdopple`), one to a foreign body (`putchar`), in the
# emitter's spelling.
# Expected behaviour: stdout holds `Hi 14` at every optimisation level —
# both callees run with the arguments they were given.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="ruf"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

int32_t putchar(int32_t c);

static uint32_t verdopple(uint32_t q) {
    return q + q;
}

int main(void) {
    putchar(72);
    putchar(105);
    putchar(10);
    printf("%u\n", verdopple(7));
    return 0;
}
C_EOF

printf 'Hi\n14\n' > "$SCRATCH/expected.txt"

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
        echo "PASS $FORM at -$OPT"
    fi
done

if [ "$FAIL" -ne 0 ]; then
    echo "RESULT $FORM: FAIL"
    exit 1
fi
echo "RESULT $FORM: PASS (-O0 -O2)"
