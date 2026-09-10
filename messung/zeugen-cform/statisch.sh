#!/usr/bin/env bash
# statisch — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:231: "declaration header; no semantics
# beyond linkage").
#
# Gabbro fragment class: a plain module-level static with a constant
# initialiser, e.g.
#   static mut ZAEHLER : u32 = 0;
# (emitter site emit.rs:2040; record and array cases at emit.rs:1890 and
# emit.rs:7995). Measured 2026-09-10 with `gabbro emit`: the fragment
# lowers to
#   static uint32_t ZAEHLER __attribute__((unused)) = 0;
# Expected C (the form under test): the `static` definition below, in the
# emitter's spelling with the `__attribute__((unused))` marker.
# Expected behaviour: the counter keeps its value across calls — stdout
# holds `2` at every optimisation level. That persistence IS the linkage
# the ruling admits: no semantics beyond it is exercised here.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="statisch"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

static uint32_t ZAEHLER __attribute__((unused)) = 0;

static void tick(void) {
    ZAEHLER = ZAEHLER + 1u;
}

int main(void) {
    tick();
    tick();
    printf("%u\n", ZAEHLER);
    return 0;
}
C_EOF

printf '2\n' > "$SCRATCH/expected.txt"

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
