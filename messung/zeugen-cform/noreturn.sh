#!/usr/bin/env bash
# noreturn — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:248: "proven non-return; the
# fall-through export needs D005 plus the tag invariant").
#
# Gabbro fragment class: a function returning `never`, e.g.
#   extern fn abbruch() -> never effects { diverges } costs <= 1 ops;
# (emitter site `ctyp_ergebnis`, emit.rs:5966: `Some(TypExpr::Never(_))`
# lowers to `_Noreturn void`). Measured 2026-09-10 with `gabbro emit`:
# the fragment lowers to
#   _Noreturn void abbruch(void);
# The qualifier is the export of a PROVEN property — the checker
# established divergence, and C only reads it back.
# Expected C (the form under test): the `_Noreturn` declaration and
# definition below, in the emitter's spelling.
# Expected behaviour: stdout holds `bereit` then `ende`, and the exit
# status is 0, at every optimisation level — the non-returning function
# runs to its own exit and control never falls through it.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries, checks
# the exit status and diffs each run against the expected output. Any
# mismatch fails loudly: unified diff on stdout, nonzero exit. Both
# levels run even if one fails, so the report answers which levels fail,
# not just that one does (no set -e over the loop, on purpose).

set -uo pipefail

FORM="noreturn"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdlib.h>

_Noreturn void zeitablauf(void);

_Noreturn void zeitablauf(void) {
    printf("ende\n");
    fflush(stdout);
    _Exit(0);
}

int main(void) {
    printf("bereit\n");
    zeitablauf();
}
C_EOF

printf 'bereit\nende\n' > "$SCRATCH/expected.txt"

FAIL=0
for OPT in O0 O2; do
    if ! cc -std=c11 -Wall -Wextra -"$OPT" -o "$SCRATCH/wit-$OPT" "$SCRATCH/wit.c" 2> "$SCRATCH/cc-$OPT.log"; then
        echo "FAIL $FORM at -$OPT: compile error:"
        cat "$SCRATCH/cc-$OPT.log"
        FAIL=1
        continue
    fi
    "$SCRATCH/wit-$OPT" > "$SCRATCH/actual-$OPT.txt"
    RC=$?
    if [ "$RC" -ne 0 ]; then
        echo "FAIL $FORM at -$OPT: exit status $RC, expected 0"
        FAIL=1
        continue
    fi
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
