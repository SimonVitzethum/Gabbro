#!/usr/bin/env bash
# atomar — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:245: "named ordering; orders under
# A10").
#
# Gabbro fragment class: a declared atomic with a named ordering and its
# paired accesses, e.g.
#   atomic BEREIT : bool release;
#   let f = BEREIT awaits { stand };
#   BEREIT = true publishes { stand };
# (emitter sites: declaration emit.rs:2197, store emit.rs:7185, load
# emit.rs:7197). Measured 2026-09-10 with `gabbro emit`: the declaration
# lowers to
#   _Atomic bool BEREIT;
#   #define BEREIT_ORDER memory_order_release
# the release write to
#   atomic_store_explicit(&BEREIT, true, memory_order_release);
# and the acquire read to
#   bool f = atomic_load_explicit(&BEREIT, memory_order_acquire);
# The ordering in C is the one the source declared, not C's default; the
# pairing claim itself stands on axiom A10 and is not what this witness
# measures.
# Expected C (the form under test): the `_Atomic` declaration with its
# `_ORDER` define and the explicit-order store/load below, in the
# emitter's spelling.
# Expected behaviour: stdout holds `1` then `0` at every optimisation
# level — the release store is visible to the acquire load that follows
# it on the same thread, twice in a row.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="atomar"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdbool.h>
#include <stdatomic.h>

_Atomic bool BEREIT;
#define BEREIT_ORDER memory_order_release

int main(void) {
    atomic_store_explicit(&BEREIT, true, memory_order_release);
    bool f = atomic_load_explicit(&BEREIT, memory_order_acquire);
    printf("%d\n", (int)f);
    atomic_store_explicit(&BEREIT, false, BEREIT_ORDER);
    f = atomic_load_explicit(&BEREIT, memory_order_acquire);
    printf("%d\n", (int)f);
    return 0;
}
C_EOF

printf '1\n0\n' > "$SCRATCH/expected.txt"

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
