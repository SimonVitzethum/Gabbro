#!/usr/bin/env bash
# wahlLesen — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:244: "conditional read with the
# condition evaluated once").
#
# Gabbro fragment class: `match` over an `option index into T`, e.g.
#   match frei {
#       None    => { return None; }
#       Some(i) => { frei = h.slots[i].naechst; return Some(i); }
#   }
# (emitter site `match_option`, emit.rs:9033). Measured 2026-09-10 with
# `gabbro emit`: the fragment lowers to
#   {
#       uint32_t _o1 = frei;
#       if (_o1 != Halde_NONE) {
#           uint32_t i = _o1;
#           ...
#       } else {
#           ...
#       }
#   }
# The scrutinee is bound ONCE into `_o{tiefe}` and the arms read the
# binding — a call in scrutinee position would otherwise run again inside
# the arm it selected.
# Expected C (the form under test): the bind-once conditional read below,
# in the emitter's spelling. The scrutinee is a call with a side-effect
# counter, so the "evaluated once" half is measured, not asserted.
# Expected behaviour: stdout holds `3 1` then `none 2` at every
# optimisation level — the `Some` arm binds and reads the value with one
# evaluation, and the `None` arm fires with one evaluation.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="wahlLesen"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

#define Halde_NONE (8)

static uint32_t aufrufe = 0;
static uint32_t frei_wert = 3;

static uint32_t lies_frei(void) {
    aufrufe = aufrufe + 1;
    return frei_wert;
}

int main(void) {
    {
        uint32_t _o1 = lies_frei();
        if (_o1 != Halde_NONE) {
            uint32_t i = _o1;
            printf("%u %u\n", i, aufrufe);
        } else {
            printf("none %u\n", aufrufe);
        }
    }
    frei_wert = Halde_NONE;
    {
        uint32_t _o1 = lies_frei();
        if (_o1 != Halde_NONE) {
            uint32_t i = _o1;
            printf("%u %u\n", i, aufrufe);
        } else {
            printf("none %u\n", aufrufe);
        }
    }
    return 0;
}
C_EOF

printf '3 1\nnone 2\n' > "$SCRATCH/expected.txt"

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
