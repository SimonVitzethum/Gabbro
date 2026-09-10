#!/usr/bin/env bash
# feld — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:242: "field access; padding bytes
# never read").
#
# Gabbro fragment class: a read of a declared record field, e.g.
# `m.last.Kurz` out of a `match` arm or `h.slots[i].naechst` out of a
# table slot (emitter site `ausdruck`, emit.rs:10139, `ExprArt::Ort` arm
# at emit.rs:9212). Measured 2026-09-10 with `gabbro emit`: field reads
# lower to member selection —
#   m.marke, m.last.Kurz, h->slots[i].naechst
# naming the declared member and nothing around it.
# Expected C (the form under test): the `.` and `->` member selections
# below, in the emitter's spelling. The struct carries a padding-prone
# layout (`uint8_t` beside `uint32_t`); only named members are read.
# Expected behaviour: stdout holds `5 7` at every optimisation level —
# each selection reads its own member.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="feld"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

typedef struct {
    uint8_t marke;
    uint32_t last_Kurz;
    uint64_t last_Lang;
} Nachricht;

typedef struct {
    Nachricht *p;
} Halter;

int main(void) {
    Nachricht m;
    m.marke = 1;
    m.last_Kurz = 5;
    m.last_Lang = 7;
    Halter h;
    h.p = &m;
    printf("%u %u\n", (unsigned)m.last_Kurz, (unsigned)h.p->last_Lang);
    return 0;
}
C_EOF

printf '5 7\n' > "$SCRATCH/expected.txt"

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
