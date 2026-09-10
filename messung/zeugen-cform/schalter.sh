#!/usr/bin/env bash
# schalter — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:235: "exhaustive switch, no default").
#
# Gabbro fragment class: `match` over a `tagged type`, e.g.
#   match m {
#       Leer    => { return 0; }
#       Kurz(k) => { return k; }
#       Lang(p) => { return p; }
#   }
# (emitter site `match_markiert`, emit.rs:8833). Measured 2026-09-10 with
# `gabbro emit`: the fragment lowers to
#   switch (m.marke) {
#   case Nachricht_Leer: { ... } break;
#   case Nachricht_Kurz: { uint32_t k = m.last.Kurz; ... } break;
#   case Nachricht_Lang: { uint64_t p = m.last.Lang; ... } break;
#   }
# with NO `default:` — the missing catch-all is the whole point: `-Wswitch`
# becomes a second reader of the exhaustiveness rule D005, so this witness
# compiles with `-Wswitch` on.
# Expected C (the form under test): the exhaustive `switch` below, in the
# emitter's spelling (`case T_V:` with braced arm plus `break`, payload
# read out of `.last.<variant>`).
# Expected behaviour: stdout holds `0 5 7` at every optimisation level —
# every variant dispatches to its own arm and reads its own payload.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra -Wswitch at -O0 and -O2, runs both binaries
# and diffs each run against the expected output. Any mismatch fails
# loudly: unified diff on stdout, nonzero exit. Both levels run even if
# one fails, so the report answers which levels fail, not just that one
# does (no set -e over the loop, on purpose).

set -uo pipefail

FORM="schalter"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

typedef enum {
    Nachricht_Leer,
    Nachricht_Kurz,
    Nachricht_Lang,
} Nachricht_marke;

typedef struct {
    Nachricht_marke marke;
    union {
        uint32_t Kurz;
        uint64_t Lang;
    } last;
} Nachricht;

static uint32_t gewicht(Nachricht m) {
    switch (m.marke) {
    case Nachricht_Leer: {
        return 0;
    } break;
    case Nachricht_Kurz: {
        uint32_t k = m.last.Kurz;
        return k;
    } break;
    case Nachricht_Lang: {
        uint64_t p = m.last.Lang;
        return (uint32_t)p;
    } break;
    }
    return 0;
}

int main(void) {
    Nachricht a = { Nachricht_Leer, { .Kurz = 0 } };
    Nachricht b = { Nachricht_Kurz, { .Kurz = 5 } };
    Nachricht c = { Nachricht_Lang, { .Lang = 7 } };
    printf("%u %u %u\n", gewicht(a), gewicht(b), gewicht(c));
    return 0;
}
C_EOF

printf '0 5 7\n' > "$SCRATCH/expected.txt"

FAIL=0
for OPT in O0 O2; do
    if ! cc -std=c11 -Wall -Wextra -Wswitch -"$OPT" -o "$SCRATCH/wit-$OPT" "$SCRATCH/wit.c" 2> "$SCRATCH/cc-$OPT.log"; then
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
