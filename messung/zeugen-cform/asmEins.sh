#!/usr/bin/env bash
# asmEins — CForm witness pair (named shape, admitted per
# grammatik/Grammatik/Erhaltung.lean:249: "exactly one emission site; no
# downstream prover (16.2 (7))").
#
# Gabbro fragment class: a single-instruction `asm` body, e.g.
#   impl fn ausgeben(tor : u16, wert : u8)
#       effects { writes GERAET }
#       costs   <= 1 ops
#       arch    x86_64
#       = asm {
#           "outb %[wert], %[tor]"
#           in { wert : "a", tor : "d" }
#           clobbers { memory }
#       };
# (emitter site emit.rs:3730). Measured 2026-09-10 with `gabbro emit`:
# the body lowers to
#   __asm__ __volatile__(
#       "outb %[wert], %[tor]\n"
#       :
#       : [wert] "a" (wert), [tor] "d" (tor)
#       : "memory");
# Gabbro does not read the instruction text — the body is a sealed hole
# carrying `arch`, `effects` and `costs` where the passes already read
# them. The witness below uses a userspace-runnable `movl` in the same
# one-instruction shape (`outb` needs port permission and would fault).
# Expected C (the form under test): the single `__asm__ __volatile__`
# block below, with operand lists and a `memory` clobber, in the
# emitter's spelling. x86-64 only, like the `arch x86_64` gate on the
# Gabbro source.
# Expected behaviour: stdout holds `42` at every optimisation level —
# the one instruction moves the constant into the output operand.
#
# Method: writes the C program below to a scratch file, compiles it with
# cc -std=c11 -Wall -Wextra at -O0 and -O2, runs both binaries and diffs
# each run against the expected output. Any mismatch fails loudly:
# unified diff on stdout, nonzero exit. Both levels run even if one
# fails, so the report answers which levels fail, not just that one does
# (no set -e over the loop, on purpose).

set -uo pipefail

FORM="asmEins"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

if [ "$(uname -m)" != "x86_64" ]; then
    echo "FAIL $FORM: needs x86_64, uname says $(uname -m)"
    exit 1
fi

cat > "$SCRATCH/wit.c" <<'C_EOF'
#include <stdio.h>
#include <stdint.h>

static uint32_t lies_wert(void) {
    uint32_t _w;
    __asm__ __volatile__(
        "movl $42, %[wert]\n"
        : [wert] "=a" (_w)
        :
        : "memory");
    return _w;
}

int main(void) {
    printf("%u\n", lies_wert());
    return 0;
}
C_EOF

printf '42\n' > "$SCRATCH/expected.txt"

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
