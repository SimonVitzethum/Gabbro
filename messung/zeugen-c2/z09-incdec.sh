#!/usr/bin/env bash
# WITNESS z09-incdec -- C2 forms `++` / `--` (42 census sites).
#
# The retry watchdog counts with `_r1++`; countdowns elsewhere use `--`. Both
# are read-modify-write on a plain object -- the classic non-atomic, and the
# reason the verdict below is NO despite the single-threaded determinism.
#
# Gabbro side: standalone fragment below (bounded retry). Verified 2026-09-10
# to emit `_r1++` inside `while (!(...))` with zero checker errors.
# Emitter: retry/watchdog lowering (counter increment); `--` shares the
# postfix lowering -- the behaviour leg covers both, the emit leg pins `++`.
# Expected C (emitted shape):
#   uint32_t _r1 = 0;
#   while (!((*(volatile uint32_t *)(g->basis + 0)) == 1)) {
#       if (_r1 >= 512u) { zeitablauf(); }
#       _r1++;
#   }
# Behaviour: count up to 10 with `++`, count down to 4 with `--`; both bounds
# must hold at -O0/-O2/-Os.
# Atomic safety: NO -- read-modify-write on a plain object; concurrent
# increments can be lost (only _Atomic increments are indivisible).
#
# Run: ./z09-incdec.sh
#      GABBRO_BIN=/path/to/gabbro ./z09-incdec.sh   (also re-emits, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z09-incdec] loudly.
set -u
FORM="z09-incdec"
TOKEN="++"
EXPECTED="incdec 10 4"
STD="c11"
FAILS=0
D="$(cd "$(dirname "$0")" && pwd)"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
say() { printf '%s\n' "$*"; }
fail() { say "FAIL[$FORM]: $*"; FAILS=$((FAILS + 1)); }

if [ -n "${GABBRO_BIN:-}" ] && [ -x "${GABBRO_BIN:-}" ]; then
    cat > "$T/f.gab" <<'GAB_EOF'
module witness::z09incdec {
device Statusregister(basis : Pa) at mmio {
    reg fertig : u32 @0x0 class r
}
extern fn zeitablauf() -> never effects { diverges };
assume geraet_antwortet
    "A status register that sets fertig does so within the promised reads."
    falsifier sonde_geraet_antwortet;
impl fn auf_quittung_warten(g : ptr<mmio, r> Statusregister) -> u32
    effects { reads g }
    costs   <= 2048 ops
{
    retry warten until g.fertig == 1
        bounded 1024 ops
        progress geraet_antwortet
        on_exceeded zeitablauf
        effects { reads g }
    { }
    return 0;
}
}
GAB_EOF
    if "${GABBRO_BIN}" emit "$T/f.gab" > "$T/f.c" 2> "$T/emit.log"; then
        if grep -qF "$TOKEN" "$T/f.c"; then
            say "EMIT[$FORM]: PASS -- fragment emits [$TOKEN]"
        else
            fail "emission lacks [$TOKEN]"
        fi
    else
        fail "gabbro emit refused the fragment:"; cat "$T/emit.log"
    fi
else
    say "EMIT[$FORM]: SKIP -- no gabbro binary (set GABBRO_BIN=path/to/gabbro to enforce); authoring-time result: emits [_r1++], 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdint.h>
#include <stdio.h>
int main(void) {
    uint32_t r = 0;
    uint32_t i = 0;
    while (i < 10) { r++; i++; }
    while (r > 4) { r--; }
    printf("incdec %u %u\n", i, r);
    return 0;
}
C_EOF
REF=""
for OPT in O0 O2 Os; do
    if ! cc -std=${STD} -Wall -Wextra "-$OPT" -o "$T/w-$OPT" "$T/w.c" 2> "$T/cc-$OPT.log"; then
        fail "cc -$OPT refused the program:"; cat "$T/cc-$OPT.log"; continue
    fi
    OUT="$("$T/w-$OPT")"; CODE=$?
    [ $CODE -eq 0 ] || fail "cc -$OPT exit code $CODE, want 0"
    [ "$OUT" = "$EXPECTED" ] || fail "cc -$OPT output [$OUT], want [$EXPECTED]"
    if [ -z "$REF" ]; then REF="$OUT"; elif [ "$OUT" != "$REF" ]; then fail "-$OPT output [$OUT] disagrees with -O0 [$REF]"; fi
done

say "ATOMIC-SAFE[$FORM]: NO -- plain ++/-- is read-modify-write; concurrent use loses updates."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: incdec behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
