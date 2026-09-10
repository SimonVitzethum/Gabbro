#!/usr/bin/env bash
# WITNESS z13-while -- C2 form `while` (11 census sites).
#
# `retry ... until` with a bounded watchdog lowers to `while (!(cond))` plus
# the counter guard. The loop as a whole is unbounded from the reader's view
# (the bound is a watchdog, not a trip count), so no atomicity claim survives
# it -- other threads interleave between iterations by construction.
#
# Gabbro side: standalone fragment below (bounded retry on a status
# register). Verified 2026-09-10 to emit `while (!((*(volatile uint32_t
# *)(g->basis + 0)) == 1))` with zero checker errors.
# Emitter: retry/until lowering with watchdog counter.
# Expected C (emitted shape):
#   uint32_t _r1 = 0;
#   while (!((*(volatile uint32_t *)(g->basis + 0)) == 1)) {
#       if (_r1 >= 512u) { zeitablauf(); }
#       _r1++;
#   }
# Behaviour: the watchdog shape over a simulated register that settles after
# 5 rounds; final counter and firings must agree at -O0/-O2/-Os.
# Atomic safety: NO -- iterations interleave with other threads; the loop is
# not one step and never claimed to be.
#
# Run: ./z13-while.sh
#      GABBRO_BIN=/path/to/gabbro ./z13-while.sh   (also re-emits, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z13-while] loudly.
set -u
FORM="z13-while"
TOKEN="while"
EXPECTED="while 6 1"
STD="c11"
FAILS=0
D="$(cd "$(dirname "$0")" && pwd)"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
say() { printf '%s\n' "$*"; }
fail() { say "FAIL[$FORM]: $*"; FAILS=$((FAILS + 1)); }

if [ -n "${GABBRO_BIN:-}" ] && [ -x "${GABBRO_BIN:-}" ]; then
    cat > "$T/f.gab" <<'GAB_EOF'
module witness::z13while {
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
    say "EMIT[$FORM]: SKIP -- no gabbro binary (set GABBRO_BIN=path/to/gabbro to enforce); authoring-time result: emits [while (!(...))], 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdint.h>
#include <stdio.h>
int main(void) {
    uint32_t reg = 0;
    uint32_t r1 = 0, fired = 0;
    while (!(reg == 1)) {
        if (r1 >= 5u) { reg = 1; fired++; }
        if (r1 >= 512u) { fired += 100; break; }
        r1++;
    }
    printf("while %u %u\n", r1, fired);
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

say "ATOMIC-SAFE[$FORM]: NO -- a loop is many steps; other threads run between iterations."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: while behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
