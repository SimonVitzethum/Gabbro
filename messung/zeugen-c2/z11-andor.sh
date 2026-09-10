#!/usr/bin/env bash
# WITNESS z11-andor -- C2 forms `&&` / `||` (23 census sites).
#
# Ruled in messung/CFORM-REGEL-LOGUNDODER.md (admit with price): the emitter
# renders Gabbro conjunctions faithfully (`Und` as `a && b` in until
# conditions, format where-clauses, walk predicates, BinOp arms). `&&`/`||`
# evaluate conditionally with a sequence point -- a right operand with a read
# side effect may not happen, and a proof about which reads happened must
# respect that.
#
# Gabbro side: standalone fragment below (float clamp). Verified 2026-09-10 to
# emit `if (x >= 0.0 && x <= 1.0)` with zero checker errors.
# Emitter: pred_c / pred_c_format / ausdruck_breit via op_text (emit.rs
# ~4849-4873, 8203-8204, 10606-10674, 10890-10891, 7097, 11041-11045).
# Expected C (emitted shape):
#   if (x >= 0.0 && x <= 1.0) {
# Behaviour: a range guard plus two short-circuit probes whose right sides
# count their runs -- both counters must stay 0, proving the right operand
# did not evaluate, at every opt level.
# Atomic safety: NO -- two reads with a sequence point between; a concurrent
# write can land between the left and the right read.
#
# Run: ./z11-andor.sh
#      GABBRO_BIN=/path/to/gabbro ./z11-andor.sh   (also re-emits, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z11-andor] loudly.
set -u
FORM="z11-andor"
TOKEN="&&"
EXPECTED="andor 1 0 1 0"
STD="c11"
FAILS=0
D="$(cd "$(dirname "$0")" && pwd)"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
say() { printf '%s\n' "$*"; }
fail() { say "FAIL[$FORM]: $*"; FAILS=$((FAILS + 1)); }

if [ -n "${GABBRO_BIN:-}" ] && [ -x "${GABBRO_BIN:-}" ]; then
    cat > "$T/f.gab" <<'GAB_EOF'
module witness::z11andor {
type Anteil = f64 in 0.0 .. 1.0;
const HALB : f64 = 0.5;
impl fn klemmen_ohne_narrow(x : f64) -> Anteil
    effects { pure }
    costs   <= 6 ops
{
    if x >= 0.0 && x <= 1.0 { return x; }
    return HALB;
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
    say "EMIT[$FORM]: SKIP -- no gabbro binary (set GABBRO_BIN=path/to/gabbro to enforce); authoring-time result: emits [x >= 0.0 && x <= 1.0], 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdbool.h>
#include <stdio.h>
static int rhs_runs = 0;
static bool rhs_true(void) { rhs_runs++; return true; }
int main(void) {
    double x = 0.5;
    int inrange = (x >= 0.0 && x <= 1.0);
    int skipped = (false && rhs_true());
    int fallback = (true || rhs_true());
    printf("andor %d %d %d %d\n", inrange, skipped, fallback, rhs_runs);
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

say "ATOMIC-SAFE[$FORM]: NO -- conditional evaluation means two reads with a gap; another thread may write between them."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: andor behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
