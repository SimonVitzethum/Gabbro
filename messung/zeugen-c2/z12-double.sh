#!/usr/bin/env bash
# WITNESS z12-double -- C2 form `double` (18 census sites).
#
# A bare floating literal is a `double` in C, and `f64` lowers to `double`.
# The emission carries its own certificate: `-ffast-math` forbidden (addition
# is not associative), SSE2 presupposed, round-to-nearest-even assumed with a
# named falsifier. None of that makes a double step atomic.
#
# Gabbro side: standalone fragment below (f64 clamp, beispiele/26 shape).
# Verified 2026-09-10 to emit `static double klemmen_ohne_narrow(double x)`
# with zero checker errors.
# Emitter: f32/f64 lowering (`f64` to `double`, emit.rs ~5110-5120).
# Expected C (emitted shape):
#   static double klemmen_ohne_narrow(double x) {
#       if (x >= 0.0 && x <= 1.0) {
# Behaviour: clamp three exactly-representable values; all print with %.6f
# and must match at -O0/-O2/-Os (no fast-math anywhere in these legs).
# Atomic safety: NO -- C promises no atomicity for double access; tearing and
# rounding-mode dependence stay possible.
#
# Run: ./z12-double.sh
#      GABBRO_BIN=/path/to/gabbro ./z12-double.sh   (also re-emits, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z12-double] loudly.
set -u
FORM="z12-double"
TOKEN="double"
EXPECTED="double 0.500000 0.250000 0.500000"
STD="c11"
FAILS=0
D="$(cd "$(dirname "$0")" && pwd)"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
say() { printf '%s\n' "$*"; }
fail() { say "FAIL[$FORM]: $*"; FAILS=$((FAILS + 1)); }

if [ -n "${GABBRO_BIN:-}" ] && [ -x "${GABBRO_BIN:-}" ]; then
    cat > "$T/f.gab" <<'GAB_EOF'
module witness::z12double {
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
    say "EMIT[$FORM]: SKIP -- no gabbro binary (set GABBRO_BIN=path/to/gabbro to enforce); authoring-time result: emits [static double klemmen_ohne_narrow(double x)], 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdio.h>
static double clamp(double x) { if (!(x >= 0.0 && x <= 1.0)) return 0.5; return x; }
int main(void) { printf("double %.6f %.6f %.6f\n", clamp(2.5), clamp(0.25), clamp(0.5)); return 0; }
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

say "ATOMIC-SAFE[$FORM]: NO -- no atomicity promised for floating access; width and rounding rest on machine assumptions."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: double behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
