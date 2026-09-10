#!/usr/bin/env bash
# WITNESS z15-float -- C2 form `float` (8 census sites).
#
# `f32` lowers to `float`, and a bare literal stays `double` -- so `x * 0.1`
# at `x : f32` computes in DOUBLE and rounds only at the return (W24 lead:
# 39 974 of 200 000 values differ from `v * 0.1f`). Width is meaning here,
# and this witness pins the exact case: `(double)0.1f == 0.1` is false.
#
# Gabbro side: standalone fragment below (messung/proben/probe-f32-literal
# shape). Verified 2026-09-10 to emit `static float zehntel(float x)` with
# zero checker errors.
# Emitter: f32 lowering (`f32` to `float`, emit.rs ~5110-5120, 5157).
# Expected C (emitted shape):
#   static float zehntel(float x) {
# Behaviour: a float multiply on exactly-representable values plus the
# float/double width inequality; both must hold at -O0/-O2/-Os.
# Atomic safety: NO -- same as double: no atomicity promised, width and
# rounding rest on machine assumptions.
#
# Run: ./z15-float.sh
#      GABBRO_BIN=/path/to/gabbro ./z15-float.sh   (also re-emits, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z15-float] loudly.
set -u
FORM="z15-float"
TOKEN="float"
EXPECTED="float 0.25 0"
STD="c11"
FAILS=0
D="$(cd "$(dirname "$0")" && pwd)"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
say() { printf '%s\n' "$*"; }
fail() { say "FAIL[$FORM]: $*"; FAILS=$((FAILS + 1)); }

if [ -n "${GABBRO_BIN:-}" ] && [ -x "${GABBRO_BIN:-}" ]; then
    cat > "$T/f.gab" <<'GAB_EOF'
module witness::z15float {
type Bruch = f32 in 0.0 .. 10.0;
impl fn zehntel(x : Bruch) -> Bruch
    effects { pure }
    costs   <= 4 ops
{
    return x * 0.1 rounded;
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
    say "EMIT[$FORM]: SKIP -- no gabbro binary (set GABBRO_BIN=path/to/gabbro to enforce); authoring-time result: emits [static float zehntel(float x)], 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdio.h>
static float halbiere(float x) __attribute__((const)) __attribute__((unused));
static float halbiere(float x) { return x * 0.5f; }
int main(void) {
    float q = halbiere(0.5f);
    int narrow = ((double)0.1f == 0.1);
    printf("float %.9g %d\n", (double)q, narrow);
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

say "ATOMIC-SAFE[$FORM]: NO -- floating access is not atomic; width and rounding are machine assumptions."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: float behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
