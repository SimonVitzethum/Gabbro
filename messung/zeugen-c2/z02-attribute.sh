#!/usr/bin/env bash
# WITNESS z02-attribute -- C2 form `__attribute__` (766 census sites).
#
# The emitter marks every generated declaration it may not call:
# `__attribute__((unused))` on statics, `__attribute__((const))` / `pure` on
# side-effect-free functions. Without the mark, `cc -Wall` drowns the build in
# unused warnings; with it, an unused static is a fact, not noise.
#
# Gabbro side: standalone fragment below (table shape, messung/narrow idiom).
# Verified 2026-09-10 to emit `__attribute__((unused))` and
# `__attribute__((pure))` with zero checker errors.
# Emitter: emit.rs `__attribute__((unused))` suffix helper (~line 3118) and the
# `__attribute__((const))`/`pure` function marks (see 26-gleitkomma.c).
# Expected C (emitted shape):
#   static uint32_t hinterlegt __attribute__((unused)) = 4096;
#   static uint64_t lesen(const Halde *restrict h, uint32_t i) __attribute__((pure)) __attribute__((unused));
# Behaviour: an unused-marked static that IS called plus a const-marked pure
# function; the marks must not change the values at any opt level.
# Atomic safety: YES -- an annotation; it changes diagnostics, not steps.
#
# Run: ./z02-attribute.sh
#      GABBRO_BIN=/path/to/gabbro ./z02-attribute.sh   (also re-emits, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z02-attribute] loudly.
set -u
FORM="z02-attribute"
TOKEN="__attribute__"
EXPECTED="attr 5 7"
STD="c11"
FAILS=0
D="$(cd "$(dirname "$0")" && pwd)"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
say() { printf '%s\n' "$*"; }
fail() { say "FAIL[$FORM]: $*"; FAILS=$((FAILS + 1)); }

if [ -n "${GABBRO_BIN:-}" ] && [ -x "${GABBRO_BIN:-}" ]; then
    cat > "$T/f.gab" <<'GAB_EOF'
module witness::z02attr {
const K : u32 = 4096;
static mut hinterlegt : u32 in 0 .. K = 4096;
table Halde count K backed hinterlegt { slot { kopf : u64, } }
impl fn lesen(h : ptr<normal, r> Halde, i : index into Halde) -> u64
    effects { reads h.slots, reads hinterlegt }
    costs   <= 4 ops
{
    narrow i to 0 ..< hinterlegt else { return 0; }
    return h.slots[i].kopf;
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
    say "EMIT[$FORM]: SKIP -- no gabbro binary (set GABBRO_BIN=path/to/gabbro to enforce); authoring-time result: emits [__attribute__((unused))] and [__attribute__((pure))], 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdint.h>
#include <stdio.h>
static uint64_t mask_low10(uint64_t x) __attribute__((const)) __attribute__((unused));
static uint64_t mask_low10(uint64_t x) { return x & 1023u; }
static uint32_t spare __attribute__((unused)) = 7;
int main(void) { printf("attr %u %u\n", (unsigned)mask_low10(4096u + 5u), spare); return 0; }
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

say "ATOMIC-SAFE[$FORM]: YES -- attributes annotate a declaration; they add no load, no store, no step."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: __attribute__ behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
