#!/usr/bin/env bash
# WITNESS z04-const -- C2 form `const` (419 census sites).
#
# Read-only borrows lower to `const T *restrict`: a `ptr<normal, r>` parameter
# becomes `const Halde *restrict h`. `const` is a compiler-checked promise, not
# a lock -- an alias can still mutate behind it, so it buys no thread safety.
#
# Gabbro side: standalone fragment below (table shape). Verified 2026-09-10 to
# emit `const Halde *restrict h` with zero checker errors.
# Emitter: read-pointer lowering (`const ... *restrict`).
# Expected C (emitted shape):
#   static uint64_t lesen(const Halde *restrict h, uint32_t i) {
#       if (!(i < hinterlegt)) { return 0; }
#       return h->slots[i].kopf;
#   }
# Behaviour: read through a const-restrict pointer plus a const table; values
# must agree at -O0/-O2/-Os.
# Atomic safety: NO -- const is a qualifier, not a lock; mutation through an
# alias or a cast-away still races.
#
# Run: ./z04-const.sh
#      GABBRO_BIN=/path/to/gabbro ./z04-const.sh   (also re-emits, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z04-const] loudly.
set -u
FORM="z04-const"
TOKEN="const Halde"
EXPECTED="const 50"
STD="c11"
FAILS=0
D="$(cd "$(dirname "$0")" && pwd)"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
say() { printf '%s\n' "$*"; }
fail() { say "FAIL[$FORM]: $*"; FAILS=$((FAILS + 1)); }

if [ -n "${GABBRO_BIN:-}" ] && [ -x "${GABBRO_BIN:-}" ]; then
    cat > "$T/f.gab" <<'GAB_EOF'
module witness::z04const {
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
    say "EMIT[$FORM]: SKIP -- no gabbro binary (set GABBRO_BIN=path/to/gabbro to enforce); authoring-time result: emits [const Halde *restrict h], 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdint.h>
#include <stdio.h>
static uint64_t read_slot(const uint64_t *restrict h, uint32_t i) { return h[i]; }
int main(void) {
    static const uint64_t tab[4] = {10, 20, 30, 40};
    printf("const %llu\n", (unsigned long long)(read_slot(tab, 3) + tab[0]));
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

say "ATOMIC-SAFE[$FORM]: NO -- const guards against accidents, not against threads; an alias may write."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: const behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
