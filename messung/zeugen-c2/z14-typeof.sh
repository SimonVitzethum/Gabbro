#!/usr/bin/env bash
# WITNESS z14-typeof -- C2 form `__typeof__` (9 census sites).
#
# Boot and entry handover tables alias foreign function types without
# repeating them: `static __typeof__(bootinfo_retten) *const ... = ...`.
# `__typeof__` is GNU C, not ISO C -- so this witness compiles its behaviour
# leg with -std=gnu11 and says so, instead of pretending the form is portable.
#
# Gabbro side: constructs in beispiele/07-eintritt-und-boot.gab (boot steps
# s2/s3/s8/s9/dispatch), emitted as
# `static __typeof__(bootinfo_retten) *const gabbro_boot_multiboot1_s2 ...`.
# Emitter: boot/entry reference lowering.
# Expected C (emitted shape):
#   static __typeof__(bootinfo_retten) *const gabbro_boot_multiboot1_s2 __attribute__((unused)) = bootinfo_retten;
# Behaviour: a typeof-aliased const function pointer called once; the result
# must agree at -O0/-O2/-Os under gnu11.
# Atomic safety: YES -- compile-time type query; no evaluation, no access.
#
# Run: ./z14-typeof.sh
#      GABBRO_BIN=/path/to/gabbro ./z14-typeof.sh   (also re-emits 07-eintritt-und-boot.gab, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z14-typeof] loudly.
set -u
FORM="z14-typeof"
TOKEN="__typeof__"
EXPECTED="typeof 42"
STD="gnu11"
SRC="../../beispiele/07-eintritt-und-boot.gab"
FAILS=0
D="$(cd "$(dirname "$0")" && pwd)"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
say() { printf '%s\n' "$*"; }
fail() { say "FAIL[$FORM]: $*"; FAILS=$((FAILS + 1)); }

if [ -n "${GABBRO_BIN:-}" ] && [ -x "${GABBRO_BIN:-}" ] && [ -f "$D/$SRC" ]; then
    if "${GABBRO_BIN}" emit "$D/$SRC" > "$T/e.c" 2> "$T/emit.log"; then
        if grep -qF "$TOKEN" "$T/e.c"; then
            say "EMIT[$FORM]: PASS -- 07-eintritt-und-boot.gab emits [$TOKEN]"
        else
            fail "emission of $SRC lacks [$TOKEN]"
        fi
    else
        fail "gabbro emit refused $SRC:"; cat "$T/emit.log"
    fi
else
    say "EMIT[$FORM]: SKIP -- needs GABBRO_BIN=path/to/gabbro and $SRC; authoring-time result: emits [static __typeof__(bootinfo_retten) *const ...], 2026-09-10"
fi

command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdint.h>
#include <stdio.h>
static uint64_t target(uint64_t v) { return v * 2; }
int main(void) {
    static __typeof__(target) *const fp __attribute__((unused)) = target;
    __typeof__(target(0)) y = fp(21);
    printf("typeof %llu\n", (unsigned long long)y);
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

say "ATOMIC-SAFE[$FORM]: YES -- typeof names a type at compile time; nothing runs."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: typeof behaves identically at -O0/-O2/-Os (gnu11, stated, not smuggled)"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
