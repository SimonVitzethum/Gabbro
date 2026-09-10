#!/usr/bin/env bash
# WITNESS z01-void -- C2 form `void` (930 census sites).
#
# `void` is the most-used unlisted form: every nullary function is `T name(void)`
# and every discarded value is `(void)e`. It carries no semantics of its own;
# it says "no value here".
#
# Gabbro side: standalone fragment below (hello shape). Verified 2026-09-10 to
# emit `int32_t main(void)` with zero checker errors.
# Emitter: return/parameter lowering; the `(void)e` cast idiom is emitted for
# unread bindings (see beispiele/01-tabelle.c `(void)e;` after an empty match arm).
# Expected C (emitted shape):
#   int32_t main(void) { ... }
#   (void)e;
# Behaviour: a nullary function plus a void-cast of an unread value; both must
# print the same line at -O0/-O2/-Os.
# Atomic safety: YES -- `void` performs no access, no step, no value.
#
# Run: ./z01-void.sh   (C legs only)
#      GABBRO_BIN=/path/to/gabbro ./z01-void.sh   (also re-emits, greps token)
# Exit 0 on PASS, 1 on FAIL. Every mismatch prints FAIL[z01-void] loudly.
set -u
FORM="z01-void"
TOKEN="void"
EXPECTED="void 42"
STD="c11"
FAILS=0
D="$(cd "$(dirname "$0")" && pwd)"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
say() { printf '%s\n' "$*"; }
fail() { say "FAIL[$FORM]: $*"; FAILS=$((FAILS + 1)); }

# --- leg 1: re-emit the Gabbro fragment when a binary is offered ---
if [ -n "${GABBRO_BIN:-}" ] && [ -x "${GABBRO_BIN:-}" ]; then
    cat > "$T/f.gab" <<'GAB_EOF'
module witness::z01void {
extern fn putchar(c : i32) -> i32 effects { writes output } costs <= 8 ops;
pub fn main() -> i32
    effects { writes output }
    costs   <= 40 ops
{
    putchar(72);
    putchar(10);
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
    say "EMIT[$FORM]: SKIP -- no gabbro binary (set GABBRO_BIN=path/to/gabbro to enforce); authoring-time result: emits [int32_t main(void)], 2026-09-10"
fi

# --- legs 2-4: behaviour at -O0/-O2/-Os, identical output required ---
command -v cc > /dev/null || { fail "no cc on PATH -- nothing measured"; }
cat > "$T/w.c" <<'C_EOF'
#include <stdint.h>
#include <stdio.h>
static int32_t sink(int32_t v) { (void)v; return v + 1; }
int32_t main(void) { printf("void %d\n", (int)sink(41)); return 0; }
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

say "ATOMIC-SAFE[$FORM]: YES -- void is a type-level marker; it performs no load, no store, no step."
if [ $FAILS -eq 0 ]; then say "PASS[$FORM]: void behaves identically at -O0/-O2/-Os"; else say "FAIL[$FORM]: $FAILS mismatch(es)"; exit 1; fi
