#!/usr/bin/env bash
# **Rule A for the BODY CHANNEL: does a generated obligation over a BODY really go through?**
#
# `gabbro pflichten --lean` writes a unit's obligation register as a Lean 4 module -- the body
# as a datum of `Gabbro.Body`, the postcondition as an expression, the goal as a theorem. *A
# generated obligation no prover has ever read is again just a line in a report -- only in a
# different file.*
#
#     .gab  ->  gabbro pflichten --lean  ->  .lean  ->  lean  ->  green
#
# **It builds EVERY unit that yields a register, not only the ones that carry a goal.** Two
# different things are being asked, and only both together mean anything:
#
#   1. is what the emitter writes VALID Lean at all -- also where it consists purely of named
#      refusals? *A module nobody ever fed to the prover is a text file.*
#   2. does at least one GENERATED obligation go through? That is Rule A, and it is checked as
#      a count: zero theorems over the whole corpus turns this guardian red.
#
# **The model lives in `programmlogik/`, not in `passlogik/`.** The latter formalises the
# CHECKER; what is proved here is a statement about a PROGRAM. Those are different claims and
# they do not share a namespace.
#
# **Nothing here is checked in.** The modules are written afresh on every run; a carried
# artefact would be the second register over one thing.
#
# **W1: a skipped run is not a passed one.** With no Lean this guardian turns red rather than
# declaring itself passed. And the deadline is handled by hand: `set -e` on return code 124
# would end this script SILENTLY -- the exact trap `pruefe-emission.sh` fell into on
# 2026-08-20, where the deadline was there and the requirement was not met.
set -euo pipefail

# **`LC_ALL=C`, and it is not a nicety.** Foreign tools report in the user's locale, and a
# `grep` written against the English wording then matches nothing. Same class as `W16`: a tool
# that measures its own locale and looks plausible doing it.
export LC_ALL=C

W="$(cd "$(dirname "$0")/.." && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

GABBRO="$W/target/debug/gabbro"
LEANBIN="${LEANBIN:-$HOME/.elan/bin/lean}"
LAKE="${LAKE:-$HOME/.elan/bin/lake}"
MODEL="${MODEL:-$W/programmlogik}"
DEADLINE=120

if [ ! -x "$GABBRO" ]; then
    echo "== LEAN PROOF: NO GABBRO -- it is built on ki-pc-fisch-101 (CLAUDE.md) =="
    exit 1
fi
if [ ! -x "$LEANBIN" ] || [ ! -x "$LAKE" ]; then
    echo "== LEAN PROOF: NO LEAN at $LEANBIN -- NOTHING measured =="
    echo "  A missing tool is not a passed test (W1)."
    exit 1
fi

# **The meaning of a body must be built before any goal can cite it.**
echo "== Building the meaning of a body =="
if ! (cd "$MODEL" && timeout "$DEADLINE" "$LAKE" build Gabbro.Body > "$TMP/lake.log" 2>&1); then
    cat "$TMP/lake.log"
    echo "== LEAN PROOF: Gabbro.Body does not build -- the MODEL is red, not the product =="
    exit 1
fi
LP="$MODEL/.lake/build/lib/lean"
echo "   Gabbro.Body built"

# One Lean run over one file. 0 green, 1 red, 2 the deadline -- and the deadline is its own
# answer, neither red nor green. **A warning is not a red**: a hypothesis the proof does not
# need is one hypothesis too many, and that is a finding, not a failure of this guardian.
run_lean() {
    local f="$1" rc=0
    LEAN_PATH="$LP" timeout "$DEADLINE" "$LEANBIN" "$f" > "$f.log" 2>&1 || rc=$?
    if [ "$rc" -eq 124 ]; then return 2; fi
    if grep -q 'error:' "$f.log"; then return 1; fi
    if [ "$rc" -ne 0 ]; then return 1; fi
    return 0
}

# **The speech test, in both directions** (R11). *A guardian that is green on the first try
# without anyone having seen it fall is an ornament.*
#
# And it stands over THE SAME MODEL as the product, not over `2 + 2 = 4`: the same body writes
# `false` into a field, and once the theorem afterwards claims `not f` and once `f`. **Only
# that way does the test measure the channel rather than Lean.**
speech_test() {
    local good=0 poison=0 case_ d post
    for case_ in good poison; do
        d="$TMP/probe-$case_.lean"
        if [ "$case_" = good ]; then
            post='(.un .not (.place "T" (.lit (.int 0)) "f"))'
        else
            post='(.place "T" (.lit (.int 0)) "f")'
        fi
        cat > "$d" <<LEAN
import Gabbro.Body
set_option autoImplicit false
open Gabbro.Body
def body : List Stmt := [(.assign "T" (.lit (.int 0)) "f" (.lit (.bool false)))]
def post : Expr := $post
theorem probe (s : State)
    : ∃ s', finalState (exec body s) = some s' ∧ eval s' post = some (.bool true) := by
  simp [body, post, exec, step, eval, unop, binop, finalState, store, bindLocal]
LEAN
        if run_lean "$d"; then
            [ "$case_" = good ] && good=1
        else
            [ "$case_" = poison ] && poison=1
        fi
    done
    echo "== Speech test =="
    echo "  a true theorem goes through: $([ $good   -eq 1 ] && echo yes || echo NO)"
    echo "  a false theorem falls:       $([ $poison -eq 1 ] && echo yes || echo NO)"
    [ $good -eq 1 ] && [ $poison -eq 1 ]
}

if ! speech_test; then
    echo "== LEAN PROOF: this guardian measures nothing -- Lean does not answer as expected =="
    exit 1
fi

UNITS=0
NO_REGISTER=0
GOALS=0
RED=0
declare -a NAMES=()
for e in "$W"/beispiele/*.gab "$W"/messung/*/*.gab; do
    if ! out="$("$GABBRO" pflichten --lean "$e" 2> /dev/null)"; then
        NO_REGISTER=$((NO_REGISTER + 1))
        continue
    fi
    name="$(printf '%s' "$out" | sed -n 's/^namespace GabbroDuty\.\(.*\)$/\1/p')"
    if [ -z "$name" ]; then
        echo "== LEAN PROOF: ${e#"$W"/} yields no module =="
        exit 1
    fi
    # **Two units with the same stem overwrote each other silently**, and the second count
    # would then be one nobody built. Same trap as in the Isabelle guardian.
    if [ -e "$TMP/$name.lean" ]; then
        echo "== LEAN PROOF: two units are both called $name =="
        exit 1
    fi
    printf '%s\n' "$out" > "$TMP/$name.lean"
    GOALS=$((GOALS + $(grep -c '^theorem duty_' "$TMP/$name.lean" || true)))
    UNITS=$((UNITS + 1))
    NAMES+=("$name")
done

# **Zero theorems over the whole corpus is a RED, not a pass.** A collection of modules
# without a single theorem builds green and measures nothing -- exactly the class W1 stands
# against: empty and passed look the same.
if [ "$GOALS" -eq 0 ]; then
    echo "== LEAN PROOF: $UNITS modules, NOT ONE theorem -- nothing measured =="
    echo "  Rule A demands that at least one GENERATED obligation really goes through."
    exit 1
fi

echo
echo "   $UNITS units -> $UNITS modules, $GOALS theorem(s) ($NO_REGISTER without a register)"
echo "   \$ LEAN_PATH=$LP lean <module>.lean   (per unit)"
for name in "${NAMES[@]}"; do
    RC=0
    run_lean "$TMP/$name.lean" || RC=$?
    if [ "$RC" -eq 2 ]; then
        echo "   DEADLINE  $name -- $DEADLINE s exceeded, NOTHING measured"
        RED=$((RED + 1))
    elif [ "$RC" -ne 0 ]; then
        echo "   RED    $name"
        sed -n '1,12p' "$TMP/$name.lean.log" | sed 's/^/          /'
        RED=$((RED + 1))
    fi
done

if [ "$RED" -ne 0 ]; then
    echo
    echo "== LEAN PROOF: RED -- $RED module(s) do not go through =="
    echo "  And that is the right colour: the emitter refuses no obligation it cannot prove"
    echo "  -- it states it. A goal that falls is a finding, not a fault of this guardian."
    exit 1
fi

echo
echo "== LEAN PROOF: $GOALS generated obligation(s) in $UNITS modules, LEAN GREEN =="
echo "   And what that does NOT mean: that the register is covered. It means two things --"
echo "   that every generated module IS valid Lean, including the one that consists purely"
echo "   of named refusals, and that the obligations standing CLOSED hold. How many those"
echo "   are and how many are not is what \`./instrumente/zaehle-lean.py\` says."
