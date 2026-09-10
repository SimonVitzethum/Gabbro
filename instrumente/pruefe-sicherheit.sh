#!/usr/bin/env bash
# The safety-theorem guardian (S5 of dokumente/PLAN-SICHERHEIT.md).
#
# It watches the three files of the safety theorem over the sequential core:
#
#     programmlogik/Gabbro/Sicherheit.lean              the sentence, the speech tests
#     programmlogik/Gabbro/Sicherheit/Ausdruck.lean     the expression half
#     programmlogik/Gabbro/Sicherheit/Anweisung.lean    the statement half
#
# WHAT IT MEASURES, in order:
#
#   1. The eight speech tests are PRESENT in `Sicherheit.lean`. They are eight
#      `example ... := by decide` lines: a refused denominator, the stuck model
#      behind it, an accepted division, a range through addition, an accepted
#      and a refused bit operation, a refused and an accepted index. A deleted
#      test still builds green and measures nothing, so presence is counted.
#   2. No `sorry` TERM stands in any of the three files. The count is over code,
#      not over text: the head file names the word `sorry` once in its own
#      header comment, and a plain `grep -c sorry` would read that word as a
#      debt. Comments (`--` to end of line, nested `/- ... -/` blocks) are
#      stripped before counting.
#   3. `lake build` in `programmlogik/` goes through. That run elaborates the
#      eight speech tests as well, so a green build means every `by decide`
#      closed. A model that does not build says nothing about the safety
#      claim, so a red build is an ABORT, not a finding.
#   4. The `#print axioms` lines the build prints name no `sorryAx` and nothing
#      outside `propext`, `Classical.choice`, `Quot.sound`. A missing axiom
#      report is an ABORT: a silent build is not evidence.
#   5. The finding ratchet: the head file names six findings (`Fund 1` to
#      `Fund 6`). That count may FALL -- a resolved finding is progress -- but
#      it must not RISE without a matching change in this guardian. A seventh
#      finding nobody booked here is a RED.
#
# EXIT CODES, the convention of this folder:
#
#     0  green -- measured, nothing found
#     1  RED -- measured, and the tree has to change
#     2  ABORTED -- NOTHING was measured (tool missing, file missing, model
#        red, evidence absent, guardian blind)
set -euo pipefail

# Whoever leaves mid-run says WHERE -- the shared form, out of `abschnitt.sh`.
. "$(dirname "$0")/abschnitt.sh"

# LC_ALL=C, and it is not a nicety. Foreign tools report in the user's locale,
# and a `grep` written against the English wording then matches nothing.
export LC_ALL=C

W="$(cd "$(dirname "$0")/.." && pwd)"
TMP="$(mktemp -d)"
trap 'abschnitt_ende; rm -rf "$TMP"' EXIT

LAKE="${LAKE:-$HOME/.elan/bin/lake}"
MODEL="${MODEL:-$W/programmlogik}"
DEADLINE="${DEADLINE:-600}"

# The head file carries the sentence, the speech tests and the findings; the
# other two carry the two halves of the proof.
HEAD="$MODEL/Gabbro/Sicherheit.lean"
AUSDRUCK="$MODEL/Gabbro/Sicherheit/Ausdruck.lean"
ANWEISUNG="$MODEL/Gabbro/Sicherheit/Anweisung.lean"

# Eight speech tests: counted, not believed. See the header above for the list.
SPEECH_TESTS=8
# Six findings: may fall when one is resolved, never rise silently.
RATCHET_FUNDE=6

if [ ! -x "$LAKE" ]; then
    stufe "SAFETY: NO LAKE at $LAKE -- NOTHING measured"
    echo "  A missing tool is not a passed test. Lake runs where it is installed;"
    echo "  until it runs here, this guardian reports an abort, not a pass."
    exit 2
fi
for f in "$HEAD" "$AUSDRUCK" "$ANWEISUNG"; do
    if [ ! -f "$f" ]; then
        stufe "SAFETY: ABORTED -- $f is missing, NOTHING measured"
        echo "  Over an empty population every count below reads zero, and zero"
        echo "  would look like a clean theorem. It is not; it is no theorem at all."
        exit 2
    fi
done

# --- 1. The speech tests are present -----------------------------------------
stufe "Speech tests present"
N_TESTS="$(grep -c '^example' "$HEAD" || true)"
echo "  $N_TESTS speech tests in Gabbro/Sicherheit.lean (expected $SPEECH_TESTS)"
if [ "$N_TESTS" -ne "$SPEECH_TESTS" ]; then
    stufe "SAFETY: ABORTED -- $N_TESTS speech tests, expected $SPEECH_TESTS"
    echo "  This guardian cannot see what is no longer there. Restore the tests,"
    echo "  or change the expectation here with the reason beside it."
    exit 2
fi

# --- 2. No sorry term ---------------------------------------------------------
# Comments are stripped first: the head file uses the WORD once in its own
# header, and that word is not a debt. What is counted is the term.
stufe "No sorry term"
SORRY_TOTAL=0
for f in "$HEAD" "$AUSDRUCK" "$ANWEISUNG"; do
    N_SORRY="$(python3 - "$f" <<'PY'
import re, sys
src = open(sys.argv[1], encoding='utf-8').read()
out = []
i, n, depth = 0, len(src), 0
while i < n:
    if depth == 0 and src.startswith('--', i):
        j = src.find('\n', i)
        i = n if j < 0 else j
    elif src.startswith('/-', i):
        depth += 1
        i += 2
    elif depth > 0 and src.startswith('-/', i):
        depth -= 1
        i += 2
    elif depth == 0:
        out.append(src[i])
        i += 1
    else:
        i += 1
code = ''.join(out)
print(len(re.findall(r'(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])', code)))
PY
)"
    echo "  ${f#"$MODEL"/}: $N_SORRY"
    SORRY_TOTAL=$((SORRY_TOTAL + N_SORRY))
done
if [ "$SORRY_TOTAL" -ne 0 ]; then
    stufe "SAFETY: RED -- $SORRY_TOTAL sorry term(s) in the safety theorem"
    echo "  A sorry is a hole with a name. Close it, or name beside it why the"
    echo "  theorem may stand open."
    exit 1
fi

# --- 3. The model builds -------------------------------------------------------
# The build elaborates the eight speech tests too: every `by decide` either
# closes here or the build fails. So from here on, present means proved.
stufe "Building the model"
if ! (cd "$MODEL" && timeout "$DEADLINE" "$LAKE" build > "$TMP/lake.log" 2>&1); then
    cat "$TMP/lake.log"
    stufe "SAFETY: ABORTED -- the model does not build, NOTHING measured"
    echo "  A model that does not build says nothing about the safety claim."
    echo "  The fault may sit anywhere upstream; it is not a finding of this guardian."
    exit 2
fi
echo "  lake build green"

# --- 4. The axioms --------------------------------------------------------------
# The four `#print axioms` lines of the head file print into the build log.
# Two ways to go blind here: the lines are missing (a silent build is not
# evidence), or a theorem leans on something it must not lean on.
stufe "Axioms"
if grep -q 'sorryAx' "$TMP/lake.log"; then
    grep -n 'sorryAx' "$TMP/lake.log" | head -8 | sed 's/^/  /'
    stufe "SAFETY: RED -- a theorem depends on sorryAx"
    echo "  That is the text-level sorry from step 2, arrived through the back"
    echo "  door: an axiom the prover owes, not one it proved."
    exit 1
fi
for t in schluss_sicher pruefe_sicher exec_sicher logik_grundfaelle; do
    if ! grep -q "$t.*depends on axioms" "$TMP/lake.log"; then
        stufe "SAFETY: ABORTED -- no axiom report for $t in the build log"
        echo "  The build went through without saying what the theorem rests on."
        echo "  Without that line there is no evidence, only an exit code."
        exit 2
    fi
done
UNEXPECTED="$(grep 'depends on axioms' "$TMP/lake.log" \
    | sed -E 's/.*depends on axioms: \[(.*)\].*/\1/' \
    | tr ',' '\n' | sed -e 's/^ *//' -e 's/ *$//' \
    | grep -v '^$' | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)"
if [ -n "$UNEXPECTED" ]; then
    printf '%s\n' "$UNEXPECTED" | sed 's/^/  unexpected axiom: /'
    stufe "SAFETY: RED -- a theorem rests on more than the three allowed axioms"
    echo "  Allowed: propext, Classical.choice, Quot.sound. Anything else is a"
    echo "  new foundation, and it needs a sentence beside it, not silence."
    exit 1
fi
echo "  four axiom reports, nothing outside propext, Classical.choice, Quot.sound"

# --- 5. The finding ratchet -------------------------------------------------------
# Findings are booked in the head file and counted here. Resolving one lowers
# the count and stays green; adding one without booking it here is a RED, and
# the fix is a line in this guardian, not in the theorem.
stufe "Finding ratchet"
N_FUNDE="$(grep -oE 'Fund [0-9]+' "$HEAD" | sort -u | wc -l)"
echo "  $N_FUNDE findings named in Gabbro/Sicherheit.lean (ratchet: $RATCHET_FUNDE)"
if [ "$N_FUNDE" -gt "$RATCHET_FUNDE" ]; then
    grep -oE 'Fund [0-9]+' "$HEAD" | sort -u | sed 's/^/  /'
    stufe "SAFETY: RED -- $N_FUNDE findings, ratchet stands at $RATCHET_FUNDE"
    echo "  A new finding is news, not a failure -- but it belongs in this"
    echo "  guardian beside the count, or the next one passes in silence too."
    exit 1
fi

# --- 6. The one named axiom outside the safety theorem ---------------------------
# `grammatik/Grammatik/Geraet.lean` carries exactly one `axiom` line: the DMA
# content assumption `dma_inhalt`, named per window, never derived (2026-09-10,
# R3 of the design review). This step teaches the ratchet that line: a SECOND
# axiom anywhere in the grammar is a RED, and the fix is a sentence beside
# it, not silence. If the line is ever discharged, this exception sits unused
# -- cleanup may remove it, nothing breaks. (Text-level check, like step 2:
# the build log only reports what `#print axioms` lines ask it to report,
# and the grammar head file asks for none.)
stufe "Named axiom"
AXIOMDATEIEN="$(grep -rln '^axiom ' "$W"/grammatik/Grammatik/*.lean 2>/dev/null || true)"
if [ -z "$AXIOMDATEIEN" ]; then
    echo "  no axiom line in grammatik/Grammatik -- the exception sits unused"
else
    echo "$AXIOMDATEIEN" | sed 's/^/  /'
fi
AXIOMFREMD="$(grep -rh '^axiom ' "$W"/grammatik/Grammatik/*.lean 2>/dev/null \
    | grep -v '^axiom dma_inhalt ' || true)"
if [ -n "$AXIOMFREMD" ]; then
    printf '%s\n' "$AXIOMFREMD" | sed 's/^/  foreign axiom: /'
    stufe "SAFETY: RED -- an axiom beside the named dma_inhalt stands in the grammar"
    echo "  Allowed: exactly the dma_inhalt line. Anything else is a new"
    echo "  foundation, and it needs a sentence beside it, not silence."
    exit 1
fi
echo "  nothing outside the named dma_inhalt line"

# From here on nothing more is measured -- what follows is the verdict over
# what the steps above ran. Its non-zero exits above are complete answers,
# not cuts.
abschnitt_fertig
stufe "SAFETY: GREEN -- 0 sorry, 8 speech tests proved, 4 axiom reports clean, $N_FUNDE findings booked"
echo "  And what that does NOT mean: that the sentence covers the language. It"
echo "  covers the sequential core under named premises; the alias, the memory"
echo "  model, termination, the axiom layer, foreign bodies and the emitter"
echo "  stand outside it, each with its own sentence in PLAN-SICHERHEIT.md."
