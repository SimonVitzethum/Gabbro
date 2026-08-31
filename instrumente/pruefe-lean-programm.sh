#!/usr/bin/env bash
# **Rule A for the PROGRAM EXPORT: can a HAND-WRITTEN Lean specification be held against a
# Gabbro program that spans several files?**
#
# `gabbro lean a.gab b.gab` joins the files into one program and writes it as a Lean 4
# module -- bodies, preconditions, the shape of every declared place. **It writes no
# specification.** What is to hold is said in Lean, by a person, in a file this emitter never
# sees. This guardian drives the whole way:
#
#     a.gab b.gab  ->  gabbro lean  ->  GabbroProgram.lean  ->  lean Spec.lean  ->  green
#
# **And it drives it in BOTH directions.** A specification that holds must go through, and
# three that do not must fall. *A guardian that has only ever been seen say yes is an
# ornament* (R11).
#
# ## The third check, and it is the one this artefact needs
#
# A specification names a place by STRING. A typo there is a specification about a place that
# does not exist -- and a theorem about a place nothing writes is not false, it is
# unprovable for the wrong reason. So every `.slot "X" _ "y"` a specification mentions is
# held against `GabbroProgram.places`, which the export carries for exactly this.
#
# **What that does NOT catch, and it is named rather than hidden:** a typo from one REAL
# field to another. `menge` where `sperrig` was meant proves a true statement about the wrong
# place, and no dictionary can see that. *The check bounds the hazard; it does not remove it.*
#
# **W1: a skipped run is not a passed one.** With no Lean this guardian turns red.
set -euo pipefail
export LC_ALL=C

W="$(cd "$(dirname "$0")/.." && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

GABBRO="$W/target/debug/gabbro"
LEANBIN="${LEANBIN:-$HOME/.elan/bin/lean}"
LAKE="${LAKE:-$HOME/.elan/bin/lake}"
MODEL="${MODEL:-$W/programmlogik}"
DEADLINE=180

if [ ! -x "$GABBRO" ]; then
    echo "== LEAN PROGRAM: NO GABBRO -- it is built on ki-pc-fisch-101 (CLAUDE.md) =="
    exit 2
fi
if [ ! -x "$LEANBIN" ] || [ ! -x "$LAKE" ]; then
    echo "== LEAN PROGRAM: NO LEAN at $LEANBIN -- NOTHING measured =="
    echo "  A missing tool is not a passed test (W1)."
    exit 2
fi

echo "== Building the meaning of a body =="
if ! (cd "$MODEL" && timeout "$DEADLINE" "$LAKE" build Gabbro.Body > "$TMP/lake.log" 2>&1); then
    cat "$TMP/lake.log"
    echo "== LEAN PROGRAM: Gabbro.Body does not build -- the MODEL is red =="
    exit 2
fi
LP="$MODEL/.lake/build/lib/lean"
echo "   Gabbro.Body built"

# ---- the export ------------------------------------------------------------------------
B="$MODEL/beispiel"
echo
echo "== Exporting the program =="
echo "   \$ gabbro lean beispiel/lager.gab beispiel/betrieb.gab"
if ! "$GABBRO" lean "$B/lager.gab" "$B/betrieb.gab" > "$TMP/GabbroProgram.lean" 2> "$TMP/err"; then
    cat "$TMP/err"
    echo "== LEAN PROGRAM: the export failed =="
    exit 1
fi
KOPF="$(grep -m1 '@program 1' "$TMP/GabbroProgram.lean" | sed 's/^ *//')"
echo "   $KOPF"

# **The balance has to add up**, the same rule the obligation channel follows: an emitter
# that swallows a routine looks exactly like one that refuses it, and only the second has
# measured anything.
R=$(printf '%s' "$KOPF" | sed -n 's/.*routines \([0-9]*\).*/\1/p')
BD=$(printf '%s' "$KOPF" | sed -n 's/.*bodies \([0-9]*\).*/\1/p')
RF=$(printf '%s' "$KOPF" | sed -n 's/.*refused \([0-9]*\).*/\1/p')
if [ "$((BD + RF))" -ne "$R" ]; then
    echo "== LEAN PROGRAM: $BD + $RF != $R -- the balance of the export does not add up =="
    exit 1
fi
if [ "$BD" -eq 0 ]; then
    echo "== LEAN PROGRAM: not one body exported -- nothing measured =="
    echo "  An export without a body builds green and says nothing (W1)."
    exit 2
fi

if ! (cd "$TMP" && LEAN_PATH="$LP" timeout "$DEADLINE" "$LEANBIN" \
        -o GabbroProgram.olean GabbroProgram.lean > "$TMP/prog.log" 2>&1); then
    cat "$TMP/prog.log"
    echo "== LEAN PROGRAM: the exported program is not valid Lean =="
    exit 1
fi
echo "   GabbroProgram compiled"

# ---- the place dictionary ----------------------------------------------------------------
# Every `.slot "carrier" … "field"` a specification names, held against what the program
# declares.
# **Both tables carry places, and a specification may name either.** `places` holds the slot
# fields of the tables, `fields` the fields of records and `format`s -- and a check that
# looked at only one would let a typo in the other through in silence.
places_of() {
    sed -n '/^def places/,/^  \]/p;/^def fields/,/^  \]/p' "$TMP/GabbroProgram.lean" \
        | grep -oE '\("[^"]+", "[^"]+"' | tr -d '(",' | awk '{print $1"."$2}' | sort -u
}
spec_places() {
    { grep -oE '\.slot "[^"]+" [A-Za-z_0-9]+ "[^"]+"' "$1" \
        | sed -E 's/\.slot "([^"]+)" [A-Za-z_0-9]+ "([^"]+)"/\1.\2/'
      grep -oE '\.field "[^"]+" "[^"]+"' "$1" \
        | sed -E 's/\.field "([^"]+)" "([^"]+)"/\1.\2/'
    } | sort -u
}
DICT="$TMP/dict"; places_of > "$DICT"
echo "   $(wc -l < "$DICT") declared places"

pruefe_orte() {
    local f="$1" fehlend
    fehlend="$(comm -23 <(spec_places "$f") "$DICT" || true)"
    if [ -n "$fehlend" ]; then
        printf '%s\n' "$fehlend" | sed 's/^/     NOT DECLARED  /'
        return 1
    fi
    return 0
}

run_lean() {
    local f="$1" rc=0
    (cd "$TMP" && LEAN_PATH="$LP:$TMP" timeout "$DEADLINE" "$LEANBIN" "$(basename "$f")" \
        > "$f.log" 2>&1) || rc=$?
    if [ "$rc" -eq 124 ]; then return 2; fi
    if grep -q 'error:' "$f.log"; then return 1; fi
    if [ "$rc" -ne 0 ]; then return 1; fi
    return 0
}

# ---- the speech test, in both directions ------------------------------------------------
echo
echo "== Speech test =="
cp "$B/Spec.lean" "$B/SpecGift.lean" "$TMP/"

GOOD=0
if pruefe_orte "$TMP/Spec.lean" && run_lean "$TMP/Spec.lean"; then GOOD=1; fi
SAETZE=$(grep -c '^theorem ' "$TMP/Spec.lean" || true)
echo "  a hand-written specification goes through: $([ $GOOD -eq 1 ] && echo "yes ($SAETZE theorems)" || echo NO)"
[ $GOOD -eq 1 ] || sed -n '1,12p' "$TMP/Spec.lean.log" | sed 's/^/     /'

POISON=0
if ! run_lean "$TMP/SpecGift.lean"; then POISON=1; fi
GIFTE=$(grep -c '^theorem ' "$TMP/SpecGift.lean" || true)
FALLEN=$(grep -c 'error:' "$TMP/SpecGift.lean.log" || true)
echo "  every poisoned one falls:                  $([ "$FALLEN" -ge "$GIFTE" ] && echo "yes ($FALLEN of $GIFTE)" || echo "NO ($FALLEN of $GIFTE)")"

# The dictionary must name the invented field of poison 3 -- **and say the true thing about
# it.** Falling with "unsolved goals" is the right colour for the wrong reason: it reads like
# a fault in the program.
ORTE=0
if ! pruefe_orte "$TMP/SpecGift.lean" > "$TMP/orte" 2>&1; then ORTE=1; fi
echo "  a place that is not declared is named:     $([ $ORTE -eq 1 ] && echo yes || echo NO)"
[ $ORTE -eq 1 ] && sed 's/^/  /' "$TMP/orte"

if [ $GOOD -ne 1 ] || [ "$FALLEN" -lt "$GIFTE" ] || [ $ORTE -ne 1 ]; then
    echo
    echo "== LEAN PROGRAM: this guardian measures nothing =="
    exit 2
fi

echo
echo "== LEAN PROGRAM: $BD bodies from 2 files, $SAETZE hand-written specifications, LEAN GREEN =="
echo "   And what that does NOT mean: that the specification says what was meant. A typo"
echo "   from one DECLARED field to another proves a true statement about the wrong place,"
echo "   and no dictionary sees that. The check bounds the hazard; it does not remove it."
