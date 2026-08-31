#!/usr/bin/env bash
# **Rule A for P6: does a GENERATED refinement obligation really go through?**
#
# `gabbro pflichten --isabelle` writes a unit's obligation register as a theory. *A generated
# obligation no prover has ever read is again just a line in a report -- only in a different
# file.* This guardian lets Isabelle read it.
#
#     .gab  ->  gabbro pflichten --isabelle  ->  .thy  ->  isabelle build  ->  green
#
# **It builds EVERY unit that yields a register, not only the ones that carry a goal.** Two
# different things are being asked, and only both together mean anything:
#
#   1. is what the emitter writes VALID Isabelle at all -- also where it consists purely of
#      named refusals? *A theory nobody ever fed to the prover is a text file.*
#   2. does at least one GENERATED obligation go through? That is Rule A, and it is checked
#      as a count: zero lemmas over the whole corpus turns this guardian red.
#
# **Nothing here is checked in.** The theories are written afresh on every run; a carried
# artefact would be the second register over one thing, and that is what `abi.rs` stands
# against. The price is that this run needs Isabelle -- an honest price, because without
# Isabelle nothing has been measured.
#
# **W1: a skipped run is not a passed one.** With no Isabelle this guardian turns red rather
# than declaring itself passed. And the deadline is handled by hand: `set -e` on return code
# 124 would end this script SILENTLY -- the exact trap `pruefe-emission.sh` fell into on
# 2026-08-20, where the deadline was there and the requirement was not met.
set -euo pipefail

# **Whoever leaves mid-run says WHERE** -- the shared form, out of `abschnitt.sh`.
. "$(dirname "$0")/abschnitt.sh"

# **`LC_ALL=C` -- und das ist kein Schoenheitsfehler.** Fremde Werkzeuge melden im
# Gebietsschema des Benutzers: unter `de_DE.UTF-8` sagt der Binder `Mehrfachdefinition von`
# statt `multiple definition`, und ein `grep -q` darauf trifft nicht. Dieselbe Klasse wie
# `W16` -- ein Werkzeug, das sein eigenes Gebietsschema misst und dabei plausibel aussieht.
export LC_ALL=C

W="$(cd "$(dirname "$0")/.." && pwd)"
ARB="$(mktemp -d)"
trap 'abschnitt_ende; rm -rf "$ARB"' EXIT

GABBRO="$W/target/debug/gabbro"
ISABELLE="${ISABELLE:-$HOME/Isabelle2025-2/bin/isabelle}"
FRIST=900

# One Isabelle session over a directory. Returns 0 green, 1 red, 2 the deadline -- and the
# deadline is its own answer, not a red and not a green.
baue() {
    local d="$1" rc=0
    timeout "$FRIST" "$ISABELLE" build -D "$d" -o threads=12 > "$d/log" 2>&1 || rc=$?
    if [ "$rc" -eq 124 ]; then return 2; fi
    if [ "$rc" -ne 0 ]; then return 1; fi
    return 0
}

if [ ! -x "$GABBRO" ]; then
    stufe "P6-BEWEIS: KEIN GABBRO -- gebaut wird auf ki-pc-fisch-101 (CLAUDE.md)"
    exit 2
fi
if [ ! -x "$ISABELLE" ]; then
    stufe "P6-BEWEIS: KEIN ISABELLE unter $ISABELLE -- NICHTS gemessen"
    echo "  Ein fehlendes Werkzeug ist kein bestandener Test (W1)."
    exit 2
fi

# **Die Sprechprobe, in beide Richtungen** (R11). *Ein Waechter, der beim ersten Versuch
# gruen ist, ohne dass jemand ihn hat fallen sehen, ist eine Verzierung.* Zwei winzige
# Theorien in derselben Bauart wie das Erzeugnis: eine wahre und eine falsche.
sprechprobe() {
    local d gut=0 gift=0
    for fall in gut gift; do
        d="$ARB/probe-$fall"; mkdir -p "$d"
        if [ "$fall" = gut ]; then
            printf 'theory P6_Probe\n  imports Main\nbegin\nlemma p: "(7 :: int) < 4096"\n  by presburger\nend\n' > "$d/P6_Probe.thy"
        else
            printf 'theory P6_Probe\n  imports Main\nbegin\nlemma p: "(4096 :: int) < 7"\n  by presburger\nend\n' > "$d/P6_Probe.thy"
        fi
        printf 'session P6_Probe = HOL +\n  options [document = false]\n  theories\n    P6_Probe\n' > "$d/ROOT"
        if baue "$d"; then [ "$fall" = gut ] && gut=1; else [ "$fall" = gift ] && gift=1; fi
    done
    stufe "Sprechprobe"
    echo "  wahrer Satz geht durch:   $([ $gut  -eq 1 ] && echo ja || echo NEIN)"
    echo "  falscher Satz faellt:     $([ $gift -eq 1 ] && echo ja || echo NEIN)"
    [ $gut -eq 1 ] && [ $gift -eq 1 ]
}

if ! sprechprobe; then
    stufe "P6-BEWEIS: der Waechter misst nicht -- Isabelle antwortet nicht wie erwartet"
    exit 2
fi

BAU="$ARB/bau"; mkdir -p "$BAU"
EINHEITEN=0
OHNE=0
ZIELE=0
for e in "$W"/beispiele/*.gab "$W"/messung/*/*.gab; do
    # A unit with errors carries no register -- the same rule `gabbro pflichten` follows.
    if ! out="$("$GABBRO" pflichten --isabelle "$e" 2> /dev/null)"; then
        OHNE=$((OHNE + 1))
        continue
    fi
    name="$(printf '%s' "$out" | sed -n 's/^theory \(.*\)$/\1/p')"
    if [ -z "$name" ]; then
        stufe "P6-BEWEIS: ${e#"$W"/} ergibt keine Theorie"
        exit 1
    fi
    # **Zwei Einheiten mit demselben Stamm ueberschrieben einander lautlos**, und die
    # zweite Zahl waere dann eine, die niemand gebaut hat.
    if [ -e "$BAU/$name.thy" ]; then
        stufe "P6-BEWEIS: zwei Einheiten heissen beide $name -- eine haette die andere ueberschrieben"
        exit 1
    fi
    printf '%s\n' "$out" > "$BAU/$name.thy"
    ZIELE=$((ZIELE + $(grep -c '^lemma ' "$BAU/$name.thy" || true)))
    EINHEITEN=$((EINHEITEN + 1))
    echo "    $name" >> "$BAU/liste"
done

# **Null Saetze ueber dem ganzen Korpus ist ein ROT, kein Bestehen.** Eine Sammlung von
# Theorien ohne einen einzigen Satz baut gruen und misst nichts -- genau die Klasse, gegen
# die W1 steht: leer und bestanden sehen gleich aus.
if [ "$ZIELE" -eq 0 ]; then
    stufe "P6-BEWEIS: $EINHEITEN Theorien, KEIN einziger Satz -- nichts gemessen"
    echo "  Regel A verlangt, dass mindestens eine ERZEUGTE Pflicht wirklich durchgeht."
    exit 2
fi

{
    echo "session Gabbro_P6 = HOL +"
    echo "  options [document = false]"
    echo "  theories"
    cat "$BAU/liste"
} > "$BAU/ROOT"

echo
echo "   $EINHEITEN Einheiten -> $EINHEITEN Theorien, $ZIELE Satz/Saetze ($OHNE ohne Register)"
echo "   \$ isabelle build -D $BAU -o threads=12"
RC=0
baue "$BAU" || RC=$?
cat "$BAU/log"
# **From here on nothing more is measured** -- the build has run. What follows is the
# verdict over it, and its non-zero exits are complete answers rather than cuts.
abschnitt_fertig
if [ "$RC" -eq 2 ]; then
    echo
    stufe "P6-BEWEIS: FRIST $FRIST s UEBERSCHRITTEN -- NICHTS gemessen"
    echo "  Ein Haenger sieht aus wie „laeuft noch\", nicht wie ein Befund."
    exit 2
fi
if [ "$RC" -ne 0 ]; then
    echo
    stufe "P6-BEWEIS: ROT -- eine ERZEUGTE Pflicht geht nicht durch"
    echo "  Und das ist die richtige Farbe: der Erzeuger sagt keine Pflicht ab, die er"
    echo "  nicht beweisen kann -- er stellt sie hin. Ein Ziel, das faellt, ist ein"
    echo "  Befund, kein Fehler des Waechters."
    exit 1
fi

echo
stufe "P6-BEWEIS: $ZIELE erzeugte Pflicht(en) in $EINHEITEN Theorien, ISABELLE GRUEN"
echo "   Und was das NICHT heisst: dass der Bestand gedeckt ist. Es heisst zweierlei --"
echo "   dass jede erzeugte Theorie gueltiges Isabelle IST, auch die, die nur aus benannten"
echo "   Absagen besteht, und dass die Pflichten, die GESCHLOSSEN dastehen, halten. Wie"
echo "   viele das sind und wie viele nicht, sagt \`./instrumente/zaehle-p6.py\`."
