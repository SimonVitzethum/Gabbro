#!/usr/bin/env bash
# **Regel A fuer den RUMPFKANAL: geht eine erzeugte Pflicht ueber einen RUMPF wirklich durch?**
#
# `gabbro pflichten --lean` schreibt das Pflichtenregister einer Einheit als Lean-4-Modul --
# den Rumpf als Datum von `Passlogik.Rumpf`, die Nachbedingung als Ausdruck, das Ziel als
# Satz. *Eine erzeugte Pflicht, die kein Beweiser je gelesen hat, ist wieder nur eine Zeile
# in einem Bericht -- bloss in einer anderen Datei.*
#
#     .gab  ->  gabbro pflichten --lean  ->  .lean  ->  lean  ->  gruen
#
# **Er baut JEDE Einheit, die ein Register liefert, nicht nur die mit einem Ziel.** Das sind
# zwei verschiedene Fragen, und erst beide zusammen heissen etwas:
#
#   1. ist gueltiges Lean, was der Erzeuger schreibt -- auch dort, wo es nur aus benannten
#      Absagen besteht? *Ein Modul, das nie ein Beweiser gelesen hat, ist eine Textdatei.*
#   2. geht mindestens eine ERZEUGTE Pflicht durch? Das ist Regel A, und sie wird als Zahl
#      geprueft: null Saetze ueber dem ganzen Korpus faerbt diesen Waechter rot.
#
# **Nichts davon wird eingecheckt.** Die Module entstehen bei jedem Lauf neu; ein
# mitgefuehrtes Erzeugnis waere das zweite Register ueber derselben Sache.
#
# **W1: ein uebersprungener Lauf ist kein bestandener.** Ohne Lean faerbt sich dieser
# Waechter rot, statt sich fuer bestanden zu erklaeren. Und die Frist wird von Hand
# behandelt: `set -e` auf Rueckgabe 124 beendete dieses Skript STILL.
set -euo pipefail

# Fremde Werkzeuge melden im Gebietsschema des Benutzers -- dieselbe Klasse wie `W16`.
export LC_ALL=C

W="$(cd "$(dirname "$0")/.." && pwd)"
ARB="$(mktemp -d)"
trap 'rm -rf "$ARB"' EXIT

GABBRO="$W/target/debug/gabbro"
LEANBIN="${LEANBIN:-$HOME/.elan/bin/lean}"
LAKE="${LAKE:-$HOME/.elan/bin/lake}"
PASSLOGIK="${PASSLOGIK:-$W/passlogik}"
FRIST=120

if [ ! -x "$GABBRO" ]; then
    echo "== LEAN-BEWEIS: KEIN GABBRO -- gebaut wird auf ki-pc-fisch-101 (CLAUDE.md) =="
    exit 1
fi
if [ ! -x "$LEANBIN" ] || [ ! -x "$LAKE" ]; then
    echo "== LEAN-BEWEIS: KEIN LEAN unter $LEANBIN -- NICHTS gemessen =="
    echo "  Ein fehlendes Werkzeug ist kein bestandener Test (W1)."
    exit 1
fi

# **Die Bedeutung eines Rumpfes muss gebaut sein, bevor irgendein Ziel sie zitieren kann.**
echo "== Die Bedeutung eines Rumpfes bauen =="
if ! (cd "$PASSLOGIK" && timeout "$FRIST" "$LAKE" build Passlogik.Rumpf > "$ARB/lake.log" 2>&1); then
    cat "$ARB/lake.log"
    echo "== LEAN-BEWEIS: Passlogik.Rumpf baut nicht -- das MODELL ist rot, nicht das Erzeugnis =="
    exit 1
fi
LP="$PASSLOGIK/.lake/build/lib/lean"
echo "   Passlogik.Rumpf gebaut"

# Ein Lean-Lauf ueber einer Datei. 0 gruen, 1 rot, 2 Frist -- und die Frist ist ihre eigene
# Antwort, weder rot noch gruen. **Warnungen sind kein Rot**: eine Voraussetzung, die der
# Beweis nicht braucht, ist eine Voraussetzung zu viel und ein Befund, kein Fehler.
lauf() {
    local f="$1" rc=0
    LEAN_PATH="$LP" timeout "$FRIST" "$LEANBIN" "$f" > "$f.log" 2>&1 || rc=$?
    if [ "$rc" -eq 124 ]; then return 2; fi
    if grep -q '^.*error:' "$f.log"; then return 1; fi
    if [ "$rc" -ne 0 ]; then return 1; fi
    return 0
}

# **Die Sprechprobe, in beide Richtungen** (R11). *Ein Waechter, der beim ersten Versuch
# gruen ist, ohne dass jemand ihn hat fallen sehen, ist eine Verzierung.*
#
# Und sie steht ueber DEMSELBEN MODELL wie das Erzeugnis, nicht ueber `2 + 2 = 4`: derselbe
# Rumpf schreibt `false` in ein Feld, und einmal behauptet der Satz danach `nicht f` und
# einmal `f`. **Nur so misst die Probe den Kanal und nicht Lean.**
sprechprobe() {
    local gut=0 gift=0 fall d schluss
    for fall in gut gift; do
        d="$ARB/probe-$fall.lean"
        if [ "$fall" = gut ]; then
            schluss='(.un .nicht (.platz "T" (.lit (.z 0)) "f"))'
        else
            schluss='(.platz "T" (.lit (.z 0)) "f")'
        fi
        cat > "$d" <<LEAN
import Passlogik.Rumpf
set_option autoImplicit false
open Passlogik.Rumpf
def rumpf : List Anweisung := [(.zuw "T" (.lit (.z 0)) "f" (.lit (.b false)))]
def nach : Ausdruck := $schluss
theorem probe (l : Lage)
    : ∃ l', endLage (fuehre rumpf l) = some l' ∧ werte l' nach = some (.b true) := by
  simp [rumpf, nach, fuehre, schritt, werte, unwert, binwert, endLage, setze, binde]
LEAN
        if lauf "$d"; then [ "$fall" = gut ] && gut=1; else [ "$fall" = gift ] && gift=1; fi
    done
    echo "== Sprechprobe =="
    echo "  wahrer Satz geht durch:   $([ $gut  -eq 1 ] && echo ja || echo NEIN)"
    echo "  falscher Satz faellt:     $([ $gift -eq 1 ] && echo ja || echo NEIN)"
    [ $gut -eq 1 ] && [ $gift -eq 1 ]
}

if ! sprechprobe; then
    echo "== LEAN-BEWEIS: der Waechter misst nicht -- Lean antwortet nicht wie erwartet =="
    exit 1
fi

EINHEITEN=0
OHNE=0
ZIELE=0
ROT=0
declare -a NAMEN=()
for e in "$W"/beispiele/*.gab "$W"/messung/*/*.gab; do
    if ! out="$("$GABBRO" pflichten --lean "$e" 2> /dev/null)"; then
        OHNE=$((OHNE + 1))
        continue
    fi
    name="$(printf '%s' "$out" | sed -n 's/^namespace GabbroPflicht\.\(.*\)$/\1/p')"
    if [ -z "$name" ]; then
        echo "== LEAN-BEWEIS: ${e#"$W"/} ergibt kein Modul =="
        exit 1
    fi
    # **Zwei Einheiten mit demselben Stamm ueberschrieben einander lautlos**, und die zweite
    # Zahl waere dann eine, die niemand gebaut hat. Dieselbe Falle wie im Isabelle-Waechter.
    if [ -e "$ARB/$name.lean" ]; then
        echo "== LEAN-BEWEIS: zwei Einheiten heissen beide $name =="
        exit 1
    fi
    printf '%s\n' "$out" > "$ARB/$name.lean"
    ZIELE=$((ZIELE + $(grep -c '^theorem duty_' "$ARB/$name.lean" || true)))
    EINHEITEN=$((EINHEITEN + 1))
    NAMEN+=("$name")
done

if [ "$ZIELE" -eq 0 ]; then
    echo "== LEAN-BEWEIS: $EINHEITEN Module, KEIN einziger Satz -- nichts gemessen =="
    echo "  Regel A verlangt, dass mindestens eine ERZEUGTE Pflicht wirklich durchgeht."
    exit 1
fi

echo
echo "   $EINHEITEN Einheiten -> $EINHEITEN Module, $ZIELE Satz/Saetze ($OHNE ohne Register)"
echo "   \$ LEAN_PATH=$LP lean <modul>.lean   (je Einheit)"
for name in "${NAMEN[@]}"; do
    RC=0
    lauf "$ARB/$name.lean" || RC=$?
    if [ "$RC" -eq 2 ]; then
        echo "   FRIST  $name -- $FRIST s ueberschritten, NICHTS gemessen"
        ROT=$((ROT + 1))
    elif [ "$RC" -ne 0 ]; then
        echo "   ROT    $name"
        sed -n '1,12p' "$ARB/$name.lean.log" | sed 's/^/          /'
        ROT=$((ROT + 1))
    fi
done

if [ "$ROT" -ne 0 ]; then
    echo
    echo "== LEAN-BEWEIS: ROT -- $ROT Modul(e) gehen nicht durch =="
    echo "  Und das ist die richtige Farbe: der Erzeuger sagt keine Pflicht ab, die er"
    echo "  nicht beweisen kann -- er stellt sie hin. Ein Ziel, das faellt, ist ein Befund."
    exit 1
fi

echo
echo "== LEAN-BEWEIS: $ZIELE erzeugte Pflicht(en) in $EINHEITEN Modulen, LEAN GRUEN =="
echo "   Und was das NICHT heisst: dass der Bestand gedeckt ist. Es heisst zweierlei --"
echo "   dass jedes erzeugte Modul gueltiges Lean IST, auch das, das nur aus benannten"
echo "   Absagen besteht, und dass die Pflichten, die GESCHLOSSEN dastehen, halten. Wie"
echo "   viele das sind und wie viele nicht, sagt \`./instrumente/zaehle-lean.py\`."
