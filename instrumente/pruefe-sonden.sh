#!/usr/bin/env bash
# **Der Sondenlaeufer -- der ORT, an dem ein `falsifier` ein Programm werden kann.**
#
#     ./instrumente/pruefe-sonden.sh [--runden N]
#
# WOZU
# ----
# `messung/AXIOMSCHICHT.md` (2026-08-21) hat es gemessen und ausgeschrieben:
#
#   **27 Annahmen nennen eine Sonde, 26 verschiedene Namen -- und NULL davon existieren als
#   Programm.**
#
#   > Ein `falsifier sonde_xyz`, dessen Sonde nirgends existiert, ist eine Zusicherung ueber
#   > das AUSBLEIBEN einer Widerlegung -- dieselbe Klasse wie R15 und W10.
#
# Der Befund dort endete mit einem Satz, der kein Werkzeug hatte: *„es gibt im ganzen Ordner
# keinen Ort, an dem eine Sonde stuende, kein Verzeichnis, keinen Laeufer, keine Buchung ueber
# ihren Lauf."* **Dies ist der Ort.** `sonden/README.md` sagt, was dort stehen darf und was
# nicht.
#
# DER VERTRAG EINER SONDE -- und die dritte Stufe, die die GRAMMATIK nicht hat
# ---------------------------------------------------------------------------
#     0    nicht widerlegt in diesem Lauf   -- und das ist ALLES, was es heisst
#     1    WIDERLEGT, oder die Sonde hat sich selbst als blind erwiesen
#     77   hier nicht lauffaehig -- kein Geraet, kein Recht, ein Kern
#
# `SYNTAX.md`:1211 nennt genau diese Unterscheidung und sagt, dass die dritte Stufe
# grammatisch nicht existiert: *„falsified (probe ran and held), not falsifiable (with a
# reason), not run."* **Sie existiert jetzt als RUECKLAUFWERT**, und das ist der ganze
# Unterschied zwischen einer benannten und einer gelaufenen Sonde.
#
# EINE SONDE, DIE NICHT ROT WERDEN KANN, MISST NICHTS (R14)
# ---------------------------------------------------------
# Deshalb verlangt dieser Laeufer von jeder Sonde, dass sie ihre eigene EMPFINDLICHKEIT
# zeigt, und deshalb traegt er selbst eine Sprechprobe in beide Richtungen: drei erfundene
# Sonden, die 0, 1 und 77 liefern muessen. *Ein Laeufer, der eine widerlegende Sonde gruen
# buchte, waere schlimmer als gar keiner.*
#
# WAS DIESER LAEUFER NICHT TUT
# ----------------------------
# Er erzeugt keine Sonde aus einer `falsifier`-Zeile, und er prueft nicht, dass eine
# vorhandene Sonde die Annahme trifft, die sie im Namen fuehrt. *Was hier gemessen wird, ist
# DASS eine laeuft, nicht WORUEBER.* Die Zuordnung steht in der ersten Ausgabezeile jeder
# Sonde und wird von einem Menschen gelesen -- genau die Grobheit, die `H015` an der
# Gnadenfrist auch hat.
set -u

# **Whoever leaves mid-run says WHERE** -- the shared form, out of `abschnitt.sh`.
# **Armed HERE and not at the `mktemp` below**: the argument check exits above that line, and
# a notice that starts halfway down the file measures the second half. The `trap` further
# down replaces this one and calls `abschnitt_ende` itself.
. "$(dirname "$0")/abschnitt.sh"
trap abschnitt_ende EXIT

# **`LC_ALL=C` -- und das ist kein Schoenheitsfehler.** Fremde Werkzeuge melden im
# Gebietsschema des Benutzers: unter `de_DE.UTF-8` sagt der Binder `Mehrfachdefinition von`
# statt `multiple definition`, und ein `grep -q` darauf trifft nicht. Dieselbe Klasse wie
# `W16` -- ein Werkzeug, das sein eigenes Gebietsschema misst und dabei plausibel aussieht.
export LC_ALL=C

FRIST=120
RUNDEN=2000000
W="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CFLAGS=(-std=c11 -Wall -Wextra -Werror -O2 -pthread)

while [ $# -gt 0 ]; do
  case "$1" in
    --runden) RUNDEN="$2"; shift 2 ;;
    *) echo "unbekanntes Argument: $1" >&2; exit 2 ;;
  esac
done

TMP="$(mktemp -d)"
trap 'abschnitt_ende; rm -rf "$TMP"' EXIT

# ---------------------------------------------------------------------------------------
# Die Sprechprobe. **In beide Richtungen und in die dritte** -- an erfundenen Sonden, nicht
# an den eigenen. Eine Probe ueber den eigenen Dateien misst, wie gut sie zum Laeufer passen.
# ---------------------------------------------------------------------------------------
probe_bauen() {
  cat > "$TMP/p$1.c" <<EOF
#include <stdio.h>
int main(void){ printf("sonde erfunden$1 :: nichts\n"); return $1; }
EOF
  cc "${CFLAGS[@]}" -o "$TMP/p$1" "$TMP/p$1.c" 2>/dev/null || return 1
  timeout "$FRIST" "$TMP/p$1" >/dev/null 2>&1
  echo $?
}

stufe "Sprechprobe des Laeufers"
S0="$(probe_bauen 0)"; S1="$(probe_bauen 1)"; S77="$(probe_bauen 77)"
echo "  eine haltende Sonde  -> $S0   (erwartet 0)"
echo "  eine WIDERLEGENDE    -> $S1   (erwartet 1)"
echo "  eine nicht lauffaehige -> $S77  (erwartet 77)"
if [ "$S0" != "0" ] || [ "$S1" != "1" ] || [ "$S77" != "77" ]; then
  echo "  GESCHEITERT -- der Laeufer unterscheidet die drei Zustaende nicht."
  # 2, not 1: if the runner cannot tell hold from refuted, nothing below is a measurement.
  exit 2
fi
echo "  ok (alle drei Zustaende kommen an)"
echo

# ---------------------------------------------------------------------------------------
# Der Bestand: wieviele Sonden sind BENANNT, wieviele stehen hier als Programm?
# ---------------------------------------------------------------------------------------
BIN="$W/target/debug/gabbro"
BENANNT="nicht gezaehlt"
GESTRICHEN="nicht gezaehlt"
if [ -x "$BIN" ]; then
  # **Aus dem Manifest, nicht aus einem `grep`.** Drei der Sonden gehoeren zu Annahmen, die
  # `manifest.rs` ERZEUGT; im Quelltext steht ihre Zeile nirgends, und eine Textzaehlung
  # meldete deshalb 24 statt 26.
  MANIFEST="$(timeout "$FRIST" "$BIN" annahmen "$W"/beispiele/*.gab 2>/dev/null)"
  BENANNT="$(printf '%s' "$MANIFEST" | grep -o 'sonde_[a-zA-Z0-9_]*' | sort -u | wc -l)"
  # **Seit dem 2026-08-30 traegt das Manifest keinen Namen mehr, dessen Sonde nicht als
  # Programm steht** -- es streicht ihn und sagt in einer Zeile, wie viele es waren.
  #
  # *Ohne diese zwei Zeilen haette der Laeufer ab da `1 Sondennamen benannt` gemeldet und
  # damit ausgesehen, als sei die Anklage erledigt.* Sie ist es nicht: die Zahl ist nur
  # umgezogen, aus der Namensspalte in die Schlusszeile. **Ein Waechter, dem sein Gegenstand
  # unter der Hand wegzieht, misst still eine Null** -- dieselbe Klasse wie W16.
  GESTRICHEN="$(printf '%s' "$MANIFEST" | grep -oE '^-- [0-9]+ probe name' \
                | grep -oE '[0-9]+' | head -1)"
  [ -n "$GESTRICHEN" ] || GESTRICHEN=0
fi
DA=0
for f in "$W"/sonden/sonde_*.c; do [ -e "$f" ] && DA=$((DA+1)); done

# **`0 von 0 Sonden gelaufen` was a GREEN run until 2026-08-31** (measured over a tree with
# no `sonden/`). Not one assumption was put to the test, nothing was refuted, and this
# guardian exited 0 -- *a positive verdict about nothing*, and over exactly the population
# whose whole purpose is to be able to refute something (W1, W17).
if [ "$DA" -eq 0 ]; then
  echo "ABBRUCH: keine einzige Sonde unter sonden/ -- es wurde NICHTS gemessen."
  echo '  Eine Sonde, die es nicht gibt, widerlegt nichts -- und `0 von 0 gelaufen` ist'
  echo '  keine Deckung, sondern eine leere Grundgesamtheit.'
  exit 2
fi

stufe "Die Sonden dieses Ordners"
GELAUFEN=0
WIDERLEGT=0
UNGEBAUT=0
NICHT_LAUFFAEHIG=0
for f in "$W"/sonden/sonde_*.c; do
  [ -e "$f" ] || continue
  name="$(basename "$f" .c)"
  if ! cc "${CFLAGS[@]}" -o "$TMP/$name" "$f" 2>"$TMP/$name.err"; then
    echo "  BAUT NICHT  $name"
    sed 's/^/      /' "$TMP/$name.err" | head -20
    UNGEBAUT=$((UNGEBAUT+1))
    continue
  fi
  timeout "$FRIST" "$TMP/$name" "$RUNDEN" > "$TMP/$name.out" 2>&1
  rc=$?
  sed 's/^/      /' "$TMP/$name.out"
  case "$rc" in
    0)  echo "  HAELT       $name  (nicht widerlegt -- und das ist alles)"
        GELAUFEN=$((GELAUFEN+1)) ;;
    1)  echo "  WIDERLEGT   $name  -- oder die Sonde hat sich selbst als blind erwiesen"
        WIDERLEGT=$((WIDERLEGT+1)); GELAUFEN=$((GELAUFEN+1)) ;;
    77) echo "  NICHT HIER  $name  (kein Geraet, kein Recht, ein Kern)"
        NICHT_LAUFFAEHIG=$((NICHT_LAUFFAEHIG+1)) ;;
    124) echo "  HAENGT      $name  -- Frist $FRIST s ueberschritten"
        UNGEBAUT=$((UNGEBAUT+1)) ;;
    *)  echo "  FEHLAUFRUF  $name  -- Ruecklaufwert $rc liegt ausserhalb {0,1,77}"
        UNGEBAUT=$((UNGEBAUT+1)) ;;
  esac
  echo
done

# **From here on nothing more is measured** -- everything below is the verdict over what
# the loop above ran. Its `exit 1`s are complete findings, not cuts.
abschnitt_fertig
stufe "$GELAUFEN von $DA Sonden gelaufen, $BENANNT Sondenname(n) im Manifest benannt"
echo "   $GESTRICHEN Sondenname(n) sind GESTRICHEN -- ihre Sonde steht nicht als Programm."
echo "   Die dritte Zahl ist die wichtigere, und sie ist die ANKLAGE: jeder Name ohne"
echo "   Programm war eine Zusicherung ueber das Ausbleiben einer Widerlegung. Seit dem"
echo "   2026-08-30 traegt das Manifest ihn nicht mehr als Deckung, sondern als Luecke mit"
echo "   einer Zahl -- benannt getragen statt weggelassen. Wer einen Namen zurueckhaben"
echo "   will, schreibt die Sonde und traegt sie in SONDEN_MIT_PROGRAMM ein."
if [ "$NICHT_LAUFFAEHIG" -gt 0 ]; then
  echo "   $NICHT_LAUFFAEHIG Sonde(n) sind hier NICHT lauffaehig -- das ist ein Loch mit einer Zahl,"
  echo "   kein gruener Haken."
fi
if [ "$UNGEBAUT" -gt 0 ]; then
  echo "   $UNGEBAUT Sonde(n) haben nicht gebaut oder nicht durchgelaufen."
  exit 1
fi
if [ "$WIDERLEGT" -gt 0 ]; then
  echo
  echo "   **$WIDERLEGT WIDERLEGT.** Eine gefallene Sonde ist kein Testfehler, sondern ein"
  echo "   Befund ueber die Maschine oder ueber die Sonde selbst. Die Annahme, die sie"
  echo "   traegt, ist tot, und alles, was auf ihr steht, mit ihr."
  exit 1
fi

# ---------------------------------------------------------------------------------------
# APPENDED 2026-09-11 (m03-sondenabnahme): the frist-28 staffel.
#
# The fourteen staged date probes under `messung/proben/frist-28/` stand outside every
# acceptance run ("staged: in keiner Abnahme", `messung/FRIST-SONDEN-28.md`). This stage
# binds their RUN into this runner, which `instrumente/abnahme.py` drives as part of the
# standard acceptance: `run.sh` must print `FRIST-28: ALL PASS` and leave with 0, or this
# runner leaves with 1.
#
# What this stage does NOT do: it moves no coverage figure. The staged probes name
# obligations no `deadline` clause declares and no manifest entry lists, so
# `pruefe-sondendeckung.py` still reports `17 of 50` after this stage -- honestly, because
# counting them would be coverage without an obligation behind it. The remainder is booked
# in `messung/SONDEN-ABDECKUNG-REST.md`; full binding (deadline clauses, `sonden/`
# programs, `manifest::SONDEN_MIT_PROGRAMM`, register rows, quota-mark move) belongs to an
# owner assembly with checker-side rights this post does not claim.
#
# Position: this stage runs LAST and nothing stands behind it, so its `exit 1` is a
# complete finding about the staffel, not a cut (`abschnitt.sh`: nothing unmeasured
# behind a failing exit). The per-probe `FRIST` is the same deadline the loop above uses;
# the staffel measures about two seconds on `fisch`, so a hang here trips the same
# `HAENGT` convention the loop books as unbuilt.
# ---------------------------------------------------------------------------------------
stufe "Frist-28 staffel -- the fourteen staged date probes"
FRIST28_OUT="$TMP/frist28.out"
if timeout "$FRIST" "$W/messung/proben/frist-28/run.sh" >"$FRIST28_OUT" 2>&1; then
  FRIST28_RC=0
else
  FRIST28_RC=$?
fi
sed 's/^/      /' "$FRIST28_OUT"
if [ "$FRIST28_RC" -eq 124 ]; then
  echo "  HAENGT  frist-28 staffel -- Frist $FRIST s ueberschritten"
  exit 1
fi
if [ "$FRIST28_RC" -eq 0 ] && grep -q "FRIST-28: ALL PASS" "$FRIST28_OUT"; then
  echo "  HOLDS  frist-28 staffel (14 staged probes behaved as booked)"
else
  echo "  FINDING  frist-28 staffel -- run.sh exit $FRIST28_RC or ALL PASS missing (see above)"
  exit 1
fi
exit 0
