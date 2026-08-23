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
trap 'rm -rf "$TMP"' EXIT

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

echo "== Sprechprobe des Laeufers =="
S0="$(probe_bauen 0)"; S1="$(probe_bauen 1)"; S77="$(probe_bauen 77)"
echo "  eine haltende Sonde  -> $S0   (erwartet 0)"
echo "  eine WIDERLEGENDE    -> $S1   (erwartet 1)"
echo "  eine nicht lauffaehige -> $S77  (erwartet 77)"
if [ "$S0" != "0" ] || [ "$S1" != "1" ] || [ "$S77" != "77" ]; then
  echo "  GESCHEITERT -- der Laeufer unterscheidet die drei Zustaende nicht."
  exit 1
fi
echo "  ok (alle drei Zustaende kommen an)"
echo

# ---------------------------------------------------------------------------------------
# Der Bestand: wieviele Sonden sind BENANNT, wieviele stehen hier als Programm?
# ---------------------------------------------------------------------------------------
BIN="$W/target/debug/gabbro"
BENANNT="nicht gezaehlt"
if [ -x "$BIN" ]; then
  # **Aus dem Manifest, nicht aus einem `grep`.** Drei der Sonden gehoeren zu Annahmen, die
  # `manifest.rs` ERZEUGT; im Quelltext steht ihre Zeile nirgends, und eine Textzaehlung
  # meldete deshalb 24 statt 26.
  BENANNT="$(timeout "$FRIST" "$BIN" annahmen "$W"/beispiele/*.gab 2>/dev/null \
             | grep -o 'sonde_[a-zA-Z0-9_]*' | sort -u | wc -l)"
fi
DA=0
for f in "$W"/sonden/sonde_*.c; do [ -e "$f" ] && DA=$((DA+1)); done

echo "== Die Sonden dieses Ordners =="
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

echo "== $GELAUFEN von $DA Sonden gelaufen, $BENANNT Sondennamen im Manifest benannt =="
echo "   Die zweite Zahl ist die wichtigere, und sie ist die ANKLAGE: jeder Name ohne"
echo "   Programm ist eine Zusicherung ueber das Ausbleiben einer Widerlegung."
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
exit 0
