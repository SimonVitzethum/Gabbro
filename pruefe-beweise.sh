#!/usr/bin/env bash
# **Der Beweiswaechter -- mit Wachhund, und der hat einen Grund.**
#
# Ein Beweisschritt, der ohne Schranke sucht, ist dieselbe Bauart wie eine Schleife ohne
# `bounded`. Dieser Ordner hat das ZWEIMAL bezahlt:
#
#   2026-08-17, erstes Mal   `metis` in Verbund_Konstruktor.thy -- 9 Minuten, 6,3 GB
#   2026-08-17, zweites Mal  `blast` in Accumulates_Monoid.thy  -- 12 Minuten, 4,8 GB
#
# **Beim zweiten Mal stand die Regel schon da.** Eine Regel, die man kennt und trotzdem
# bricht, braucht keinen weiteren Satz -- sie braucht ein Werkzeug.
#
#   ./pruefe-beweise.sh          -- baut die Sitzung mit Wachhund
#
# Der Wachhund haelt an, statt die Maschine anzuhalten. *Ein Ordner, der beim Beweisen den
# Rechner umbringt, misst danach gar nichts mehr.*
set -uo pipefail
W="$(cd "$(dirname "$0")" && pwd)"
GRENZE_GB="${GRENZE_GB:-3}"
ZEIT="${ZEIT:-600}"
ISABELLE="${ISABELLE:-$HOME/Isabelle2025-2/bin/isabelle}"

[ -x "$ISABELLE" ] || { echo "ABBRUCH: $ISABELLE nicht ausfuehrbar -- es wurde NICHTS geprueft."; exit 1; }

echo "== Beweise: Sitzung Gabbro, Wachhund bei ${GRENZE_GB} GB / ${ZEIT}s =="
( cd "$W/beweise" && "$ISABELLE" build -o threads=1 -D . ) > /tmp/gabbro-beweise.log 2>&1 &
BAU=$!

ANGEHALTEN=0
while kill -0 $BAU 2>/dev/null; do
    sleep 5
    for p in $(pgrep -f poly 2>/dev/null); do
        # **Feld 2, nicht Feld 1.** Die erste Zahl in `statm` ist die VIRTUELLE Groesse --
        # bei Poly/ML rund 22 GB, und zwar im Normalbetrieb. Die erste Fassung dieses
        # Wachhunds hat damit jeden Lauf erschlagen. *Ein Waechter, der immer anschlaegt,
        # misst nichts -- er verbietet nur.*
        RSS=$(awk '{print $2}' /proc/$p/statm 2>/dev/null || echo 0)
        GB=$(( RSS * 4096 / 1073741824 ))
        if [ "$GB" -ge "$GRENZE_GB" ]; then
            echo "  WACHHUND: PID $p bei ${GB} GB -- angehalten."
            echo "  **Ein Beweisschritt ohne Schranke sucht, statt zu rechnen.** Wer hier"
            echo "  landet, ersetzt den Schritt durch einen geschriebenen, nicht die Grenze."
            kill -9 $p 2>/dev/null
            ANGEHALTEN=1
        fi
    done
done
wait $BAU; ERG=$?

if [ $ANGEHALTEN = 1 ]; then
    echo "== BEWEISE: ABGEBROCHEN (Wachhund) =="
    exit 1
fi
if [ $ERG != 0 ]; then
    echo "== BEWEISE: FEHLER =="
    grep -E "^\*\*\*" /tmp/gabbro-beweise.log | head -12
    exit 1
fi
grep -E "Finished Gabbro" /tmp/gabbro-beweise.log
N=$(grep -c "^    [A-Z]" "$W/beweise/ROOT")
echo "== BEWEISE: ALL PASS -- $N Theorien =="
echo "  Und was das NICHT heisst: jede Theorie fuehrt ihren eigenen M-2-Abschnitt --"
echo "  was sie zeigt, und was sie ausdruecklich nicht zeigt. Ein gruener Lauf ist die"
echo "  Summe dieser Saetze, nicht mehr."
