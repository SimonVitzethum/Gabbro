#!/usr/bin/env bash
# Leitet die Zahlen aus fallen-klassifikation.tsv ab, statt sie danebenzuschreiben.
# Falle 80: eine Zahl, die ein Mensch parallel zur Wahrheit fuehrt.
set -euo pipefail

# **`LC_ALL=C` -- und das ist kein Schoenheitsfehler.** Fremde Werkzeuge melden im
# Gebietsschema des Benutzers: unter `de_DE.UTF-8` sagt der Binder `Mehrfachdefinition von`
# statt `multiple definition`, und ein `grep -q` darauf trifft nicht. Dieselbe Klasse wie
# `W16` -- ein Werkzeug, das sein eigenes Gebietsschema misst und dabei plausibel aussieht.
export LC_ALL=C

cd "$(dirname "$0")/.."
D=fallen-klassifikation.tsv
n=$(grep -cE '^[0-9]+\s' "$D")
[ "$n" -eq 100 ] || { echo "ERWARTET 100 Eintraege, gefunden $n -- Quelle und Tabelle sind auseinander."; exit 1; }
echo "== Klassen (n=$n) =="
awk -F'\t' '/^[0-9]+\t/{c[$2]++} END{for(k in c) printf "  %-2s %3d  %5.1f %%\n", k, c[k], 100*c[k]/100}' "$D" | sort
echo
echo "== Konstrukte, nach Zahl der getoeteten Fallen =="
awk -F'\t' '/^[0-9]+\t/ && $3!="-" {c[$3]++} END{for(k in c) printf "  %-12s %3d\n", k, c[k]}' "$D" | sort -k2 -rn
echo
# Sprechprobe: die Auswertung muss auch FALLEN koennen.
awk -F'\t' '/^[0-9]+\t/ && $2!~/^[SMWB]$/ {print "  UNBEKANNTE KLASSE in Zeile " $1 ": " $2; bad=1} END{exit bad?1:0}' "$D" \
  && echo "Sprechprobe: alle Klassen sind S/M/W/B."
