#!/usr/bin/env bash
# **Die Vergleichsmessung, die P5s Tor verlangt:** „erzeugt <= Handschrift + Rauschen".
#
# Zwei Lasten, je dieselbe Rechnung auf beiden Seiten -- und die GLEICHHEIT der Ergebnisse
# wird vor der Zeit geprueft. *Zwei verschieden schnelle Rechnungen ueber verschiedene
# Ergebnisse zu vergleichen ist keine Messung.*
#
# Die Handschrift ist die IDIOMATISCHE, nicht die abgeschriebene: gepacktes `struct` mit
# Bitfeldern und Byteordnungstausch fuer den IP-Kopf, Feld fester Laenge fuer die Tabelle --
# einschliesslich der fehlenden Schrankenpruefung, denn die schreibt ein C-Programmierer
# auch nicht hin.
#
# *Der erste Anlauf am IP-Kopf kopierte je Kopf mit `memcpy` und liess Gabbro 3,5-mal
# schneller aussehen. Ein Vergleich, den die eigene Seite so gewinnt, ist ein Strohmann.*
set -euo pipefail
W="$(cd "$(dirname "$0")" && pwd)"
command -v cc > /dev/null || { echo "KEIN CC -- nichts gemessen"; exit 1; }
echo "== IP-Kopf: Bitfelder, Byteordnung, 20 000 Koepfe x 2 000 Runden =="
cc -std=c11 -O2 -Wall -Wextra -I"$W" -o "$W/.ip" "$W/treiber-ipkopf.c" "$W/hand-ipkopf.c"
"$W/.ip"
echo
echo "== Tabelle: 4 096 Plaetze, Index aus einem undurchsichtigen Feld =="
cc -std=c11 -O2 -Wall -Wextra -I"$W" -o "$W/.tab" "$W/treiber-tabelle.c" "$W/hand-tabelle.c"
"$W/.tab"
rm -f "$W/.ip" "$W/.tab"
