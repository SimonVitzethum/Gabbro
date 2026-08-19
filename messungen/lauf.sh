#!/usr/bin/env bash
# **BEIDE Seiten in DERSELBEN Uebersetzungseinheit** (berichtigt 2026-08-20).
#
# Der erste Aufbau zog Gabbros C per `#include` in den Treiber und uebersetzte die
# Handschrift als eigene Einheit. Damit war die eine Seite inlinebar und die andere nicht --
# **das misst die Bauart, nicht die Sprache**, und es bevorteilte systematisch die eigene.
# Aufgefallen ist es am `accumulates`-Lauf, wo Gabbro 3,5-mal schneller aussah.
#
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
cc -std=c11 -O2 -Wall -Wextra -I"$W" -o "$W/.ip" "$W/treiber-ipkopf.c"
"$W/.ip"
echo
echo "== Tabelle: 4 096 Plaetze, Index aus einem undurchsichtigen Feld =="
cc -std=c11 -O2 -Wall -Wextra -I"$W" -o "$W/.tab" "$W/treiber-tabelle.c"
"$W/.tab"
echo
echo "== narrow: eine GEPRUEFTE Schranke gegen gar keine =="
cc -std=c11 -O2 -Wall -Wextra -I"$W" -o "$W/.nar" "$W/treiber-narrow.c"
"$W/.nar"
echo
echo "== accumulates min: das KOMPLEMENT gegen ein vorbelegtes Feld =="
cc -std=c11 -O2 -Wall -Wextra -I"$W" -o "$W/.akk" "$W/treiber-akku.c"
"$W/.akk"
rm -f "$W/.ip" "$W/.tab" "$W/.nar" "$W/.akk"
