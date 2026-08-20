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
#   ./instrumente/pruefe-beweise.sh          -- baut die Sitzung mit Wachhund
#
# Der Wachhund haelt an, statt die Maschine anzuhalten. *Ein Ordner, der beim Beweisen den
# Rechner umbringt, misst danach gar nichts mehr.*
set -uo pipefail
W="$(cd "$(dirname "$0")/.." && pwd)"
GRENZE_GB="${GRENZE_GB:-3}"
ZEIT="${ZEIT:-600}"
ISABELLE="${ISABELLE:-$HOME/Isabelle2025-2/bin/isabelle}"

[ -x "$ISABELLE" ] || { echo "ABBRUCH: $ISABELLE nicht ausfuehrbar -- es wurde NICHTS geprueft."; exit 1; }

# **(c) Deckt ROOT jede Theoriedatei?** Eine `.thy`, die keiner Sitzung angehoert, wird nie
# geprueft -- und die Theorienzahl unten haette sie trotzdem nicht gezaehlt. *Eine Datei, die
# im Ordner liegt und in keinem ROOT steht, ist ein Beweis, den niemand fuehrt.*
FEHLT=""
for T in "$W"/beweise/*.thy; do
    N="$(basename "$T" .thy)"
    grep -qE "^    $N\\b" "$W/beweise/ROOT" || FEHLT="$FEHLT $N"
done
if [ -n "$FEHLT" ]; then
    echo "ABBRUCH: Theorien ohne ROOT-Eintrag --$FEHLT"
    echo "  Sie liegen im Ordner und gehoeren keiner Sitzung an. Es wurde NICHTS an ihnen geprueft."
    exit 1
fi

# **Sprechprobe, und sie steht VOR dem Lauf.** Ein Wachhund, der nie anschlaegt, ist von
# einem fehlenden nicht zu unterscheiden -- genau das war er bis zum 2026-08-20 fuer die
# Zeitgrenze. Hier wird beides gemessen: ein Schlaefer MUSS fallen, ein kurzer Lauf NICHT.
sprechprobe() {
    local Z=2 v=0 pid rc
    sleep 30 & pid=$!
    while kill -0 $pid 2>/dev/null; do
        sleep 1; v=$((v + 1))
        if [ "$v" -ge "$Z" ]; then kill -9 $pid 2>/dev/null; rc=gefangen; break; fi
    done
    [ "${rc:-durch}" = gefangen ] || { echo "  SPRECHPROBE GESCHEITERT: der Wachhund laesst einen Schlaefer durch"; return 1; }
    v=0; sleep 0.1 & pid=$!
    while kill -0 $pid 2>/dev/null; do
        sleep 1; v=$((v + 1))
        if [ "$v" -ge "$Z" ]; then echo "  SPRECHPROBE GESCHEITERT: der Wachhund erschlaegt einen kurzen Lauf"; return 1; fi
    done
    echo "  Sprechprobe: ok (ein Schlaefer faellt, ein kurzer Lauf nicht)"
}
sprechprobe || exit 1

echo "== Beweise: Sitzung Gabbro, Wachhund bei ${GRENZE_GB} GB / ${ZEIT}s =="
( cd "$W/beweise" && "$ISABELLE" build -o threads=1 -d . Gabbro ) > /tmp/gabbro-beweise.log 2>&1 &
BAU=$!

ANGEHALTEN=0
VERSTRICHEN=0
while kill -0 $BAU 2>/dev/null; do
    sleep 5
    VERSTRICHEN=$((VERSTRICHEN + 5))
    # **Die ZEITgrenze stand seit jeher in der Kopfzeile und wurde nie durchgesetzt**
    # (gefunden 2026-08-20 von `pruefe-waechter.py`, beim ersten Lauf). Der Banner sagte
    # „Wachhund bei N GB / Ms", und der Wachhund sah nur den Speicher.
    #
    # > *Ein angekuendigter Riegel, den niemand einlegt, ist schlechter als keiner: er
    # > beruhigt.* Dieselbe Klasse wie der Haenger in `pruefe-emission.sh` am selben Tag --
    # > ein Lauf, der nicht endet, sieht aus wie einer, der noch arbeitet.
    if [ "$VERSTRICHEN" -ge "$ZEIT" ]; then
        echo "  WACHHUND: ${VERSTRICHEN}s ohne Ende -- angehalten (Grenze ${ZEIT}s)."
        echo "  **Ein Beweislauf ohne Ende ist kein Beweislauf.** Wer hier landet, teilt die"
        echo "  Sitzung oder ersetzt den suchenden Schritt durch einen geschriebenen."
        kill -9 $BAU 2>/dev/null
        pkill -9 -f poly 2>/dev/null
        ANGEHALTEN=1
        break
    fi
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
# **(b) Ausgang 0 ist keine Evidenz.** `isabelle build` schweigt und meldet Erfolg, wenn die
# Auswahl LEER ist -- genau das tat die erste Fassung mit `-D .`: sie sang „ALL PASS" ueber
# einem Lauf, der nichts gebaut hatte. *Ein Waechter, der Schweigen fuer Zustimmung nimmt,
# misst nicht.* Darum wird hier ein Nachweis verlangt: entweder eine frische Fertigmeldung
# oder ein Bauwerksbuch, das juenger ist als jede Quelle.
BUCH="$(ls -t "$($ISABELLE getenv -b ISABELLE_HEAPS)"/*/log/Gabbro.db 2>/dev/null | head -1)"
if grep -qE "Finished Gabbro" /tmp/gabbro-beweise.log; then
    NACHWEIS="$(grep -E 'Finished Gabbro' /tmp/gabbro-beweise.log)"
elif [ -n "$BUCH" ] && [ -z "$(find "$W/beweise" -name '*.thy' -newer "$BUCH" -print -quit)" ] \
                    && [ ! "$W/beweise/ROOT" -nt "$BUCH" ]; then
    NACHWEIS="unveraendert seit $(date -r "$BUCH" '+%d.%m. %H:%M') -- keine Quelle ist juenger"
else
    echo "== BEWEISE: OHNE NACHWEIS =="
    echo "  Der Lauf endete ohne Fehler und ohne Fertigmeldung, und kein Bauwerksbuch ist"
    echo "  juenger als die Quellen. **Das ist kein gruener Lauf, sondern gar keiner.**"
    echo
    # **Und die haeufigste Ursache ist keine Aenderung an den Beweisen, sondern der SYNC**
    # (gefunden 2026-08-20). `CLAUDE.md` fuehrt ZWEI Uebertragungen mit verschiedenen
    # Schaltern, und das ist kein Schoenheitsfehler:
    #
    #     rsync -a       beweise/   -- Zeitstempel ERHALTEN
    #     rsync -rlpgoD  ./         -- Zeitstempel NEU (`cargo` braucht das)
    #
    # Wer den ganzen Baum mit `-rlpgoD` uebertraegt, gibt jeder `.thy` die aktuelle Zeit.
    # Isabelle rechnet nach INHALT und waehlt korrekt nichts aus; dieser Nachweis rechnet
    # nach ZEIT und findet keinen. **Zwei Begriffe von „aktuell" in einer Kette** -- dieselbe
    # Sippe wie der Bau aus einer Mischung (W16), nur mit umgekehrtem Vorzeichen: dort log
    # ein gruener Lauf, hier faellt ein richtiger durch.
    echo "  Haeufigste Ursache ist NICHT eine Aenderung an den Beweisen, sondern der Sync:"
    echo "  \`rsync -rlpgoD\` (fuer \`cargo\`) gibt jeder uebertragenen \`.thy\` die AKTUELLE"
    echo "  Zeit. Isabelle rechnet nach INHALT und baut nichts; dieser Nachweis rechnet nach"
    echo "  ZEIT und findet keinen. **CLAUDE.md uebertraegt \`beweise/\` deshalb mit \`-a\`.**"
    echo "  Heilung: \`rsync -a beweise/ …\` -- oder einmal \`isabelle build -f -d . Gabbro\`,"
    echo "  und das baut Pure und HOL mit."
    exit 1
fi

N=$(grep -c "^    [A-Z]" "$W/beweise/ROOT")
D=$(ls "$W"/beweise/*.thy | wc -l)
echo "== BEWEISE: ALL PASS -- $N Theorien ($D Dateien) =="
echo "  Nachweis: $NACHWEIS"
echo "  Und was das NICHT heisst: jede Theorie fuehrt ihren eigenen M-2-Abschnitt --"
echo "  was sie zeigt, und was sie ausdruecklich nicht zeigt. Ein gruener Lauf ist die"
echo "  Summe dieser Saetze, nicht mehr."
