#!/usr/bin/env bash
# **Der Differenztest -- die JA-Aussagen dieses Ordners.**
#
# Bis zum 2026-08-17 war die Emissionsflaeche die groesste unbeschaedigbare Flaeche des
# Projekts: `mutiere-pruefer.py` wies sie mit 0 Mutationen aus, und *was 0 Mutationen hat,
# ist nicht gedeckt, sondern unbeschaedigbar*.
#
# Dieser Waechter schliesst sie fuer SIEBEN Uebersetzungseinheiten, nicht fuer zehn:
#
#     .gab -> emit -> [zweimal, byteidentisch] -> cc -Werror -O0 UND -O2 -> UBSan
#          -> ausgefuehrt -> Ergebnis verglichen -> Zeugnis -> verfaelschtes C faellt
#
# **Seit dem 2026-08-19 uebersetzt er OPTIMIERT** (OPT0). Bis dahin fuhr er ohne `-O`, und
# damit lief die eine Probe nie, die eine ganze Klasse faengt: *eine Abweichung zwischen
# `-O0` und `-O2` ist der Fingerabdruck von undefiniertem Verhalten* -- der Uebersetzer legt
# UB zu seinen Gunsten aus, also tut er es erst, wenn er optimiert. Ein Erzeugnis, das nur
# ungeoptimiert stimmt, sieht bei jeder Abnahme richtig aus und ist es nicht.
#
# **Jede Stufe muss halten, und die letzte ist die, auf die es ankommt.** Ein Erzeuger, der
# uebersetzbares C liefert, das etwas anderes rechnet, ist schlimmer als einer, der nichts
# liefert -- er sieht aus wie ein Ergebnis.
#
#   1. `beispiele/16-by-ops-am-feld.gab` -- ein BEISPIEL. Tabelle, `count`, Bereichstypen.
#   2. `dokumente/FRAGMENTE.md` F7 -- ein FRAGMENT, und zwar aus dem eingefrorenen Korpus
#      geschnitten, nicht aus einer Kopie. Es misst die GEISTLOESCHUNG: `BootPhase` ist ein
#      `linear ghost type`, und die Frage, die dieser Lauf beantwortet, lautet **was kostet
#      die Phasendisziplin zur Laufzeit** -- Antwort: nichts.
set -euo pipefail

# **`LC_ALL=C` -- und das ist kein Schoenheitsfehler.** Fremde Werkzeuge melden im
# Gebietsschema des Benutzers: unter `de_DE.UTF-8` sagt der Binder `Mehrfachdefinition von`
# statt `multiple definition`, und ein `grep -q` darauf trifft nicht. Dieselbe Klasse wie
# `W16` -- ein Werkzeug, das sein eigenes Gebietsschema misst und dabei plausibel aussieht.
export LC_ALL=C

W="$(cd "$(dirname "$0")/.." && pwd)"
ARB="$(mktemp -d)"
trap 'rm -rf "$ARB"' EXIT

# **W1: eine uebersprungene Probe senkt die Zahl, sie laesst sie nicht unberuehrt.**
# Kein `cc` heisst NICHT „bestanden, uebersprungen" -- es heisst, dass dieser Waechter
# nichts gemessen hat, und das ist ein Rot.
if ! command -v cc > /dev/null; then
    echo "== EMISSION: KEIN CC -- der Differenztest hat NICHTS gemessen =="
    echo "  Ein fehlendes Werkzeug ist kein bestandener Test. W1: der Ausfall senkt die"
    echo "  Zahl, er laesst sie nicht unberuehrt."
    exit 1
fi

# **Die Sprechprobe der zwei neuen Stufen** (OPT0, 2026-08-19). *Ein Waechter, der beim
# ersten Versuch gruen ist, ohne dass jemand ihn hat fallen sehen, ist eine Verzierung* (R11).
#
# Zwei kleine C-Programme mit ABSICHTLICH undefiniertem Verhalten. Faengt der Aufbau sie
# nicht, misst die Stufe daneben nichts -- und dann faerbt dieser Waechter sich rot, bevor er
# eine einzige Einheit anfasst.
sprechprobe_ub() {
    local d; d="$(mktemp -d)"; local ok=0
    # (a) Stufe 5: eine Typverletzung rechnet bei -O0 und -O2 VERSCHIEDEN.
    cat > "$d/a.c" <<'PROBE_A'
#include <stdio.h>
#include <stdlib.h>
__attribute__((noinline)) static int f(int *pi, float *pf) { *pi = 1; *pf = 0.0f; return *pi; }
int main(void) { void *p = malloc(8); printf("%d\n", f((int *)p, (float *)p)); return 0; }
PROBE_A
    cc -std=c11 -O0 -o "$d/a0" "$d/a.c" 2>/dev/null
    cc -std=c11 -O2 -o "$d/a2" "$d/a.c" 2>/dev/null
    if [ "$("$d/a0")" = "$("$d/a2")" ]; then
        echo "  Sprechprobe 5: GESCHEITERT -- -O0 und -O2 rechnen gleich, wo sie es NICHT duerfen"
        echo "                 Diese Maschine kann den Unterschied nicht zeigen; Stufe 5 misst nichts."
        ok=1
    else
        echo "  Sprechprobe 5: ok (-O0 $("$d/a0") gegen -O2 $("$d/a2"))"
    fi
    # (b) Stufe 6: ein echter Ueberlauf muss den Sanitizer ausloesen.
    cat > "$d/b.c" <<'PROBE_B'
#include <stdio.h>
#include <limits.h>
volatile int a = INT_MAX;
__attribute__((noinline)) static int plus(int x, int y) { return x + y; }
int main(void) { printf("%d\n", plus(a, 1)); return 0; }
PROBE_B
    if ! cc -std=c11 -O1 -fsanitize=undefined -fno-sanitize-recover=all -o "$d/b" "$d/b.c" 2>/dev/null; then
        echo "  Sprechprobe 6: KEIN UBSAN -- Stufe 6 hat NICHTS gemessen"; ok=1
    elif "$d/b" > /dev/null 2>&1; then
        echo "  Sprechprobe 6: GESCHEITERT -- ein Ueberlauf kam durch, der Sanitizer schweigt"; ok=1
    else
        echo "  Sprechprobe 6: ok (der Ueberlauf faellt)"
    fi
    rm -rf "$d"
    return $ok
}
echo "== Sprechprobe: koennen die neuen Stufen ueberhaupt fallen? =="
if ! sprechprobe_ub; then
    echo "== EMISSION: die Sprechprobe haelt nicht -- ein Haken ohne Messung ist schlimmer als keiner =="
    exit 1
fi
echo

# Schneidet den ```gabbro-Block, der eine gegebene Zeile enthaelt, aus einer Markdown-Datei.
# **Aus dem Korpus, nicht aus einer Kopie** -- sonst misst der Waechter seine eigene Ablage.
schneide() {
    awk -v marke="$2" '
        /^```gabbro/ { drin=1; puffer=""; next }
        drin && /^```/ { if (puffer ~ marke) { printf "%s", puffer; exit } drin=0; next }
        drin { puffer = puffer $0 "\n" }
    ' "$1"
}

N_DURCHGESTOCHEN=0

lauf() {          # $1 Name  $2 Quelle  $3 Treiber  $4 Erwartet  $5 Gift-sed  $6 Zeugnis
    local name="$1" quelle="$2" treiber="$3" erwartet="$4" gift="$5" zeugnis="$6"
    # **Die Zahl wird GEZAEHLT, nicht gepflegt** (2026-08-20). Sie stand als `17` in der
    # Schlusszeile, waehrend achtzehn Einheiten liefen -- dieselbe Klasse wie die Liste, die
    # eine Regel wurde, nur eine Ebene hoeher. *Eine Kennzahl, die jemand nachtragen muss,
    # ist irgendwann falsch.*
    N_DURCHGESTOCHEN=$((N_DURCHGESTOCHEN + 1))
    local c="$ARB/$name.c"
    echo "== Differenztest: $name =="

    # 1. Erzeugen. Der Pruefer laeuft davor -- C aus einem Baum zu erzeugen, den die Paesse
    #    nicht angenommen haben, waere C fuer ein Programm, das Gabbro ablehnt.
    if ! cargo run -q --manifest-path "$W/Cargo.toml" --bin gabbro -- emit "$quelle" \
            > "$c" 2> "$ARB/fehler"; then
        echo "  1. erzeugen:   GESCHEITERT"; cat "$ARB/fehler"; exit 1
    fi
    echo "  1. erzeugen:   ok ($(grep -c '' "$c") Zeilen C)"

    # 1b. **Zweimal erzeugen, Byte gegen Byte.** Die Reproduzierbarkeit war ueber 25 Laeufe
    #     GEMESSEN und nirgends ZUGESAGT -- und eine gemessene Eigenschaft ohne Waechter ist
    #     eine, die beim naechsten `HashMap` ueber Namen still verschwindet: Rust wuerfelt je
    #     Prozess einen anderen Startwert. Jeder Zwischenspeicher stromabwaerts (`ccache`, ein
    #     Bausystem, ein Wiederholbau) ruht darauf, dass derselbe Quelltext dasselbe C ergibt;
    #     *ein Erzeugnis, das sich zwischen zwei Laeufen unterscheidet, macht jeden Vergleich
    #     zweier Baeume wertlos.* («C», Die Sprechprobe; «Z2»)
    #
    #     **Diese Stufe stand zweimal da** -- beide Zweige haben sie unabhaengig gebaut, und
    #     erst der Merge hat es gezeigt (WERKZEUGKASTEN.md W7).
    if ! cargo run -q --manifest-path "$W/Cargo.toml" --bin gabbro -- emit "$quelle" \
            > "$ARB/$name-zweitlauf.c" 2> /dev/null; then
        echo "  1b. zweitlauf: GESCHEITERT"; exit 1
    fi
    if ! cmp -s "$c" "$ARB/$name-zweitlauf.c"; then
        echo "  1b. zweitlauf: VERSCHIEDEN -- zwei Laeufe, zwei Erzeugnisse"
        diff "$c" "$ARB/$name-zweitlauf.c" | head -10; exit 1
    fi
    echo "  1b. zweitlauf: ok (bitgleich)"

    # 2. Der Lizenzhinweis. `LIZENZ-ZUSATZ.md` knuepft die zusaetzliche Erlaubnis an ihn --
    #    eine Bedingung, die niemand prueft, ist eine Bitte.
    if ! grep -q "Generated by Gabbro" "$c"; then
        echo "  2. Lizenz:     FEHLT -- die Bedingung aus LIZENZ-ZUSATZ.md steht nicht im C"; exit 1
    fi
    echo "  2. Lizenz:     ok (Hinweis im Kopf)"

    # 3. Uebersetzen, und zwar streng. Eine Warnung im erzeugten C ist ein Befund ueber den
    #    Erzeuger, nicht ueber den Anwender -- er hat die Zeile nicht geschrieben.
    printf '%s' "$treiber" | sed "s/@ERZEUGT@/$name.c/" > "$ARB/$name-treiber.c"
    if ! cc -std=c11 -O0 -Wall -Wextra -Werror -I"$ARB" -o "$ARB/$name-probe" \
            "$ARB/$name-treiber.c" 2> "$ARB/ccfehler"; then
        echo "  3. cc -Werror: GESCHEITERT"; head -20 "$ARB/ccfehler"; exit 1
    fi
    echo "  3. cc -Werror: ok (keine Warnung)"

    # 4. Ausfuehren und VERGLEICHEN. Das ist die Stufe, die die anderen drei erst zu einer
    #    Aussage macht.
    local ist; ist="$("$ARB/$name-probe")"
    if [ "$ist" != "$erwartet" ]; then
        echo "  4. Ergebnis:   FALSCH"
        echo "     erwartet:   $erwartet"
        echo "     bekommen:   $ist"
        exit 1
    fi
    echo "  4. Ergebnis:   ok ($ist)"

    # 5. **`-O0` gegen `-O2`, und die Ergebnisse muessen GLEICH sein** (OPT0, 2026-08-19).
    #
    #    Bis heute uebersetzte dieser Waechter ohne `-O` -- und damit lief die eine Probe
    #    nie, die eine ganze Klasse faengt: **eine Abweichung zwischen `-O0` und `-O2` ist
    #    der Fingerabdruck von undefiniertem Verhalten.** Der Uebersetzer darf UB zu seinen
    #    Gunsten auslegen, also tut er es erst, wenn er optimiert; ein Erzeugnis, das nur
    #    ungeoptimiert stimmt, sieht bei jeder Abnahme richtig aus und ist es nicht.
    #
    #    *Und es ist die EINZIGE Probe, die ein falsches `restrict` findet* -- eine falsche
    #    Alias-Zusicherung erzeugt Code, der bei `-O0` stimmt und bei `-O2` nicht.
    if ! cc -std=c11 -O2 -Wall -Wextra -Werror -I"$ARB" -o "$ARB/$name-probe-o2" \
            "$ARB/$name-treiber.c" 2> "$ARB/ccfehler2"; then
        echo "  5. -O2:        GESCHEITERT beim Uebersetzen"; head -20 "$ARB/ccfehler2"; exit 1
    fi
    local ist_o2; ist_o2="$("$ARB/$name-probe-o2")"
    if [ "$ist_o2" != "$ist" ]; then
        echo "  5. -O2:        ANDERES ERGEBNIS als -O0 -- das ist undefiniertes Verhalten"
        echo "     -O0:        $ist"
        echo "     -O2:        $ist_o2"
        exit 1
    fi
    echo "  5. -O2:        ok (gleiches Ergebnis wie -O0)"

    # 6. **Der Sanitizer, und er prueft eine ZUSAGE nach.** Gabbro beweist Ueberlauffreiheit
    #    (`M104`) und Schrankentreue (`M103`) -- **dann darf `-fsanitize=undefined` nichts
    #    finden, und wenn doch, ist es ein Befund ueber M1 und nicht ueber C.**
    #
    #    `-fno-sanitize-recover=all`, damit ein Fund den Lauf beendet statt eine Zeile zu
    #    drucken und weiterzulaufen. *Ein Sanitizer, der meldet und durchlaesst, faerbt keinen
    #    Waechter rot.*
    #
    #    **`address` steht hier NICHT**, und das ist kein Vergessen: auf dem Arbeitsrechner
    #    (gehaerteter Kern) kollidiert ASans Schattenspeicher mit der Speicherkarte und der
    #    Lauf bricht vor `main` ab. *Eine Probe, die nicht laeuft, ist keine bestandene* --
    #    sie steht als offener Punkt im TODO und nicht als Haken hier.
    if ! cc -std=c11 -O1 -fsanitize=undefined -fno-sanitize-recover=all \
            -I"$ARB" -o "$ARB/$name-probe-ub" "$ARB/$name-treiber.c" 2> "$ARB/ccfehler3"; then
        echo "  6. UBSan:      GESCHEITERT beim Uebersetzen"; head -20 "$ARB/ccfehler3"; exit 1
    fi
    local ist_ub; ist_ub="$("$ARB/$name-probe-ub" 2> "$ARB/ubfehler")" || {
        echo "  6. UBSan:      SCHLAEGT AN -- Gabbro beweist Ueberlauffreiheit, hier faellt sie"
        head -10 "$ARB/ubfehler"; exit 1
    }
    if [ -s "$ARB/ubfehler" ]; then
        echo "  6. UBSan:      MELDUNG auf stderr"; head -10 "$ARB/ubfehler"; exit 1
    fi
    if [ "$ist_ub" != "$ist" ]; then
        echo "  6. UBSan:      ANDERES ERGEBNIS"; echo "     $ist / $ist_ub"; exit 1
    fi
    echo "  6. UBSan:      ok (kein Fund, gleiches Ergebnis)"

    # 7. **Das Uebersetzungszeugnis** -- K100.4, Weg (b). Die Differenztests messen EIN
    #    Ergebnis; das Zeugnis zaehlt auf, worauf die Uebersetzung ruht. Die Bedingung hier ist
    #    die Kreuzprobe: **was der Erzeuger absenkt, muss das Zeugnis einordnen.** Steht eine
    #    Form in keiner Einordnung, hat der Erzeuger etwas abgesenkt und es niemandem gesagt.
    if ! cargo run -q --manifest-path "$W/Cargo.toml" --bin gabbro -- zeugnis "$quelle" \
            > "$ARB/$name.zeugnis" 2> "$ARB/zfehler"; then
        echo "  7. Zeugnis:    GESCHEITERT"; cat "$ARB/zfehler"; exit 1
    fi
    if grep -q "UNZUGEORDNET" "$ARB/$name.zeugnis"; then
        echo "  7. Zeugnis:    UNZUGEORDNET -- der Erzeuger senkt eine Form ab, die keine"
        echo "                 Einordnung kennt. Die Vertrauensflaeche ist groesser als gebucht."
        grep -A3 "UNZUGEORDNET" "$ARB/$name.zeugnis"; exit 1
    fi
    # **Die Zahl wird ABGELESEN, nicht nachgezaehlt** (W2). Ein `grep -c` ueber der
    # Schablonenliste zaehlte hier erst die Zeile „keine. Diese Einheit nimmt nichts an" mit --
    # sie faengt genauso mit fuenf Leerzeichen und einem Punkt an. *Eine zweite Zaehlung neben
    # einer vorhandenen ist eine Gelegenheit, sich zu widersprechen.*
    #    **Und der Befund wird VERGLICHEN, nicht gedruckt.** Ein Zeugnis, das man nur ansieht,
    #    ist ein Bericht; eines, gegen das ein Tor steht, ist eine Buchung. Wer eine Form
    #    umklassifiziert -- eine Schablone zur direkten Absenkung erklaert -- faellt hier.
    # **`templates` statt `Schablonen` seit 2026-08-19** -- die Sprachflaeche von Gabbro ist
    # englisch, und diese Zeile liest sie ab.
    local zist; zist="$(sed -n 's/^     \(.*templates.*\)$/\1/p' "$ARB/$name.zeugnis")"
    if [ "$zist" != "$zeugnis" ]; then
        echo "  7. Zeugnis:    ANDERS ALS GEBUCHT"
        echo "     gebucht:    $zeugnis"
        echo "     bekommen:   $zist"
        exit 1
    fi
    echo "  7. Zeugnis:    ok ($zist)"

    # **Die Sprechprobe in die andere Richtung.** Ein Differenztest, der nicht rot werden kann,
    # misst nichts -- dieselbe Regel, mit der jede Messung dieses Ordners anfaengt (R14).
    sed "$gift" "$c" > "$ARB/$name-gift.c"
    printf '%s' "$treiber" | sed "s/@ERZEUGT@/$name-gift.c/" > "$ARB/$name-gifttreiber.c"
    cc -std=c11 -w -I"$ARB" -o "$ARB/$name-giftprobe" "$ARB/$name-gifttreiber.c"
    # **Ein verfaelschtes Erzeugnis darf NICHT ENDEN, und bis 2026-08-20 hing der Waechter
    # dann fuer immer.**
    #
    # `baum41`s Gift lenkt den Abstieg von `erstes_kind` auf `elter` -- der Lauf klettert zur
    # Wurzel und dreht dort. Ohne Frist blieb `pruefe-emission.sh` an genau dieser Zeile
    # stehen: kein Fehler, keine Ausgabe, **nur ein Prozess, der laeuft.** Auf
    # `ki-pc-fisch-101` standen dadurch am 2026-08-20 einundzwanzig Laeufe nebeneinander, der
    # aelteste seit dreieinhalb Stunden -- und sie stritten sich um denselben Baum.
    #
    # > *Ein Haenger sieht aus wie „laeuft noch", nicht wie ein Befund.* Dieselbe Klasse wie
    # > W16: das Werkzeug misst nicht, und nichts wird rot.
    #
    # Eine Frist macht daraus eine Antwort. **Und eine ueberschrittene Frist ist ein
    # BESTEHEN**: ein Programm, das nicht zu Ende kommt, liefert das erwartete Ergebnis
    # gewiss nicht.
    # **`set -e` steht in Zeile 28, und eine ueberschrittene Frist ist ein Fehlschlag.**
    # Ohne das `|| rc=$?` beendete die Frist den ganzen Waechter STILL -- mit Ruecklaufwert 0
    # und ohne Stufe 9. *Der erste Anlauf tat genau das, und die Ausgabe sah vollstaendig
    # aus, weil sie mit einem `ok` endete.*
    local gausgabe rc
    rc=0
    gausgabe="$(timeout 10 "$ARB/$name-giftprobe")" || rc=$?
    if [ "$rc" = 124 ]; then
        echo "  8. Sprechprobe: ok (verfaelschtes C endet nicht -- Frist 10 s)"
    elif [ "$gausgabe" = "$erwartet" ]; then
        echo "  8. Sprechprobe: UEBERSEHEN -- ein veraendertes Erzeugnis liefert dasselbe?"; exit 1
    else
        echo "  8. Sprechprobe: ok (verfaelschtes C faellt)"
    fi
}

# -- 1. Das Beispiel: eine Tabelle, ein Feld, eine erzeugte Operation --------------------
#
#    Erwartet:  42  -- `stand` liefert, was geschrieben wurde
#                1  -- `belegen` setzt `benutzt`
#                8  -- das Feld hat die Slots aus `count N`, N = 8
#                0  -- und Slot 0 ist unberuehrt: die Operation trifft EINEN Slot
TREIBER16='#include <stdio.h>
#include "@ERZEUGT@"
int main(void) {
    Objekte o = {0};
    o.slots[3].zaehler = 42;
    belegen(&o, 3);
    printf("%u %d %d %d\n",
           stand(&o, 3),
           (int)o.slots[3].benutzt,
           (int)(sizeof(o.slots) / sizeof(o.slots[0])),
           (int)o.slots[0].benutzt);
    return 0;
}
'
lauf "beispiel16" "$W/beispiele/16-by-ops-am-feld.gab" "$TREIBER16" "42 1 8 0" \
     's/\.benutzt = true/.benutzt = false/' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 1 templates (0 of them UNPROVED), 5 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 2. Das Fragment: die Geistloeschung -------------------------------------------------
#
# **Die Frage, die dieser Lauf beantwortet:** `BootPhase` ist ein `linear ghost type`, der
# durch sechs Bootschritte gefaedelt und am Ende verbraucht wird. Er traegt das ganze
# Sicherheitsargument des Fragments -- und er darf zur Laufzeit **nicht existieren**.
#
# Die Loeschung muss an DREI Orten gleichzeitig halten, und zwei davon sind still, wenn sie
# ausfallen: die Signatur (`void mmu_an(void)`, nicht `void mmu_an(BootPhase)`), der Rufort
# (`mmu_an()`, nicht `mmu_an(p)`) und die `let`-Bindung (`mmu_an();`, nicht
# `void p1 = mmu_an();`). Faellt die dritte falsch aus -- naemlich indem die ganze Anweisung
# verschwindet --, uebersetzt das C und der Bootschritt findet **nicht statt**.
#
# Genau das misst die Erwartung: **sechs Schritte, in dieser Reihenfolge, je genau einmal.**
verlorene_zeilen() {   # $1 Ausschnitt  $2 Arbeitsfassung -- druckt, was FEHLT
    diff "$1" "$2" > "$ARB/f2-diff" || true
    grep '^<' "$ARB/f2-diff" || true
}

schneide "$W/dokumente/FRAGMENTE.md" "module caprock::bringup" > "$ARB/f7.gab"
if ! grep -q "linear ghost type BootPhase" "$ARB/f7.gab"; then
    echo "== EMISSION: F7 NICHT GESCHNITTEN -- der Waechter misst seine eigene Ablage =="
    exit 1
fi
TREIBER7='#include <stdio.h>
static int spur[8];
static int n;
void mmu_an(void)               { spur[n++] = 1; }
void cap_tabellen(void)         { spur[n++] = 2; }
void ipc_tabellen(void)         { spur[n++] = 3; }
void autoritaet_melden(void)    { spur[n++] = 4; }
void verifizierer_starten(void) { spur[n++] = 5; }
void root_task_starten(void)    { spur[n++] = 6; }
#include "@ERZEUGT@"
int main(void) {
    hochlauf();
    for (int i = 0; i < n; i++) printf("%d", spur[i]);
    printf("\n");
    return 0;
}
'
# **F7 faehrt seit dem 2026-08-25 aus der VERVOLLSTAENDIGTEN Fassung**, und zwar aus dem
# Grund, aus dem es diesen Ordner ueberhaupt gibt: der Ausschnitt nennt `Text` als Zeigerziel
# und erklaert es nirgends. *`N040` sagt es seit heute; bis dahin lief dieser Durchstich
# darueber hinweg* -- der Erzeuger schrieb eine C-Vorwaertsdeklaration, `cc -Werror` war
# zufrieden, und `123456` stimmte. **Ein Durchstich misst, was er sieht.**
#
# Derselbe Riegel wie bei F2: fehlt der Arbeitsfassung auch nur EINE Zeile des Ausschnitts,
# faellt der Lauf. *Ergaenzen ist erlaubt, weglassen nicht.*
if [ -n "$(verlorene_zeilen "$ARB/f7.gab" "$W/messung/fragmente/F07.gab")" ]; then
    echo "== EMISSION: F07.gab hat eine Zeile des eingefrorenen Ausschnitts VERLOREN =="
    verlorene_zeilen "$ARB/f7.gab" "$W/messung/fragmente/F07.gab" | head -10
    exit 1
fi
grep -v "linear ghost type BootPhase" "$W/messung/fragmente/F07.gab" > "$ARB/f7-kurz.gab"
if [ -z "$(verlorene_zeilen "$ARB/f7.gab" "$ARB/f7-kurz.gab")" ]; then
    echo "== EMISSION: Sprechprobe F7 haelt nicht -- eine entfernte Ausschnittzeile faellt"
    echo "             nicht auf. Dieser Vergleich misst NICHTS. =="
    exit 1
fi
echo "  (F7: der eingefrorene Ausschnitt steht vollstaendig in der Arbeitsfassung"
echo "       -- und eine fehlende Zeile faellt auf, Sprechprobe ok)"
lauf "fragment7" "$W/messung/fragmente/F07.gab" "$TREIBER7" "123456" \
     's/    ipc_tabellen();/    \/* geloescht *\//' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 0 templates (0 of them UNPROVED), 4 direct forms, 7 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 3. Das Fragment F8: die Sperre wird auf JEDEM Pfad gegeben --------------------------
#
# **Der Rumpf von `toeten` kehrt aus dem `locks`-Block heraus zurueck, und zwar aus beiden
# Zweigen.** Ein Erzeuger, der die Freigabe nur ans Blockende schreibt, laesst die Sperre auf
# beiden Wegen stehen -- und das C uebersetzt. *Woertlich die Klasse, die C8 bezahlt hat: ein
# neuer Abweispfad erbt die Aufraeumpflicht des alten nicht.* Hier erbt er sie, weil nicht der
# Schreiber sie ausgibt.
#
# Zweitens misst dieser Lauf den SONDERWERT: `aufloesen` liefert `option index into Laufliste`,
# und `Laufliste_NONE` ist die Laenge selbst -- der eine Wert, den ein gueltiger Index nach
# `count N` und M1 nie annimmt.
schneide "$W/dokumente/FRAGMENTE.md" "module caprock::sched" > "$ARB/f8.gab"
if ! grep -q "locks SCHEDS" "$ARB/f8.gab"; then
    echo "== EMISSION: F8 NICHT GESCHNITTEN =="; exit 1
fi
TREIBER8='#include <stdio.h>
static int genommen, gegeben;
static unsigned antwort;
void SCHEDS_nimm(void)         { genommen++; }
void SCHEDS_gib(void)          { gegeben++; }
void SCHEDS_nimm_geteilt(void) { genommen++; }
void SCHEDS_gib_geteilt(void)  { gegeben++; }
#include "@ERZEUGT@"
uint32_t aufloesen(const Laufliste *l, uint32_t t) { (void)l; (void)t; return antwort; }
int main(void) {
    static Laufliste l;
    l.slots[3].belegt = true;
    antwort = 3; genommen = 0; gegeben = 0;
    int a = toeten(&l, 7, 0);
    printf("%d %d %d %d", a, genommen, gegeben, (int)l.slots[3].belegt);

    l.slots[3].belegt = true;
    antwort = Laufliste_NONE; genommen = 0; gegeben = 0;
    int b = toeten(&l, 7, 0);
    printf(" %d %d %d %d\n", b, genommen, gegeben, (int)l.slots[3].belegt);
    return 0;
}
'
#    Erwartet, Fall A (`aufloesen` findet den Faden):
#      1  -- `toeten` meldet Erfolg
#      1  -- die Sperre wurde einmal genommen
#      1  -- **und einmal gegeben, obwohl der Weg mit `return` aus dem Block springt**
#      0  -- der Slot ist geraeumt
#    Fall B (`aufloesen` liefert `None`):
#      0  -- kein Erfolg
#      1 1 -- genommen und gegeben, auch auf dem ANDEREN Rueckkehrpfad
#      1  -- und der Slot ist unberuehrt: der None-Zweig fasst nichts an
lauf "fragment8" "$ARB/f8.gab" "$TREIBER8" "1 1 1 0 0 1 1 1" \
     '0,/^                SCHEDS_gib();$/s///' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 3 templates (2 of them UNPROVED), 5 direct forms, 2 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 4. Das Fragment F10: das Format und das Operationsbudget ----------------------------
#
# **Zwei Absenkungen, die keine Uebersetzungen sind.**
#
# `format` wird KEIN C-Verbund -- Fuellung und Bitreihenfolge sind in C implementierungsoffen,
# und ein Format ist genau eine Zusage ueber BYTES. Es wird ein Bytezeiger mit
# Zugriffsfunktionen in der ERKLAERTEN Reihenfolge, plus EINER Gueltigkeitsfunktion aus den
# `where`-Klauseln. *Der gemessene Bestand schreibt genau das von Hand: `be32(data, n)?`.*
#
# `retry ... bounded 65536 ops` ist ein OPERATIONSBUDGET, kein Schleifenzaehler. Geteilt durch
# die Kosten eines Durchgangs (der Kostenpass rechnet sie) ergibt das 21845 Durchgaenge.
schneide "$W/dokumente/FRAGMENTE.md" "module caprock::dtb" > "$ARB/f10.gab"
if ! grep -q "format DtbKopf" "$ARB/f10.gab"; then
    echo "== EMISSION: F10 NICHT GESCHNITTEN =="; exit 1
fi
TREIBER10='#include <stdio.h>
#include <stdlib.h>
#include "@ERZEUGT@"
static int rufe;
uint32_t naechstes_token(const DtbKopf *k, uint32_t pos) { (void)k; (void)pos; rufe++; return 1; }
_Noreturn void baum_unlesbar(void) { printf(" UEBERLAUF"); exit(0); }
int main(void) {
    static const uint8_t gut[16]    = { 0xd0,0x0d,0xfe,0xed, 0,0,0,64, 0,0,0,40, 0,0,0,50 };
    static const uint8_t falsch[16] = { 0xde,0xad,0xbe,0xef, 0,0,0,64, 0,0,0,40, 0,0,0,50 };
    /* Der Cast steht im TREIBER und nicht im Erzeugnis: seit ein `format` Schreiber hat
     * (2026-08-20), traegt seine Sicht `uint8_t *`. Wer eine Sicht ueber ein `const`-Feld
     * baut, sagt hier selbst, dass er sie nur liest -- und `ptr<normal, r>` sagt es auf der
     * Gabbro-Seite, wo M3 es haelt. */
    DtbKopf a = { (uint8_t *)gut, 64 }, b = { (uint8_t *)falsch, 64 },
            c = { (uint8_t *)gut, 8 }, d = { (uint8_t *)gut, 20 };
    rufe = 0;
    unsigned n = kerne_zaehlen(&a);
    printf("%d %d %d %d %u %d\n",
           (int)DtbKopf_gueltig(&a), (int)DtbKopf_gueltig(&b),
           (int)DtbKopf_gueltig(&c), (int)DtbKopf_gueltig(&d), n, rufe);
    return 0;
}
'
#    Erwartet:
#      1  -- der gute Kopf ist gueltig: Magie stimmt, beide Versaetze liegen im Puffer
#      0  -- **die Magie ist die Zusage, und `endian big` ist der Grund**: dieselben Bytes
#            klein gelesen ergaeben etwas anderes
#      0  -- ein Puffer kuerzer als der Kopf faellt an `v->len < 16`
#      0  -- und DAS ist die eigentliche `where`-Klausel: der Kopf passt, aber `off_struct`
#            zeigt hinter den Puffer. *Danach braucht kein Zugriff mehr eine Laengenpruefung.*
#      0  -- `kerne_zaehlen` liefert seine Null
#     65  -- **die Durchgaenge, und die Zahl ist vorhergesagt worden**: `narrow tiefe to
#            0 ..< 64` traegt 64 Durchgaenge, der 65. Test faellt. Nicht 21845 -- das
#            Operationsbudget ist die WEITERE Schranke, nicht die engere
#    **Die Sprechprobe dreht die Bytereihenfolge im LESER**, nicht seinen Namen. Der erste
#    Versuch ersetzte `gabbro_be32` durch `gabbro_le32` -- und traf damit Definition UND
#    Rufort, benannte die Funktion also bloss um. *Ein Gift, das nichts aendert, ist keines,
#    und die Probe hat es gemeldet.*
lauf "fragment10" "$ARB/f10.gab" "$TREIBER10" "1 0 0 0 0 65" \
     's/(uint32_t)p\[0\] << 24/(uint32_t)p[3] << 24/' \
     "1 assumptions (0 of them NOT FALSIFIABLE), 2 templates (0 of them UNPROVED), 7 direct forms, 2 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 4b. Das Fragment F2: die VT-d-Einheit, und sie kommt aus dem VERVOLLSTAENDIGTEN Korpus --
#
# **Das ist die erste Absenkungspflicht, die nicht mehr `gap` ist.** F7, F8 und F10 waren
# schon Programme und liessen sich aus dem eingefrorenen Korpus schneiden. F2 nicht: fuenf
# `reserved`-Felder fehlten, und ohne sie sagt kein `format`, welche Bits ueberhaupt
# EXISTIEREN. *Ein Ausschnitt ist kein Programm* -- die fehlenden Zeilen stehen jetzt in
# `messung/fragmente/F02.gab`, und nichts sonst steht dort anders.
#
# **Und genau das wird hier GEPRUEFT, nicht behauptet.** Der eingefrorene Block wird
# geschnitten und gegen die Arbeitsfassung gehalten: *keine Zeile darf fehlen.* Wer eine
# Absage wegdefiniert, statt eine Deklaration zu ergaenzen, faellt an dieser Stelle -- sonst
# waere die Vervollstaendigung ein Verschieben des Massstabs und keine Messung.
schneide "$W/dokumente/FRAGMENTE.md" "device Vtd" > "$ARB/f2-ausschnitt.gab"
if ! grep -q "device Vtd(base : Pa) at mmio" "$ARB/f2-ausschnitt.gab"; then
    echo "== EMISSION: F2 NICHT GESCHNITTEN -- der Waechter misst seine eigene Ablage =="
    exit 1
fi
#
# **Und die Vergleichsfunktion steht als FUNKTION da, weil sie zweimal gebraucht wird:**
# einmal fuer F02 und einmal fuer die Sprechprobe darunter. *Ein Waechter, den niemand hat
# fallen sehen, ist eine Verzierung* (R11) -- und dieser hier WAR eine: der erste Anlauf
# schrieb `if diff … | grep -q '^<'`, und `set -o pipefail` (Zeile 28) gibt dann den
# Rueckgabewert von `diff` weiter. **`diff` meldet 1, sobald sich irgendetwas unterscheidet
# -- und ergaenzt wurde ja etwas.** Damit war die Bedingung immer falsch, und eine
# entfernte Registerzeile ging glatt durch. *Gefunden, indem eine entfernt wurde.*
if [ -n "$(verlorene_zeilen "$ARB/f2-ausschnitt.gab" "$W/messung/fragmente/F02.gab")" ]; then
    echo "== EMISSION: F02.gab hat eine Zeile des eingefrorenen Ausschnitts VERLOREN =="
    echo "  Ergaenzen ist erlaubt, weglassen nicht. Was hier fehlt:"
    verlorene_zeilen "$ARB/f2-ausschnitt.gab" "$W/messung/fragmente/F02.gab" | head -10
    exit 1
fi
# Die Sprechprobe: eine Fassung, der eine Zeile FEHLT, muss auffallen.
grep -v "reg IQH  : u64 @0x080 class r" "$W/messung/fragmente/F02.gab" > "$ARB/f2-kurz.gab"
if [ -z "$(verlorene_zeilen "$ARB/f2-ausschnitt.gab" "$ARB/f2-kurz.gab")" ]; then
    echo "== EMISSION: Sprechprobe F2 haelt nicht -- eine entfernte Ausschnittzeile faellt"
    echo "             nicht auf. Dieser Vergleich misst NICHTS. =="
    exit 1
fi
echo "  (F2: der eingefrorene Ausschnitt steht vollstaendig in der Arbeitsfassung"
echo "       -- und eine fehlende Zeile faellt auf, Sprechprobe ok)"
#
# **Die Frage, die dieser Lauf beantwortet:** die VT-d-Einheit hat kein einziges
# `fn` -- sie ist eine Registerkarte, ein Bankenrechenwerk und fuenf Formate. Rechnet das
# erzeugte C dieselben ADRESSEN aus, die `vtd.rs` von Hand rechnet, und liest es dieselben
# BITS?
TREIBER2='#include <stdio.h>
#include "@ERZEUGT@"
_Alignas(16) static uint8_t mmio[4096];
static void le64(uint8_t *p, uint64_t v) { for (int i = 0; i < 8; i++) p[i] = (uint8_t)(v >> (8 * i)); }
int main(void) {
    Vtd d = { mmio };
    /* CAP.FRO @[33:24] = 32 -> die Aufzeichnungsbank liegt bei 32 * 16 = 512.
     * ECAP.IRO @[17:8] = 16 -> der IOTLB-Satz liegt bei 16 * 16 = 256. */
    *(volatile uint64_t *)(mmio + 0x008) = (uint64_t)32 << 24;
    *(volatile uint64_t *)(mmio + 0x010) = (uint64_t)16 << 8;
    *(volatile uint64_t *)(mmio + 560) = 0x1000000u;   /* FRR[3].FR_LO -- 512 + 3 * 16 */
    *(volatile uint64_t *)(mmio + 568) = (uint64_t)0x0100 | ((uint64_t)1 << 28)
                                       | ((uint64_t)6 << 32) | ((uint64_t)2 << 60)
                                       | ((uint64_t)1 << 63);
    *(volatile uint64_t *)(mmio + 576) = 0x99000u;     /* FRR[4].FR_LO -- eine Schrittweite weiter */
    *(volatile uint64_t *)(mmio + 264) = (uint64_t)7 << 32;  /* IOTLB[0].CMD.DID = 7 */
    /* Falle 4: GSTS traegt RTPS. `mirrors GCMD from GSTS` traegt es in den GCMD-Schreibvorgang. */
    *(volatile uint32_t *)(mmio + 0x01c) = 1u << 30;
    Vtd_scharf_te(&d);
    uint32_t gcmd = *(volatile uint32_t *)(mmio + 0x018);
    /* Die GELESENEN Woerter gehen in die Formate -- die Kette Bank -> Wort -> Bitlage. */
    uint8_t lo[8], hi[8], schief[8];
    le64(lo, Vtd_FRR_FR_LO(&d, 3));
    le64(hi, Vtd_FRR_FR_HI(&d, 3));
    le64(schief, 0x12000u);
    FaultRecordLo flo = { lo, 8 };
    FaultRecordHi fhi = { hi, 8 };
    FaultRecordLo fs  = { schief, 8 };
    printf("%u %u %u %u %u %u %u %u %u %d %d %d\n",
        (unsigned)FaultRecordLo_input_addr(&flo),
        (unsigned)(Vtd_FRR_FR_LO(&d, 4) >> 12),
        (unsigned)(Vtd_IOTLB_CMD(&d, 0) >> 32),
        (unsigned)((gcmd >> 30) & 3u),
        (unsigned)FaultRecordHi_sid(&fhi),
        (unsigned)FaultRecordHi_typ(&fhi),
        (unsigned)FaultRecordHi_grund(&fhi),
        (unsigned)FaultRecordHi_at(&fhi),
        (unsigned)FaultRecordHi_f_bit(&fhi),
        (int)FaultRecordLo_gueltig(&flo),
        (int)FaultRecordLo_gueltig(&fs),
        (int)VtdFehler_AufzeichnungVoll);
    return 0;
}
'
#    Erwartet:
#   4096  -- **die Registerlage kommt aus einem GELESENEN Feld.** `bank FRR at CAP.FRO * 16`
#            rechnet 32 * 16 + 3 * 16 = 560; dort steht das Wort, und `input_addr @[63:12]`
#            liest daraus 0x1000. *`frr_off` (vtd.rs:442) rechnet dieselbe Adresse von Hand.*
#    153  -- `stride 16`: der naechste Satz liegt 16 Bytes weiter und nicht dort, wo eine
#            `struct`-Fuellung ihn haette. Ein Bankeintrag ist kein C-Verbund
#      7  -- dieselbe Rechnung mit dem ZWEITEN gelesenen Feld: ECAP.IRO * 16 + 8 = 264
#      3  -- **FALLE 4, und sie ist hier bezahlt.** GCMD ist kein Read-Modify-Write; ein
#            blosses `TE = 1` loeschte RTPS. `mirrors GCMD from GSTS` traegt Bit 30 mit --
#            beide Bits stehen, nicht nur das geschriebene. *Genau das misst das Gift: ohne
#            den Spiegel steht da 2.*
#    256  -- SID aus @[15:0]
#      1  -- TYPE aus @[29:28], und das ist die am 2026-08-19 KORRIGIERTE Lage: `@[13:12]`
#            haette mit `sid` ueberlappt
#      6  -- GRUND aus @[39:32]
#      2  -- AT aus @[61:60]
#      1  -- das F-Bit aus @63, also aus dem OBEREN Wort («B24»)
#      1  -- `FaultRecordLo_gueltig`: die `where`-Klausel haelt
#      0  -- und sie kann fallen. **Und was dabei auffiel, steht hier statt in einer Notiz:**
#            die Klausel `(input_addr & 0xfff) == 0` (FRAGMENTE.md:497) prueft das FELD,
#            nicht die Adresse -- @[63:12] ist bereits geschoben, die unteren zwoelf Bits
#            sind also gar nicht mehr da. *Der Ausschnitt sagt weniger, als er zu sagen
#            scheint; die Zeile bleibt trotzdem stehen, denn sie ist die des Menschen.*
#      9  -- `reason` traegt die DEKLARIERTE Zahl, nicht die Reihenfolge der Aufzaehlung
lauf "fragment2" "$W/messung/fragmente/F02.gab" "$TREIBER2" \
     "4096 153 7 3 256 1 6 2 1 1 0 9" \
     's/uint32_t _s = (\*(volatile uint32_t \*)(d->basis + 28));/uint32_t _s = 0;/' \
     "3 assumptions (1 of them NOT FALSIFIABLE), 3 templates (0 of them UNPROVED), 1 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 4b. «B22-nah»: ABWESENHEIT und ABSAGE sind zwei Antworten ---------------------------
#
# **Der Nachweis, dass die Luecke zu ist -- und er ist AUSGEFUEHRT, nicht behauptet.**
#
# Ein VT-d Fault Record hat drei Zustaende. Bis zum 2026-08-25 konnte ein `format` nur zwei
# davon sagen: `f_bit : u64 in 1 .. 1` WEIST das leere Register ab, statt „leer" zu melden --
# *„kein Fehler" und „Satz unlesbar" wurden dieselbe Antwort.* So steht es im eingefrorenen
# Ausschnitt (`FRAGMENTE.md`:505), und so hat es der Mensch geschrieben, dem die Sprache
# nichts anderes anbot.
#
# **Die Notation fehlte dabei nie** -- `pred = orpred` steht seit jeher in der Grammatik.
# Es fehlte ein `match`-Arm: `PredArt::Oder` fiel in `pred_c_format` durch das
# `_ => return None`, und der Erzeuger sagte `C001`.
#
# Die drei Zahlen unten sind die drei Zustaende, und dass sie sich UNTERSCHEIDEN ist der
# ganze Posten:
#
#      1  -- der Ring ist LEER (F-Bit 0): lesbar, kein Fehler
#      0  -- der Satz ist zu KURZ (4 Bytes): unlesbar
#      1  -- ein Fault mit Grund 6: lesbar, ein Fehler
#      0  -- F-Bit 1 mit Grund 0: der Satz behauptet einen Grund, den es nicht gibt
#
# *Zwei verschiedene Antworten auf „leer" und „unlesbar" -- vorher waren beide `0`.*
TREIBER22='#include <stdio.h>
#include "@ERZEUGT@"
static uint8_t puffer[8];
static void le64(uint8_t *p, uint64_t v) { for (int i = 0; i < 8; i++) p[i] = (uint8_t)(v >> (8 * i)); }
static int pruefe(uint64_t wort, uint32_t laenge) {
    le64(puffer, wort);
    FaultRecordHi r = { puffer, laenge };
    return FaultRecordHi_gueltig(&r) ? 1 : 0;
}
int main(void) {
    printf("%d ", pruefe(0, 8));                                             /* leer     */
    printf("%d ", pruefe((uint64_t)6 << 32 | (uint64_t)1 << 63, 4));         /* zu kurz  */
    printf("%d ", pruefe((uint64_t)6 << 32 | (uint64_t)1 << 63, 8));         /* Fault    */
    printf("%d\n", pruefe((uint64_t)1 << 63, 8));                            /* Grund 0  */
    return 0;
}'
# **Die Giftprobe nimmt genau die Disjunktion weg** und laesst die rechte Haelfte stehen.
# Danach ist „leer" wieder `0` -- also dieselbe Antwort wie „unlesbar", und der Vergleich
# faellt. *Ohne diese Sprechprobe wuerde der Lauf nicht messen, ob das `||` etwas tut.*
lauf "b22-abwesenheit" "$W/beispiele/51-abwesenheit-und-absage.gab" "$TREIBER22" \
     "1 0 1 0" \
     's/FaultRecordHi_f_bit(v) == 0 || //' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 1 templates (0 of them UNPROVED), 0 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 4c. Das Fragment F4: der virtio-Treiber, und er senkt seit dem 2026-08-26 ab -----------
#
# **Die letzte der sieben Absenkungen, die als UNERREICHBAR galt.** Die `at dma`-Absage war
# Axiomschicht: *„welche Barriere ein DMA-Zugriff verlangt, ist eine Aussage ueber das
# Speichermodell, und der Pruefer baut sie ausdruecklich nicht."* Richtig -- und damit war die
# Pflicht nicht durch Arbeit einloesbar, sondern nur durch eine Entscheidung.
#
# **Die Entscheidung ist dieselbe wie bei «B19»/«B38»/«B39» in K100.2: nicht erledigen,
# sondern beim NAMEN mit einer Sonde fuehren.** `at dma` senkt jetzt ab, wenn die Einheit
# `assume dma_kohaerent … falsifier …` erklaert -- und weigert sich sonst, mit einer Absage,
# die die fehlende Annahme NENNT. *Aus einer Wand wird eine Tuer.*
#
# Zwei Erzeugerluecken lagen darunter, und beide waren still:
#
#   * `Device::parameter` wurde geparst und von `emit.rs` NIE gelesen. `q.n` hatte keinen Typ,
#     und die Absage nannte den `let` statt `q.n`.
#   * **Ein Bankzugriff senkte zu einem Strukturfeld ab, das es nicht gibt** --
#     `q->USED_RING[s].id`. Die erzeugten Zugriffsfunktionen rief kein erzeugter Code.
#     *Kein Durchstich hat es gefangen, weil die einzige durchgestochene Einheit mit einer
#     Bank (F02) sie aus dem C-TREIBER liest.* Eine erzeugte Schnittstelle, die nur ein
#     handgeschriebener Rufer benutzt, wird von ihrem eigenen Korpus nicht gemessen.
#
# Die vier Zahlen unten pruefen genau das, was hier neu ist:
#
#     42  -- `AVAIL_RING[0].e` nach dem ersten `publish` -- der Bank-SETZER traegt
#      1  -- `AVAIL_IDX` danach: der umlaufende Zaehler ist gestiegen
#      7  -- `AVAIL_RING[1].e` nach dem zweiten -- `platz = AVAIL_IDX % q.n` benutzt den
#            GERAETEPARAMETER, und der faehrt im Griff mit
#     99  -- `poll_used` liest `USED_RING[3].id` durch die Zugriffsfunktion
schneide "$W/dokumente/FRAGMENTE.md" "device Virtq" > "$ARB/f4.gab"
if ! grep -q "device Virtq" "$ARB/f4.gab"; then
    echo "== EMISSION: F4 NICHT GESCHNITTEN =="; exit 1
fi
fehlende_f4() { diff "$1" "$2" | grep "^<" || true; }
if [ -n "$(fehlende_f4 "$ARB/f4.gab" "$W/messung/fragmente/F04.gab")" ]; then
    echo "== EMISSION: F04.gab hat eine Zeile des eingefrorenen Ausschnitts VERLOREN =="
    fehlende_f4 "$ARB/f4.gab" "$W/messung/fragmente/F04.gab" | head -10
    exit 1
fi
grep -v "reg USED_FLAGS  : u16 @0x200 class rw" "$W/messung/fragmente/F04.gab" > "$ARB/f4-kurz.gab"
if [ -z "$(fehlende_f4 "$ARB/f4.gab" "$ARB/f4-kurz.gab")" ]; then
    echo "== EMISSION: Sprechprobe F4 haelt nicht -- eine entfernte Ausschnittzeile faellt"
    echo "             nicht auf. Dieser Vergleich misst NICHTS. =="
    exit 1
fi
echo "  (F4: der eingefrorene Ausschnitt steht vollstaendig in der Arbeitsfassung"
echo "       -- und eine fehlende Zeile faellt auf, Sprechprobe ok)"
TREIBER4='#include <stdio.h>
#include "@ERZEUGT@"
_Alignas(16) static uint8_t ring[4096];
/* Der Ausgang des `retry`. Er steht als `extern fn … -> never` in der Einheit, also
 * schuldet ihn der Rufer -- und hier ist der Rufer der Treiber. Er wird NICHT genommen:
 * die Probe setzt `USED_IDX` so, dass die Schleife sofort austritt. */
_Noreturn void DeviceSilent(void) { for (;;) { } }
int main(void) {
    Virtq q = { .basis = ring, .n = 8 };
    publish(&q, 42);
    printf("%u ", (unsigned)Virtq_AVAIL_RING_e(&q, 0));
    printf("%u ", (unsigned)(*(volatile uint16_t *)(ring + 0x102)));
    publish(&q, 7);
    printf("%u ", (unsigned)Virtq_AVAIL_RING_e(&q, 1));
    Virtq_USED_RING_setz_id(&q, 3, 99);
    *(volatile uint16_t *)(ring + 0x202) = 5;
    printf("%u\n", poll_used(&q, 3));
    return 0;
}'
# **Das Gift nimmt dem Griff seinen Parameter.** `% q->n` wird `% 1`; danach ist `platz`
# immer 0, der zweite `publish` ueberschreibt den ersten Platz, und `s` zeigt auf 0 statt 3.
# *Ohne diese Sprechprobe wuerde der Lauf nicht messen, ob der Geraeteparameter etwas tut.*
lauf "fragment4" "$W/messung/fragmente/F04.gab" "$TREIBER4" \
     "42 1 7 99" \
     's/% q->n/% 1/g' \
     "2 assumptions (0 of them NOT FALSIFIABLE), 2 templates (0 of them UNPROVED), 7 direct forms, 3 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 5. Die Traversierung: die Schleife OHNE Laufzeitzaehler ----------------------------
#
# **Der Unterschied zu `retry` steht jetzt im C nebeneinander:**
#
#     traverse  ->  for (uint32_t i = 0; i < sizeof(...)/sizeof(...[0]); i++)
#     retry     ->  while (!(...)) { if (n >= SCHRANKE) { ausgang(); } n++; ... }
#
# Die Laufgrenze hier, der Wachhund dort -- und der Grund ist die Domaene: `slots of` ist
# durch Konstruktion endlich, die Bedingung eines `retry` haengt von der Welt ab. *Genau
# darum verlangt die Grammatik dort ein `on_exceeded` und hier keines.*
TREIBER19='#include <stdio.h>
#include "@ERZEUGT@"
int main(void) {
    static Werte w;
    for (unsigned i = 0; i < 16; i++) w.slots[i].aktiv = (i % 3 == 0);
    unsigned vorher = aktive_zaehlen(&w);
    aktive_loeschen(&w);
    unsigned nachher = aktive_zaehlen(&w);
    printf("%d %u %u %d\n",
           (int)(sizeof(w.slots) / sizeof(w.slots[0])), vorher, nachher,
           (int)w.slots[15].aktiv);
    return 0;
}
'
#    Erwartet:
#     16  -- die Domaenenschranke kommt aus `count NSLOTS`, nicht aus dem Rumpf
#      6  -- Slots 0,3,6,9,12,15 sind aktiv: **jeder Slot GENAU EINMAL besucht**. Eine
#            Traversierung, die einen ausliesse, zaehlte weniger; eine, die doppelt liefe,
#            mehr -- und der Zaehler ist auf `0 ..< 16` verengt, koennte also gar nicht ueber
#            16 hinaus
#      0  -- nach dem Loeschen ist keiner mehr aktiv
#      0  -- und der LETZTE Slot ist mitgeloescht: die Grenze ist `< n`, nicht `< n-1`
# **8 -> 7 direkte Formen am 2026-08-19.** Mit «H2.1» ist das `narrow` aus `beispiele/19`
# entfallen -- ein Zaehler erbt die Schranke seiner Domaene, und die Zeile war ein Ritual.
# *Eine direkte Form weniger heisst hier: eine Klempnereizeile weniger, nicht eine Luecke.*
lauf "beispiel19" "$W/beispiele/19-traversierung.gab" "$TREIBER19" "16 6 0 0" \
     's/; i++)/; i += 2)/' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 2 templates (0 of them UNPROVED), 7 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 6. Das Geraet: ein Register ist KEIN Feld ------------------------------------------
#
# Ein C-Verbund haette dieselbe Schwaeche wie beim `format`: die Versaetze stehen in der
# Deklaration, die Fuellung eines `struct` bestimmt der Uebersetzer. Dazu kommt hier, dass ein
# Registerzugriff **nicht wegoptimiert werden darf** -- `volatile` ist die eine Stelle, an der
# die Absenkung dem C-Uebersetzer etwas VERBIETEN muss.
#
#     r.AVAIL_IDX += 1;   ->   (*(volatile uint16_t *)(r->basis + 258)) += 1;
#
# **Und der Umlauf ist erklaert, nicht geduldet** («B32»): `u16 wrapping` senkt zu `uint16_t`
# ab, dessen Umlauf C definiert. Bei 0xffff geht es auf 0 -- genau das, was virtio meint.
TREIBER12='#include <stdio.h>
#include "@ERZEUGT@"
static uint8_t bank[512];
int main(void) {
    Ring r = { bank };
    *(volatile uint16_t *)(bank + 258) = 7;
    *(volatile uint16_t *)(bank + 260) = 64;
    vorruecken(&r);
    unsigned a = *(volatile uint16_t *)(bank + 258);
    *(volatile uint16_t *)(bank + 258) = 0xffff;
    vorruecken(&r);
    unsigned b = *(volatile uint16_t *)(bank + 258);
    unsigned c = *(volatile uint16_t *)(bank + 260);
    printf("%u %u %u %d\n", a, b, c, (int)sizeof(Ring));
    return 0;
}
'
#    Erwartet:
#      8  -- 7 + 1: der Zugriff trifft Versatz 0x102 und nichts daneben
#      0  -- **0xffff + 1 laeuft um**, und zwar mit Absicht: `u16 wrapping` («B32»)
#     64  -- das NACHBARREGISTER bei 0x104 ist unberuehrt geblieben
#      8  -- der Griff ist ein Zeiger, kein abgebildeter Registersatz: kein `struct` mit
#            Fuellung, ueber die der Uebersetzer entscheidet
lauf "beispiel12" "$W/beispiele/12-umlaufendes-register.gab" "$TREIBER12" "8 0 64 8" \
     's/+ 258/+ 260/' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 1 templates (0 of them UNPROVED), 2 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 7. FALLE 4: `mirrors`, und der Test misst genau die bezahlte Falle -----------------
#
# **Die Falle, in einem Satz:** `GCMD` ist kein Lese-Aendere-Schreib-Register. Wer ein Bit
# setzt, schreibt das GANZE Wort -- und jedes Zustandsbit, das er nicht mitschreibt, ist
# danach geloescht. Die mitzuschreibenden Bits stehen nicht in GCMD (es ist `class w`,
# unlesbar), sondern im Statusregister daneben.
#
#     mirrors GCMD from GSTS;   ->   write(GCMD, (read(GSTS) & ~geaendert) | neu)
#
# *Eine Zeile je Geraet, und sie ersetzt `GCMD_STATE_MASK` samt der Kommentarwand.*
TREIBER20='#include <stdio.h>
#include "@ERZEUGT@"
static uint8_t mmio[64];
#define GCMD (*(volatile uint32_t *)(mmio + 0x18))
#define GSTS (*(volatile uint32_t *)(mmio + 0x1c))
int main(void) {
    Einheit e = { mmio };
    /* Das Geraet meldet: die Uebersetzung laeuft bereits (TES, Bit 31). */
    GSTS = 1u << 31;
    GCMD = 0;
    Einheit_setze_rtp(&e);
    unsigned nach_rtp = GCMD;

    /* Und jetzt meldet es zusaetzlich RTPS (Bit 30). */
    GSTS = (1u << 31) | (1u << 30);
    GCMD = 0;
    Einheit_scharf_te(&e);
    unsigned nach_te = GCMD;

    printf("%d %d %d %d\n",
           !!(nach_rtp & (1u << 30)),   /* SRTP gesetzt */
           !!(nach_rtp & (1u << 31)),   /* TES MITGESCHRIEBEN -- das ist die Falle */
           !!(nach_te  & (1u << 31)),   /* TE gesetzt */
           !!(nach_te  & (1u << 30)));  /* RTPS mitgeschrieben */
    return 0;
}
'
#    Erwartet:  1 1 1 1
#      Die ERSTE und die DRITTE Zahl sagen, dass der Uebergang tut, was er sagt.
#      **Die ZWEITE und die VIERTE sind die Falle.** Ohne `mirrors` waeren sie 0: das
#      Zustandsbit, das niemand mitgeschrieben hat, waere geloescht -- und die Einheit haette
#      die Uebersetzung mitten im Betrieb abgeschaltet. *Genau dafuer hat der Bestand eine
#      Maske und eine Kommentarwand; hier ist es eine Zeile.*
lauf "beispiel20" "$W/beispiele/20-falle-vier.gab" "$TREIBER20" "1 1 1 1" \
     's/(_s \& /(0*_s \& /' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 2 templates (0 of them UNPROVED), 1 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"


# -- 8. «B7»: der Verbundwert, und der Test misst genau das, wofuer die Marken Pflicht sind --
#
# **Die Entscheidung, in einem Satz:** ein geschweiftes `P { a: 1 }` waere die erste
# Ausdrucksform gewesen, die mit `{` weitergeht -- an 76 Korpusstellen folgt ein `{` direkt
# auf einen Ausdruck, und ein falsch gesetzter Kontextschalter verliest sie ALLE still.
# Gewaehlt ist darum der markierte Ruf `P(a: …, b: …)`.
#
# **Und die Marken sind nicht Zierde.** `Completion` hat zwei `u32`-Felder; eine Reihung
# `Completion(k, n)` liesse sich vertauschen, ohne dass ein Typ dagegen spricht. Der Erzeuger
# uebersetzt die Marken zu BENANNTEN Bestimmern -- `(Completion){ .id = k, .len = n }` --,
# und damit steht die bewiesene Zusage `map fst zs = fs` im Erzeugnis statt nur im Pruefer.
TREIBER21='#include <stdio.h>
#include "@ERZEUGT@"
int main(void) {
    Completion c = fertig(5, 300);
    Marke m = markiere(9);
    printf("%u %u %u %u %d\n", c.id, c.len, laenge_von(5), m.wer, m.fertig ? 1 : 0);
    return 0;
}
'
#    Erwartet:  5 300 7 9 1
#      Die ersten beiden Zahlen sind die Falle: **vertauscht waeren sie `300 5`**, und kein
#      Typ haette etwas dagegen gehabt. Das Gift unten vertauscht genau die zwei Bestimmer.
lauf "beispiel21" "$W/beispiele/21-verbundwert.gab" "$TREIBER21" "5 300 7 9 1" \
     's/\.id = k, \.len = n/.id = n, .len = k/' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 1 templates (0 of them UNPROVED), 4 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"


# -- 9. K11.2.3: `release`/`acquire` senken ab -- und was der Test NICHT zeigen kann ------
#
# Bis zum 2026-08-17 weigerte sich der Erzeuger hier, mit diesem Grund: *„dass ein
# release-Speichern die Sichtbarkeit HERSTELLT, die die Paarung behauptet, ist eine Aussage
# ueber das Speichermodell."* **Der Grund stimmt weiter -- er ist nur kein Grund fuer eine
# Weigerung.** Die Aussage steht als A10 in der Axiomschicht, gebucht als NICHT falsifizierbar.
#
# **Und die Grenze dieses Tests gehoert hierher, nicht in eine Fussnote:** ein Differenztest
# kann die ABWESENHEIT eines Rennens nicht zeigen. Ein gruener Lauf sagt nur, dass die
# Umordnung diesmal ausblieb -- woertlich der Satz, mit dem A10 als nicht falsifizierbar
# gebucht ist.
#
# *Was er zeigt, ist die STRUKTURELLE Zusage: im C steht die Ordnung, die die Quelle sagte,
# und nicht das Vorgabemodell von `_Atomic`.* Das Gift unten ersetzt sie durch `relaxed`.
# **Der Treiber deklarierte `struct Bericht` SELBST, und das war der Befund** (2026-08-25).
# Das Gabbro-Programm nannte den Typ an drei Stellen und erklaerte ihn nirgends; `N040` hat
# es gefunden. Der Durchstich lief trotzdem gruen -- *weil dieser Treiber nachlieferte, was
# der Erzeuger nicht bekommen hatte.* Jetzt erklaert die `.gab` ihn, der Erzeuger schreibt
# ihn, und der Treiber nimmt ihn wie jeden anderen erzeugten Typ entgegen.
TREIBER14='#include <stdio.h>
#include "@ERZEUGT@"
int main(void) {
    Bericht b = { 0 };
    printf("%d ", abholen(&b) ? 1 : 0);
    anstossen(&b);
    printf("%d\n", abholen(&b) ? 1 : 0);
    return 0;
}
'
#    Erwartet:  0 1
#      Vor dem Anstossen liest die Gegenseite `false`, danach `true` -- die Paarung traegt
#      ueber eine ZWISCHENFUNKTION (`anstossen` publiziert selbst nicht).
#
#    **Das Gift vertauscht den WERT, nicht die Ordnung, und das ist kein Versehen.** Ein
#    erster Versuch ersetzte `memory_order_release` durch `relaxed` -- und die Sprechprobe
#    meldete UEBERSEHEN: das veraenderte Erzeugnis liefert dasselbe. *Natuerlich tut es das.*
#    Ein einlaeufiger Test kann eine Ordnung nicht sehen.
#
#    > **Genau das hat `PLAN.md` (K11.2.3) vorab gesagt:** ein Differenztest kann die
#    > ABWESENHEIT eines Rennens nicht zeigen. Die Ordnung im C wird darum ANDERSWO gehalten
#    > -- durch das gebuchte Zeugnis (Stufe 5), eine Sprechprobe in `rechenwerk.rs` und zwei
#    > Mutationen. *Hier faellt der Wert; die Ordnung faellt dort.*
lauf "beispiel14" "$W/beispiele/14-paarung-ueber-zwischenfunktion.gab" "$TREIBER14" "0 1" \
     's/atomic_store_explicit(&FERTIG, true,/atomic_store_explicit(\&FERTIG, false,/' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 1 templates (0 of them UNPROVED), 6 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"


# -- 12. «F»: Gleitkomma -- und der Test misst, dass das C WIRKLICH RECHNET -----------------
#
# **Die Zeugniszeile behauptet etwas ueber die Aufrufkonvention.** Eine Zeile ueber eine
# Eigenschaft, die niemand ausgefuehrt hat, waere die teuerste Fassung desselben Fehlers, den
# dieser Ordner an `rank` und `ensures` schon zweimal bezahlt hat.
#
# Gemessen wird die Klemmung an drei Stellen, darunter NaN -- der Fall, um dessentwillen die
# ganze Faktenmaschine gebaut wurde. `0.0/0.0` erzeugt ihn, ohne dass ein Literal ihn nennt.
TREIBER26='#include <stdio.h>
#include "@ERZEUGT@"
int main(void) {
    double null = 0.0;
    printf("%.1f %.1f %.1f %.1f %.1f\n",
           klemmen(0.25), klemmen(2.5), nur_endlich(null/null),
           klemmen_ohne_narrow(0.75), voll());
    return 0;
}
'
#    Erwartet:  0.2 0.5 0.5 0.8 1.0
#      Das ZWEITE ist der Ausstieg: `klemmen` KLEMMT nicht, es verengt oder steigt aus --
#      2.5 liegt nicht in [0,1], also gibt es `HALB`. *Die erste Fassung dieses Treibers
#      erwartete 1.0 und hatte damit die Sprache falsch gelesen, nicht den Code.*
#
#      Das DRITTE ist die Falle: `0.0/0.0` ist NaN, und `isfinite` faengt es -- der
#      `else`-Zweig gibt `HALB`. Das Gift dreht die Pruefung um; dann laeuft NaN durch und
#      `%.1f` druckt `nan` oder `-nan`. **Kein Literal nennt NaN** -- es entsteht.
lauf "beispiel26" "$W/beispiele/26-gleitkomma.gab" "$TREIBER26" "0.2 0.5 0.5 0.8 1.0" \
     's/if (!isfinite(x))/if (isfinite(x))/' \
     "2 assumptions (0 of them NOT FALSIFIABLE), 0 templates (0 of them UNPROVED), 6 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 10. `accumulates`: eine Zelle je Kern, und der Test misst die SCHABLONE ---------------
#
# **Der Beweis lag VOR dem Konstrukt** (`beweise/Accumulates_Monoid.thy`, 2026-08-17), und er
# hat die Falle ausgespuelt, die hier drinsteckt: `min` hat als Neutrales das MAXIMUM des
# Typs, nicht die Null. Ein Erzeuger, der mit `0` anfaengt, zieht jedes `min` auf null.
#
# Der Treiber setzt drei Kerne und liest -- **das ist der RUHEPUNKT**, und nur dort sagt die
# Schablone eine Gleichheit mit einem atomaren RMW zu.
TREIBER23='#include <stdio.h>
static unsigned aktueller_kern = 0;
unsigned gabbro_kern(void) { return aktueller_kern; }
#include "@ERZEUGT@"
int main(void) {
    aktueller_kern = 0; melde_hoch(7);  melde_tief(7);  fehler_melden(1);
    aktueller_kern = 2; melde_hoch(19); melde_tief(3);  fehler_melden(1);
    aktueller_kern = 3; melde_hoch(4);  melde_tief(11); fehler_melden(1);
    printf("%llu %llu %u\n",
           (unsigned long long)hoechster(), (unsigned long long)tiefster(), fehler());
    return 0;
}
'
#    Erwartet:  19 3 3
#      Das MITTLERE ist die Falle: `min` ueber drei Kernen, waehrend 61 Zellen UNBERUEHRT
#      sind. **Der erste Lauf lieferte dort 0** -- C nullt statische Felder, und null ist
#      nicht das Neutrale von `min`. Der Beweis hatte den Satz (`min_ist_monoid_mit_top`),
#      die Absenkung hatte ihn nicht.
#
#      Die Loesung ist die DARSTELLUNG: `min` speichert das Komplement und faltet mit `max`.
#      Das Gift nimmt die Ruecknahme heraus -- dann steht dort das Komplement statt der Zahl.
lauf "beispiel23" "$W/beispiele/23-akkumulatoren.gab" "$TREIBER23" "19 3 3" \
     's/return (uint64_t)~z;/return z;/' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 1 templates (0 of them UNPROVED), 4 direct forms, 3 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"


# -- 11. «B24» entschieden: der IP-Kopf, an einem echten Paket gemessen ------------------
#
# **Die Bitlage liegt im EIGENEN WORT des Feldes**, und das Wort wird zuerst in der erklaerten
# Bytereihenfolge gelesen. Der Treiber legt einen echten IPv4-Kopf hin und liest ihn zurueck.
#
# *Das Gift dreht die Schiebung um -- dann liest `version` die unteren vier Bits statt der
# oberen, und aus 4 wird 5.*
TREIBER24='#include <stdio.h>
#include "@ERZEUGT@"
static const unsigned char paket[20] = {
    0x45, 0x28, 0x00, 0x54,      /* v=4 ihl=5 | dscp=10 ecn=0 | len=84 */
    0x1c, 0x46, 0x40, 0x00,      /* id | flags=2 frag=0            */
    0x40, 0x06, 0xb1, 0xe6,      /* ttl=64 proto=6 | pruefsumme    */
    0xac, 0x10, 0x0a, 0x63,
    0xac, 0x10, 0x0a, 0x0c
};
int main(void) {
    IpKopf k = { (uint8_t *)paket, 20 };
    printf("%u %u %u %u %u %u %u\n",
           IpKopf_version(&k), IpKopf_ihl(&k), IpKopf_dscp(&k), IpKopf_ecn(&k),
           IpKopf_flags(&k), IpKopf_fragment(&k), IpKopf_protokoll(&k));
    return 0;
}
'
#    Erwartet:  4 5 10 0 2 0 6
#      Die ERSTEN ZWEI sind die Falle: `version` und `ihl` teilen Byte 0. Wer die Schiebung
#      vertauscht, liest 5 und 4 -- beides gueltige Zahlen, und kein Typ sagt etwas.
lauf "beispiel24" "$W/beispiele/24-ip-kopf.gab" "$TREIBER24" "4 5 10 0 2 0 6" \
     's/>> 4) & 15u/>> 0) \& 15u/' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 1 templates (0 of them UNPROVED), 0 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 12. «C1»: die Freiliste -- der SONDERWERT, und der Beweis lag seit zwei Tagen da ------
#
# `option index into T` senkt zu einem Sonderwert ab, und der Sonderwert ist `count` selbst
# (`beweise/Option_Sonderwert.thy`, `sonderwert_ausserhalb`/`kodiere_injektiv`). Bis zum
# 2026-08-19 weigerte sich der Erzeuger dafuer -- **der Satz stand da und kein Erzeuger
# benutzte ihn**, und die Freiliste war die Datei, die daran haengenblieb.
#
#     static mut frei : option index into Halde = None;   ->   static uint32_t frei = Halde_NONE;
#     match frei { Some(i) => …, None => … }              ->   if (_o1 != Halde_NONE) …
#
# **Der Treiber laeuft die Liste einmal leer und einmal voll**, und der letzte Wert ist der,
# auf den es ankommt: nach dem letzten `belegen` ist der Kopf `Halde_NONE` -- *nicht 0, nicht
# irgendein Slot.* Genau das ist der Unterschied zwischen einer Option und einem `uint32_t`.
#
# *Das Gift setzt den Sonderwert auf 0 -- dann ist `None` von `Some(0)` nicht mehr zu
# unterscheiden, und die Liste haelt sich fuer leer, sobald Slot 0 der Kopf ist.*
TREIBER27='#include <stdio.h>
#include "@ERZEUGT@"
extern uint32_t frei_lesen(void);
int main(void) {
    static Halde h;
    /* Drei Plaetze einhaengen: 7, dann 3, dann 0 -- der Kopf ist zuletzt 0. */
    freigeben(&h, 7);
    freigeben(&h, 3);
    freigeben(&h, 0);
    uint32_t a = belegen(&h);
    uint32_t b = belegen(&h);
    uint32_t c = belegen(&h);
    uint32_t d = belegen(&h);      /* jetzt ist sie leer: der Sonderwert */
    printf("%u %u %u %d %d\n", a, b, c, (int)(d == 1024u), (int)(d == 0u));
    return 0;
}
'
#    Erwartet:  0 3 7  -- LIFO: zuletzt eingehaengt, zuerst herausgenommen
#                    1  -- die leere Liste liefert `Halde_NONE`, und das ist `count` = 1024
#                    0  -- und sie liefert NICHT 0. **Das ist die ganze Aussage des
#                          Sonderwerts:** `None` ist kein gueltiger Index, und Slot 0 ist
#                          einer. Wer den Sonderwert auf 0 legt, dreht diese zwei Zahlen um.
lauf "beispiel27" "$W/beispiele/27-freiliste.gab" "$TREIBER27" "0 3 7 1 0" \
     's/#define Halde_NONE (1024)/#define Halde_NONE (0)/' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 2 templates (1 of them UNPROVED), 5 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 13. «C2»: der markierte Wert -- `struct { marke; union }`, und `-Wswitch` liest mit ---
#
# Ein `tagged type` war bis zum 2026-08-19 reine Prueferangelegenheit: `D005` verlangt das
# erschoepfende `match` ohne Sammelzweig, und ABGESENKT wurde er gar nicht. Die Absenkung ist
# `struct { marke; union { … } }`, und die eine Entscheidung darin ist der Typ der Marke.
#
# **Sie wird ein `enum`, damit `switch` OHNE `default` unter `-Wswitch` ein zweiter Leser von
# `D005` ist** -- derselbe Bau wie `-Wmissing-field-initializers` beim Verbundkonstruktor.
# Stufe 3 dieses Laufs ist damit nicht nur eine Uebersetzung, sondern eine Pruefung: ein
# fehlender Fall waere hier ein Fehler, kein stiller Durchfall.
#
# *Das Gift vertauscht zwei Glieder der Vereinigung -- dann liest `Kurz` das Wort von `Lang`.
# Beides sind gueltige Zahlen, und kein C-Typ spricht dagegen: genau die Klasse, gegen die
# die Marke steht.*
TREIBER34='#include <stdio.h>
#include <inttypes.h>
#include "@ERZEUGT@"
int main(void) {
    Nachricht leer = { .marke = Nachricht_Leer, { 0 } };
    Nachricht kurz = { .marke = Nachricht_Kurz, { .Kurz = 41u } };
    /* Passt NICHT in 32 Bit -- wer das falsche Glied liest, bekommt 2. */
    Nachricht lang = { .marke = Nachricht_Lang, { .Lang = 4294967298ull } };
    Nachricht antw = { .marke = Nachricht_Antwort, { .Antwort = 7u } };
    static Anfragen a;
    a.slots[3].was = lang;
    printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %u %u %" PRIu64 " %d\n",
           gewicht(leer), gewicht(kurz), gewicht(lang), gewicht(antw),
           art_von(leer), art_von(lang),
           gewicht_im_slot(&a, 3),
           (int)(sizeof(a.slots) / sizeof(a.slots[0])));
    return 0;
}
'
#    Erwartet:  0 41 4294967298 7  -- je Variante ihr EIGENES Glied der Vereinigung
#                          0 2     -- und die Marke allein, ohne die Nutzlast zu lesen
#                4294967298       -- dasselbe `switch` ueber einem Slotfeld
#                         8       -- `count NANFRAGEN` traegt das Feld
#
# *Das Gift laesst den `Lang`-Zweig das `Kurz`-Glied lesen. Es uebersetzt, es rechnet -- und
# es liefert 2 statt 4294967298. Genau die Klasse, gegen die eine Marke steht: ohne sie ist
# jedes Glied so gut wie jedes andere.*
lauf "beispiel34" "$W/beispiele/34-markierter-wert.gab" "$TREIBER34" \
     "0 41 4294967298 7 0 2 4294967298 8" \
     's/= m.last.Lang;/= m.last.Kurz;/' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 1 templates (0 of them UNPROVED), 6 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 14. «C3c»: die Gruppe erzeugt NICHTS -- und die Tabelle IST der Speicher -----------
#
# **Die billigste Zeile des ganzen Plans, und sie ist trotzdem eine Aussage:** eine `group`
# ist die Verbindungsinvariante ueber zwei Traegern, und was sie zur Laufzeit kostet, ist
# null. Ihr Sperrabdruck (`U001`-`U006`) wird zur Uebersetzungszeit nachgerechnet -- W6.
#
# **Und der Lauf hat sofort etwas anderes freigelegt:** `Endpunkte.slots[e]` senkte zu
# `Endpunkte->slots[e]` ab -- ein Pfeil auf einen Typnamen. Es war an `cc` delegiert und
# folgenlos, solange jede solche Datei aus einem anderen Grund `C001` sagte. *Seit «C3c»
# sagt diese hier keinen mehr.* `beispiele/09` nennt die Regel selbst: die Tabelle IST der
# Speicher, ihr Name der Ort.
#
# *Das Gift nimmt die INNERE Sperre weg. Der Rumpf rechnet dasselbe -- aber der Zaehler, den
# der Treiber fuehrt, bleibt stehen: eine Gruppe verlangt BEIDE Sperren, und das ist die
# Aussage, um derentwillen `U003` existiert.*
TREIBER17='#include <stdio.h>
#include "@ERZEUGT@"
static int genommen_punkte = 0, genommen_plan = 0, offen = 0;
void PUNKTE_nimm(void) { genommen_punkte++; offen++; }
void PUNKTE_gib(void)  { offen--; }
void PLAN_nimm(void)   { genommen_plan++; offen++; }
void PLAN_gib(void)    { offen--; }
int main(void) {
    einreihen(5, 9);
    printf("%u %u %d %d %d %d\n",
           Endpunkte_speicher.slots[5].wartet,
           Faeden_speicher.slots[9].gruende,
           genommen_punkte, genommen_plan, offen,
           (int)(sizeof(Endpunkte_speicher.slots) / sizeof(Endpunkte_speicher.slots[0])));
    return 0;
}
'
#    Erwartet:  9 1  -- beide Traeger geschrieben, jeder ueber SEINEN Speicher
#                1 1 -- beide Sperren genau einmal genommen
#                  0 -- und beide wieder gegeben: kein Pfad laesst eine stehen
#                 64 -- `count NPUNKTE` traegt das Feld
lauf "beispiel17" "$W/beispiele/17-gruppe-ueber-zwei-sperren.gab" "$TREIBER17" "9 1 1 1 0 64" \
     's/        PLAN_nimm();//' \
     "1 assumptions (1 of them NOT FALSIFIABLE), 2 templates (1 of them UNPROVED), 3 direct forms, 2 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 15. «C3b»: RCU -- und der Unterschied zur Sperre ist das, was FEHLT ----------------
#
# `rcu` senkt ab wie ein `lock`: zwei Prototypen, keine Zeile Rumpf. **Und genau daran wird
# sichtbar, was RCU ist** -- es gibt kein `_nimm`, das jemanden aufhaelt. Der Lesebereich
# wird betreten und verlassen; ausgeschlossen wird niemand. *Die Leseseite braucht die
# Schreibersperre nicht, und das ist die ganze Substanz des Konstrukts.*
#
# Der Treiber zaehlt beide Seiten mit und misst die Aussage direkt:
#
#   * `lesen` betritt den Lesebereich und nimmt KEINE Sperre,
#   * `setzen` und `zurueckgeben` nehmen die Schreibersperre und betreten KEINEN Lesebereich,
#   * und der Lesebereich wird auf JEDEM Pfad verlassen -- auch dem mit `return` darin.
#
# *Das Gift streicht das Verlassen am Rueckkehrpfad. Der Rumpf rechnet dasselbe, und der
# Zaehler bleibt offen stehen -- woertlich die Klasse, gegen die die Austrittsliste steht.*
TREIBER31='#include <stdio.h>
#include "@ERZEUGT@"
static int drin = 0, tiefstand = 0, schreibsperre = 0;
void BACCT_lese_start(void) { drin++; }
void BACCT_lese_ende(void)  { drin--; if (drin < tiefstand) tiefstand = drin; }
void SCHREIBER_nimm(void)   { schreibsperre++; }
void SCHREIBER_gib(void)    { schreibsperre--; }
int main(void) {
    setzen(4, 55);
    unsigned w = lesen(4);
    zurueckgeben(4);
    printf("%u %d %d %d %d\n", w, drin, tiefstand, schreibsperre, (int)(frei == 4u));
    return 0;
}
'
#    Erwartet:  55 -- der Leser sieht, was der Schreiber unter seiner Sperre schrieb
#                0 -- der Lesebereich ist wieder zu, obwohl der Rumpf ein `return` enthaelt
#                0 -- und er wurde nie ZWEIMAL verlassen (der Tiefstand bleibt bei null)
#                0 -- die Schreibersperre ist gegeben
#                1 -- `reclaims frei` steht als `Some(i)` im Kopf der Freiliste
lauf "beispiel31" "$W/beispiele/31-rcu.gab" "$TREIBER31" "55 0 0 0 1" \
     's/^        BACCT_lese_ende();$//' \
     "1 assumptions (0 of them NOT FALSIFIABLE), 2 templates (1 of them UNPROVED), 4 direct forms, 2 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 16. «C4»: der Tausch, und die ORDNUNG ist die Falle --------------------------------
#
# Ein compare-exchange ist `publishes` und `awaits` in EINEM Befehl. Die Absenkung ist
# `atomic_compare_exchange_strong_explicit` mit der **deklarierten** Ordnung -- und genau hier
# hat dieser Erzeuger schon einmal geschummelt: der Mutationskatalog fuehrt
# `veroeffentlichung-nimmt-die-vorgabeordnung`, weil ein `=` auf einem `_Atomic` in C
# `seq_cst` bedeutet.
#
# **Was dieser Lauf NICHT zeigen kann, steht hier, damit es niemand hineinliest:** eine
# Ordnung ist an einem Faden nicht messbar. Der Differenztest misst die LOGIK des Tausches
# (er gelingt genau dann, wenn der alte Wert der erwartete war); dass die Ordnung die
# deklarierte ist, haelt eine Probe im Rechenwerk und eine Mutation daneben.
#
# *Das Gift setzt den erwarteten Wert auf den neuen. Dann gelingt die Uebernahme nie, und die
# erste Zahl kippt -- der Vergleich ist die ganze Substanz der Form.*
TREIBER35='#include <stdio.h>
#include "@ERZEUGT@"
int main(void) {
    int a = besitz_nehmen(7);      /* frei -> gelingt   */
    int b = besitz_nehmen(9);      /* belegt -> scheitert */
    int c = besitz_geben(9);       /* nicht seiner -> scheitert */
    int d = besitz_geben(7);       /* seiner -> gelingt */
    printf("%d %d %d %d %u\n", a, b, c, d,
           (unsigned)atomic_load_explicit(&BESITZER, memory_order_acquire));
    return 0;
}
'
#    Erwartet:  1 0 0 1  -- der Tausch gelingt genau dann, wenn der ALTE Wert der erwartete war
#                    0   -- und am Ende ist der Platz wieder frei
lauf "beispiel35" "$W/beispiele/35-tausch.gab" "$TREIBER35" "1 0 0 1 0" \
     's/uint32_t _cx1 = (uint32_t)(NIEMAND);/uint32_t _cx1 = (uint32_t)(f);/' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 0 templates (0 of them UNPROVED), 5 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# **`wrapping` heisst DEFINIERT -- und diese Einheit misst genau das** (2026-08-20).
#
# 50000 * 50000 = 2 500 000 000, modulo 2^16 sind das 63744. Der Wert kam auch VOR der
# Reparatur heraus -- und war nicht zugesichert: UBSan meldete
# *„signed integer overflow: 50000 * 50000 cannot be represented in type 'int'"*, weil die
# ganzzahlige Aufwertung beide Seiten auf `int` hebt.
#
# > Stufe 6 ist hier die Stufe, auf die es ankommt. Stufe 4 haette gruen gemeldet.
#
# Das Gift macht aus der Multiplikation eine Addition -- 50000 + 50000 = 100000, modulo
# 2^16 sind das 34464. *Ein Gift, das denselben Wert liefert, misst nichts.*
TREIBER37='#include <stdio.h>
#include "@ERZEUGT@"
int main(void) {
    Zaehler t = {{{0}}};
    t.slots[1].a = 50000;
    quadriere(&t, 1);
    printf("%u\n", (unsigned)t.slots[1].a);
    return 0;
}
'
lauf "beispiel37" "$W/beispiele/37-umlauf-rechnet.gab" "$TREIBER37" "63744" \
     's/) \* (uint32_t)/) + (uint32_t)/' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 2 templates (0 of them UNPROVED), 2 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 19. «B41b»: der BAUMDURCHLAUF, und er ist die Einheit, auf die es hier ankommt ------
#
# **Uebersetzbar ist nicht richtig.** Der Kopf dieser Datei sagt es seit jeher -- *ein
# Erzeuger, der uebersetzbares C liefert, das etwas anderes rechnet, ist schlimmer als einer,
# der nichts liefert*. Und der Abstieg an `tree { child, sibling, parent }` ist genau die
# Form, bei der das zutreffen koennte: **kein Stapel, eine Marke fuer „von unten gekommen",
# Nachordnung, und jede Kante gelesen, BEVOR der Rumpf sie zerstoeren darf.**
#
# Vier Zahlen, und jede trennt eine andere Fehlform:
#
#      7  -- ALLE Nachfahren gesehen. Ein Abstieg, der an `parent` statt an `child`
#            hinunterliefe, saehe keinen einzigen.
#      0  -- keiner ZWEIMAL. Ohne die Marke `_h` stiege der Lauf beim Aufsteigen sofort
#            wieder in dasselbe Kind hinab und liefe nicht aus.
#      0  -- die WURZEL ist nicht dabei: ein Knoten ist kein Nachfahre seiner selbst.
#      1  -- **Nachordnung**: jedes Kind steht vor seinem Elter. Das ist die Zusage, die
#            `by consuming` gibt, und `blatt_loeschen` verlangt sie als `requires ist_blatt`.
#
# > Das Gift dreht `{k} = {basis}[{k}].{kind}` auf `.elter` -- also genau die Verwechslung,
# > die «B41b» ueberhaupt erst zur Frage gemacht hat.
read -r -d '' QUELLE41 <<'GABEOF' || true
module probe::baum {

const NSLOTS : u32 = 4096;

-- **Der Zaehler traegt seine Schranke, und M1 hat es verlangt.** Die erste Fassung schrieb
-- `static mut zaehler : u32` und `zaehler + 1` -- ein volles Wort plus eins, also `M104`.
-- *Die Probe des Erzeugers ist an dem Pass gefallen, den sie ueberhaupt erst voraussetzt.*
type Rang = u32 in 0 .. 8190;

table Kappenraum count NSLOTS {
    tree { parent elter, child erstes_kind, sibling naechstes }

    slot {
        gesehen     : u32 wrapping,
        rang        : u32 wrapping,
        elter       : option index into Kappenraum,
        erstes_kind : option index into Kappenraum,
        naechstes   : option index into Kappenraum,
    }
}

static mut zaehler : Rang = 0;

impl fn besuche(c : ptr<normal, rw> Kappenraum, s : index into Kappenraum)
    effects { reads zaehler, writes zaehler, writes c.slots }
    costs   <= 16 ops
{
    if zaehler < 8190 {
        zaehler = zaehler + 1;
    }
    c.slots[s].gesehen = c.slots[s].gesehen + 1;
    c.slots[s].rang = zaehler;
}

impl fn einsammeln(c : ptr<normal, rw> Kappenraum, s : index into Kappenraum)
    effects { reads zaehler, writes zaehler, consumes c.slots, writes c.slots }
    costs   <= 81920 ops
{
    traverse opfer over descendants of c.slots[s] by consuming
        touches reads zaehler, writes zaehler, consumes c.slots, writes c.slots
    {
        besuche(c, opfer);
    }
}

}
GABEOF
printf '%s\n' "$QUELLE41" > "$ARB/b41.gab"

TREIBER41='#include <stdio.h>
#include "@ERZEUGT@"
#define NIL 4096u
static void haenge(Kappenraum *t, uint32_t e, uint32_t k) {
    t->slots[k].elter = e;
    t->slots[k].erstes_kind = NIL;
    t->slots[k].naechstes = t->slots[e].erstes_kind;
    t->slots[e].erstes_kind = k;
}
int main(void) {
    static Kappenraum t;
    for (uint32_t i = 0; i < 4096; i++) {
        t.slots[i].elter = NIL; t.slots[i].erstes_kind = NIL; t.slots[i].naechstes = NIL;
    }
    /*        0
     *      / | \
     *     1  2  3
     *    /|     |
     *   4 5     6
     *           |
     *           7   */
    haenge(&t, 0, 3); haenge(&t, 0, 2); haenge(&t, 0, 1);
    haenge(&t, 1, 5); haenge(&t, 1, 4);
    haenge(&t, 3, 6); haenge(&t, 6, 7);

    einsammeln(&t, 0);

    unsigned gesehen = 0, doppelt = 0;
    for (uint32_t i = 1; i <= 7; i++) {
        if (t.slots[i].gesehen == 1) gesehen++;
        if (t.slots[i].gesehen > 1) doppelt++;
    }
    /* Nachordnung: jedes Kind traegt einen kleineren Rang als sein Elter. */
    uint32_t paare[6][2] = {{4,1},{5,1},{7,6},{6,3},{1,0},{2,0}};
    unsigned nachordnung = 1;
    for (int i = 0; i < 6; i++) {
        uint32_t k = paare[i][0], e = paare[i][1];
        if (e == 0) continue;
        if (t.slots[k].rang > t.slots[e].rang) nachordnung = 0;
    }
    printf("%u %u %u %u\n", gesehen, doppelt,
           (unsigned)t.slots[0].gesehen, nachordnung);
    return 0;
}
'
lauf "baum41" "$ARB/b41.gab" "$TREIBER41" "7 0 0 1" \
     's/\.erstes_kind; _h1 = false/.elter; _h1 = false/' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 2 templates (0 of them UNPROVED), 7 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- Das BAUGATTER: `when TESTBUILD` -----------------------------------------------------
#
# **Die Frage, die dieser Lauf beantwortet:** was kostet das Mess- und Selbsttestgeruest im
# ausgelieferten Erzeugnis? Antwort: nichts, und zwar nachgezaehlt.
#
# `messung/GEGENRECHNUNG.md` §8 ist der eine Posten der Caprock-Messung, den die Nachrechnung
# ohne Abzug bestaetigt -- und er wurde dabei GROESSER: **29,8 % des Baumes sind Geruest**,
# 19 849 Zeilen, davon 15 154 Code. *Rust sagt dazu nichts, Verus sagt dazu nichts, Loom sagt
# dazu nichts.* Bis zum 2026-08-28 sagte Gabbro auch nichts dazu: `when` war geparst und
# wurde von `emit.rs` nie gelesen.
#
# Der `lauf` unten misst den AUSLIEFERUNGSBAU -- er ist der Standard, `emit` ohne Fahne.
# Die Stufe danach ist die eigentliche Aussage: **derselbe Quelltext, zwei Bauten, und der
# Name des Geruests kommt in genau einem davon vor.**
TREIBER52='#include <stdio.h>
#include "@ERZEUGT@"
int main(void) {
    Puffer p = {0};
    ablegen(&p, 3, 42);
    printf("%u %u\n", stand(&p, 3), stand(&p, 0));
    return 0;
}
'
lauf "beispiel52" "$W/beispiele/52-baugatter.gab" "$TREIBER52" "42 0" \
     's/p->slots\[i\].fuellstand = v;/(void)v;/' \
     "0 assumptions (0 of them NOT FALSIFIABLE), 1 templates (0 of them UNPROVED), 9 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# **Und die Aussage, auf die es bei einem Gatter ankommt: es steht NICHT im C.**
#
# *Ein Gatter, das im C landet, ist kein Gatter* -- ein `#if` haette den ganzen Block
# mitgeliefert und nur den Praeprozessor darueber entscheiden lassen. Hier wird der Baum vor
# dem Erzeuger gefiltert (`gatter::ohne_gatter`), und was das heisst, wird hier gezaehlt.
echo '== Baugatter: `when TESTBUILD` erzeugt im Auslieferungsbau nichts =='
cargo run -q --manifest-path "$W/Cargo.toml" --bin gabbro -- emit \
    "$W/beispiele/52-baugatter.gab" > "$ARB/g52-aus.c"
cargo run -q --manifest-path "$W/Cargo.toml" --bin gabbro -- emit --testbuild \
    "$W/beispiele/52-baugatter.gab" > "$ARB/g52-pruef.c"
GERUEST='hoechstmarke\|kerne_gemessen\|abnahme\|freigabe\|puffer_haelt'
n_aus_g="$(grep -c "$GERUEST" "$ARB/g52-aus.c" || true)"
n_pr_g="$(grep -c "$GERUEST" "$ARB/g52-pruef.c" || true)"
if [ "$n_aus_g" != "0" ]; then
    echo "  Auslieferung:  GESCHEITERT -- $n_aus_g Zeilen nennen das Geruest"
    grep -n "$GERUEST" "$ARB/g52-aus.c" | head -10; exit 1
fi
# **Die Sprechprobe der Zaehlung selbst.** Waere das Geruest auch im Pruefbau abwesend, waere
# die Null oben keine Aussage ueber das Gatter, sondern ueber einen leeren Zaehler.
if [ "$n_pr_g" = "0" ]; then
    echo "  Pruefbau:      GESCHEITERT -- auch --testbuild nennt das Geruest nicht."
    echo "                 Diese Zaehlung misst NICHTS."; exit 1
fi
echo "  Geruestnamen:  ok (0 im Auslieferungs-C, $n_pr_g im Pruefbau-C)"
echo "  Zeilen:        $(grep -c '' "$ARB/g52-aus.c") gegen $(grep -c '' "$ARB/g52-pruef.c")"
# **Und der Pruefbau muss auch UEBERSETZEN.** Ein Gatter, das nur den kleineren Bau richtig
# macht, verlegt den Fehler in den Bau, in dem die Pruefungen laufen.
if ! cc -std=c11 -Wall -Wextra -Werror -c -o /dev/null "$ARB/g52-pruef.c" 2> "$ARB/g52err"; then
    echo "  Pruefbau cc:   GESCHEITERT"; head -10 "$ARB/g52err"; exit 1
fi
echo "  Pruefbau cc:   ok (-Werror, und die Probe pruefe_puffer_haelt steht darin)"

# =======================================================================================
# **Stufe 9: die REGEL, nicht die Liste** (2026-08-20).
#
# Bis heute war dieser Waechter eine gepflegte Liste von Dateien. Er wuchs von 12 auf 17
# Einheiten, weil eine Rezension die Luecke benannte -- und der NAECHSTE neue Konstrukttyp
# lief wieder daran vorbei: `beispiele/36-asm.gab` erzeugte C, das `gcc` ablehnt
# (`%eax` statt `%%eax` in erweitertem Assembler), und keine Stufe hat gefragt.
#
# > *Bei `asm` sagt die Sprache ausdruecklich, dass sie den Inhalt nicht liest. Damit ist
# > der C-Uebersetzer die einzige Pruefung, die es ueberhaupt gibt -- und genau der wurde
# > nicht gefragt.*
#
# Eine Liste deckt, was jemand eingetragen hat. Eine REGEL deckt, was da ist:
#
#     JEDE Datei, die durch `emit` kommt, MUSS `cc -Werror` bestehen.
#
# Die Ausnahmen stehen einzeln und mit Grund da -- und **eine Ausnahme, die nicht mehr
# noetig ist, faellt ebenfalls auf.** Sonst waechst hier eine zweite Liste nach.
echo
echo "== Stufe 9: jede Datei, die emittiert, muss auch uebersetzen =="

# Datei -> Grund. Eine Ausnahme ist ein BEFUND mit Adresse, kein Freibrief.
# **Die Liste ist LEER, und das ist der Ertrag des 2026-08-20.**
#
# Drei Eintraege standen hier, und alle drei sind an demselben Tag abgelaufen -- gemeldet
# von diesem Waechter selbst, nicht von einem Leser:
#
#   * `02-geraet.gab`  -- Namensschemabruch: definiert `Vtd_wurzel_setzen`, ruft
#                         `wurzel_setzen`. Der Erzeuger stellt den Bezug jetzt her.
#   * `13-zeuge-mit-staerke.gab` -- unvollstaendiges `struct Zaehlwerk`. Der Verbund stand
#                         in der QUELLE nicht; jetzt steht er da.
#   * `23-akkumulatoren.gab` -- ruft `gabbro_kern()` ohne Prototyp. Der Eintrag nannte es
#                         Absicht und sagte im selben Satz, dass die Ausgabe damit nicht
#                         selbsttragend ist. **Ein fremder Rumpf braucht seinen Prototypen**;
#                         der steht jetzt im Erzeugnis, mit seinem Vertrag daneben.
#
# > *Eine Ausnahmeliste, die niemand leert, wird zur Beschreibung des Zustands.* Diese hier
# > hat sich selbst gemeldet -- die Erkennung abgelaufener Eintraege ist der Teil, auf den es
# > ankommt, und nicht die Liste.
ausnahme_grund() {
    case "$1" in
    *) return 1 ;;
    esac
}

n_emit=0; n_ok=0; n_aus=0; schlecht=0
for q in "$W"/beispiele/*.gab; do
    d="$(basename "$q")"
    if ! cargo run -q --manifest-path "$W/Cargo.toml" --bin gabbro -- emit "$q" \
            > "$ARB/regel.c" 2>/dev/null || [ ! -s "$ARB/regel.c" ]; then
        continue          # `C001` weigert sich -- eine Weigerung ist eine ehrliche Antwort.
    fi
    n_emit=$((n_emit + 1))
    if cc -std=c11 -Wall -Wextra -Werror -c -o /dev/null "$ARB/regel.c" 2> "$ARB/regelerr"; then
        n_ok=$((n_ok + 1))
        if grund="$(ausnahme_grund "$d")"; then
            echo "  ABGELAUFENE AUSNAHME: $d uebersetzt jetzt -- der Eintrag gehoert geloescht"
            echo "                        (stand da als: $grund)"
            schlecht=1
        fi
    elif grund="$(ausnahme_grund "$d")"; then
        n_aus=$((n_aus + 1))
        echo "  ausgenommen  $d -- $grund"
    else
        echo "  UEBERSETZT NICHT: $d"
        head -3 "$ARB/regelerr" | sed 's/^/      /'
        schlecht=1
    fi
done
echo "  $n_ok von $n_emit emittierenden Dateien uebersetzen; $n_aus benannte Ausnahmen"

# **Die Zahl `n_emit` ist SELBSTGEWAEHLT, und das ist eine Luecke gewesen** (2026-08-28).
#
# Der Waechter zaehlt nur Dateien, die ueberhaupt emittieren. Faellt eine aus der Menge --
# weil eine neue Form dazukam, die der Erzeuger mit `C001` absagt --, schrumpft der NENNER,
# und `n_ok von n_emit` bleibt gruen. **Genau so ist es an diesem Tag passiert:** `beispiele/07`
# bekam fuer S3 einen Parameter vom Typ eines `walk`, den `emit.rs` nicht absenkt, und die
# Zeile las sich unveraendert als ALL PASS -- bei 52 -> 51.
#
# *Dieselbe Klasse wie die Bilanzregel des Rumpfkanals, eine Ebene hoeher:* ein Erzeuger, der
# eine Form verschluckt, sieht aus wie einer, der sie absagt -- und ein WAECHTER, dessen
# Nenner das ist, was das Werkzeug selbst liefert, misst seine eigene Reichweite.
#
# **Die Marke ist eine Ratsche: sie darf STEIGEN, nicht fallen.** Wer eine Form baut, die
# eine Datei aus der Emission wirft, sagt es hier -- mit Grund, nicht durch Absenken.
MARKE_EMIT=52
if [ "$n_emit" -lt "$MARKE_EMIT" ]; then
    echo "  RATSCHE GEBROCHEN: $n_emit emittierende Dateien, gebucht sind $MARKE_EMIT."
    echo "                     Eine Datei hat die Emission VERLASSEN -- das ist kein gruener"
    echo "                     Lauf, sondern ein kleinerer Nenner. Nachsehen mit:"
    echo "                     for f in beispiele/*.gab; do ./target/debug/gabbro emit \$f >/dev/null || echo \$f; done"
    schlecht=1
elif [ "$n_emit" -gt "$MARKE_EMIT" ]; then
    echo "  FUND: $n_emit statt $MARKE_EMIT emittierende Dateien -- die Marke gehoert"
    echo "        nachgezogen (der gute Fall, und trotzdem ein Befund)."
    schlecht=1
fi
if [ "$schlecht" != "0" ]; then
    echo "== EMISSION: die REGEL haelt nicht -- eine neue Form ist am C-Uebersetzer vorbei =="
    exit 1
fi

# **Die Sprechprobe der Regel.** Ein Waechter, der nur gruen kann, misst nichts: hier faellt
# absichtlich erzeugtes C durch, damit „$n_ok von $n_emit" eine Aussage ist und kein Ritual.
printf 'int fehlt(void) { return nicht_da(); }\n' > "$ARB/sprech9.c"
if cc -std=c11 -Wall -Wextra -Werror -c -o /dev/null "$ARB/sprech9.c" 2>/dev/null; then
    echo "== EMISSION: Sprechprobe 9 haelt nicht -- cc -Werror laesst alles durch =="
    exit 1
fi
echo "  Sprechprobe:  ok (ein fehlender Prototyp faellt an cc -Werror)"

# =======================================================================================
# **Stufe 10: die BIBLIOTHEKSKETTE, und sie ist die einzige Stufe mit einem BINDER.**
#
# Jede Stufe darueber uebersetzt EINE Uebersetzungseinheit und schliesst das Erzeugnis mit
# `#include` in ihren Treiber ein. Damit ist eine ganze Klasse von Aussagen unmessbar:
# **welcher Name bindet nach aussen und welcher nicht.** Ein `static`, das fehlt, faellt in
# einer einzelnen Einheit ueberhaupt nicht auf -- es faellt beim Binden, und gebunden hat
# dieser Waechter bis zum 2026-08-25 nie.
#
#     bib-fach.gab  ---abi--->  fach.gabi    ---.
#     bib-mischen.gab -abi--->  mischen.gabi ---+--> emit --with --> nutzer.o
#            |                                             |
#            +--- emit --> fach.o, mischen.o --------------+--> ld --> AUSFUEHREN
#
# Drei Aussagen haengen daran, und keine davon kann eine einzelne Einheit treffen:
#
#   (a) die `.gabi` reicht dem Nutzer, um zu PRUEFEN und zu UEBERSETZEN;
#   (b) was `pub` traegt, bindet nach aussen -- und was es NICHT traegt, bindet NICHT
#       (`nm` fragt den Binder und nicht den Erzeuger);
#   (c) das gebundene Programm rechnet, was die Handschrift sagt.
#
# > **(b) ist die Stufe, um derentwillen es diese gibt.** Vor dem 2026-08-25 kannte `emit.rs`
# > das Wort `pub` an keiner Stelle: ein privater Rechenhelfer erschien im C als Symbol mit
# > aeusserer Bindung, und der ganze Innenraum einer Bibliothek lag auf dem Tisch des Binders.
echo
echo "== Stufe 10: die Bibliothekskette, mit Binder =="
N_DURCHGESTOCHEN=$((N_DURCHGESTOCHEN + 1))
BIB="$ARB/bib"; mkdir -p "$BIB"
G() { cargo run -q --manifest-path "$W/Cargo.toml" --bin gabbro -- "$@"; }

for b in fach mischen; do
    if ! G abi "$W/messung/abi-proben/bib-$b.gab" > "$BIB/$b.gabi" 2> "$BIB/err"; then
        echo "  1. abi:        GESCHEITERT ($b)"; cat "$BIB/err"; exit 1
    fi
    grep -q '^-- @gabi 1' "$BIB/$b.gabi" || { echo "  1. abi: $b.gabi traegt die Marke nicht"; exit 1; }
done
echo "  1. abi:        ok (zwei .gabi, je mit Marke)"

# **Die Schnittstelle traegt nur, was `pub` traegt.** Der private Helfer darf in KEINER
# der beiden stehen -- sonst zeigt sie auf einen Namen, den der Binder nicht hergibt.
if grep -q 'begrenze\|verdopple' "$BIB/fach.gabi" "$BIB/mischen.gabi"; then
    echo "  1b. Ausfuhr:   ein PRIVATER Name steht in der Schnittstelle"; exit 1
fi
grep -q 'pub table Kaesten' "$BIB/fach.gabi" || { echo "  1b. Ausfuhr: der ausgefuehrte Traeger fehlt"; exit 1; }
echo "  1b. Ausfuhr:   ok (Traeger drin, die beiden privaten Helfer nicht)"

if ! G pruefe --with "$BIB/fach.gabi" --with "$BIB/mischen.gabi" \
        "$W/messung/abi-proben/nutzt-beide.gab" > "$BIB/pruef" 2>&1; then
    echo "  2. pruefe:     GESCHEITERT"; head -20 "$BIB/pruef"; exit 1
fi
grep -q ', 0 Fehler, 0 Hinweise' "$BIB/pruef" || { echo "  2. pruefe: nicht sauber"; head -20 "$BIB/pruef"; exit 1; }
echo "  2. pruefe:     ok (0 Fehler, 0 Hinweise ueber die Grenze)"

G emit "$W/messung/abi-proben/bib-fach.gab"    > "$BIB/fach.c"    || exit 1
G emit "$W/messung/abi-proben/bib-mischen.gab" > "$BIB/mischen.c" || exit 1
G emit --with "$BIB/fach.gabi" --with "$BIB/mischen.gabi" \
       "$W/messung/abi-proben/nutzt-beide.gab" > "$BIB/nutzer.c"  || exit 1
for o in fach mischen nutzer; do
    if ! cc -std=c11 -O0 -Wall -Wextra -Werror -c -o "$BIB/$o.o" "$BIB/$o.c" 2> "$BIB/ccerr"; then
        echo "  3. cc -Werror: GESCHEITERT ($o)"; head -10 "$BIB/ccerr"; exit 1
    fi
done
echo "  3. cc -Werror: ok (drei Einheiten, getrennt uebersetzt)"

# **`nm` fragt den BINDER.** Was hier steht, ist keine Absicht des Erzeugers, sondern das,
# was die Objektdatei hergibt.
aussen="$(nm -g --defined-only "$BIB/fach.o" "$BIB/mischen.o" | awk '$2=="T"{print $3}' | sort | tr '\n' ' ')"
if [ "$aussen" != "lege_ab lies mische " ]; then
    echo "  4. Bindung:    FALSCH -- aussen sichtbar ist: $aussen"
    echo "                 erwartet: lege_ab lies mische"
    exit 1
fi
echo '  4. Bindung:    ok (drei pub-Namen aussen, begrenze/verdopple nicht)'

cat > "$BIB/treiber.c" <<'BIBTREIBER'
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
bool eintragen(uint32_t i, uint32_t a, uint32_t b);
uint32_t nachsehen(uint32_t i);
int main(void) {
    eintragen(3, 1000, 7);        /* mische = 2*1000+7 = 2007, unter der Schranke */
    eintragen(0, 40000, 40000);   /* mische = 120000, `begrenze` deckelt auf 65535 */
    printf("%u %u\n", nachsehen(3), nachsehen(0));
    return 0;
}
BIBTREIBER
BIBERWARTET="2007 65535"
for opt in -O0 -O2; do
    if ! cc -std=c11 $opt -Wall -Wextra -Werror -o "$BIB/probe$opt" \
            "$BIB/treiber.c" "$BIB/fach.o" "$BIB/mischen.o" "$BIB/nutzer.o" 2> "$BIB/lderr"; then
        echo "  5. binden:     GESCHEITERT ($opt)"; head -10 "$BIB/lderr"; exit 1
    fi
    ist="$("$BIB/probe$opt")"
    if [ "$ist" != "$BIBERWARTET" ]; then
        echo "  6. Ergebnis:   FALSCH bei $opt -- erwartet '$BIBERWARTET', bekommen '$ist'"; exit 1
    fi
done
echo "  5. binden:     ok (-O0 und -O2, ein Programm aus drei Objekten)"
echo "  6. Ergebnis:   ok ($BIBERWARTET -- der private Helfer hat gedeckelt)"

# **Sprechprobe A: der PRIVATE Helfer rechnet wirklich mit.** Ohne sie sagt „6. Ergebnis"
# nichts ueber ihn -- er koennte tot sein und die Zahl trotzdem stimmen.
sed 's/return x + x;/return x + 0;/' "$BIB/mischen.c" > "$BIB/mischen-gift.c"
cmp -s "$BIB/mischen.c" "$BIB/mischen-gift.c" && { echo "  7. Sprechprobe A: das Gift greift nicht"; exit 1; }
cc -std=c11 -O0 -w -c -o "$BIB/mischen-gift.o" "$BIB/mischen-gift.c" || exit 1
cc -std=c11 -O0 -w -o "$BIB/probe-gift" "$BIB/treiber.c" "$BIB/fach.o" "$BIB/mischen-gift.o" "$BIB/nutzer.o" || exit 1
if [ "$("$BIB/probe-gift")" = "$BIBERWARTET" ]; then
    echo '  7. Sprechprobe A: GESCHEITERT -- verfaelschtes verdopple rechnet dasselbe'; exit 1
fi
echo "  7. Sprechprobe A: ok (verfaelschter privater Helfer aendert das Ergebnis)"

# **Sprechprobe B: die GEGENRICHTUNG, und sie ist der Grund fuer `N039`.**
#
# Zwei Bibliotheken mit demselben oeffentlichen Namen muessen an einer GABBRO-Kennung
# fallen, nicht am Binder. Gemessen wird beides: dass der Uebersetzer absagt -- und dass
# der Binder es sonst getan haette, damit die Absage nicht auf eine Kollision zeigt, die
# es gar nicht gibt.
cat > "$BIB/eins.gab" <<'BIBEINS'
module eins {
pub impl fn lesen() -> u32 effects { pure } costs <= 2 ops { return 1; }
}
BIBEINS
sed 's/module eins/module zwei/; s/return 1;/return 2;/' "$BIB/eins.gab" > "$BIB/zwei.gab"
if G pruefe "$BIB/eins.gab" "$BIB/zwei.gab" > "$BIB/koll" 2>&1; then
    echo "  8. Sprechprobe B: GESCHEITERT -- zwei gleiche oeffentliche Namen gehen durch"; exit 1
fi
grep -q 'N039' "$BIB/koll" || { echo "  8. Sprechprobe B: es faellt, aber nicht an N039:"; head -5 "$BIB/koll"; exit 1; }
# und die Gegenprobe der Gegenprobe: EINZELN erzeugt kollidiert es wirklich beim Binder.
G emit "$BIB/eins.gab" > "$BIB/e1.c" && G emit "$BIB/zwei.gab" > "$BIB/e2.c" || exit 1
cc -std=c11 -w -c -o "$BIB/e1.o" "$BIB/e1.c" && cc -std=c11 -w -c -o "$BIB/e2.o" "$BIB/e2.c" || exit 1
printf 'int main(void){return 0;}\n' > "$BIB/leer.c"
if cc -w -o "$BIB/zusammen" "$BIB/leer.c" "$BIB/e1.o" "$BIB/e2.o" 2> "$BIB/ld2"; then
    echo '  8. Sprechprobe B: GESCHEITERT -- der Binder nimmt zwei lesen an, N039 zeigt ins Leere'; exit 1
fi
grep -q 'multiple definition' "$BIB/ld2" || { echo "  8. Sprechprobe B: der Binder faellt aus anderem Grund:"; head -3 "$BIB/ld2"; exit 1; }
echo "  8. Sprechprobe B: ok (N039 sagt ab, und der Binder haette es sonst getan)"

echo "== EMISSION: ALL PASS -- $N_DURCHGESTOCHEN durchgestochen, $n_ok von $n_emit uebersetzen =="
echo "  Und was das NICHT heisst: DURCHGESTOCHEN sind $N_DURCHGESTOCHEN -- erzeugt, uebersetzt,"
echo "  AUSGEFUEHRT und mit einer Handschrift verglichen. Die Regel darueber ist"
echo "  schwaecher: sie fragt nur, ob der C-Uebersetzer die Ausgabe annimmt. Ein"
echo "  Programm, das uebersetzt und falsch rechnet, faellt ihr nicht auf."
