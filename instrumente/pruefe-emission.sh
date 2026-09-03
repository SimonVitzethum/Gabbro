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

# **WER MITTEN IM LAUF ABBRICHT, SCHREIBT DAZU, WAS ER NICHT MEHR GEMESSEN HAT**
# ----------------------------------------------------------------------------
# (2026-08-31, und der Anlass ist dieser Waechter selbst.)
#
# Am 2026-08-31 starb er an `F06`s `N043` in der VIERTEN von zehn Stufen, mit `exit 1`.
# **Die Stufen 9 und 10 liefen nie, und keine Zeile sagte das.** Dahinter standen zwei
# Befunde, die zwei Wochen niemand gesehen hat: sechs Dateien, deren erzeugtes C nicht
# uebersetzt, und eine Marke, die sieben zu niedrig stand.
#
# > *Eine leere Grundgesamtheit ist ein gruenes Urteil ueber nichts (W17). Eine
# > ABGESCHNITTENE sieht aus wie ein Urteil ueber alles.*
#
# Der Ruecklaufwert allein kann es nicht sagen: `1` heisst „Befund", und ein Befund in
# Stufe 4 ist zugleich ein Abbruch fuer die Stufen 5 bis 10. **Also sagt es die Ausgabe.**
# `messung/RUECKLAUFWERTE.md` fuehrt die Klasse und ihre Zahl (43 von 49 Waechtern koennen
# so abbrechen); dies hier ist die Form, die sie beantwortet.
LETZTE_STUFE="Kopf (vor der ersten Stufe)"
GANZ_DURCH=0
aufraeumen() {
    local rc=$?
    if [ "$rc" != 0 ] && [ "$GANZ_DURCH" = 0 ]; then
        echo
        echo "== ABGESCHNITTEN in: $LETZTE_STUFE -- Ruecklaufwert $rc =="
        echo "   Was DAHINTER steht, wurde NICHT gemessen -- weder ja noch nein. Die volle"
        echo "   Kette ist: Sprechprobe des Kopfes, die Differenztests, Baugatter, Stufe 9"
        echo "   (uebersetzt jede emittierende Datei?), Stufe 10 (die Bibliothekskette)."
        echo "   Ein Ruecklaufwert, der wie ein Befund aussieht, ist hier zugleich ein"
        echo "   Abbruch fuer den Rest -- messung/RUECKLAUFWERTE.md, Abschnitt zum Schnitt."
    fi
    rm -rf "$ARB"
}
trap aufraeumen EXIT

# **W1: eine uebersprungene Probe senkt die Zahl, sie laesst sie nicht unberuehrt.**
# Kein `cc` heisst NICHT „bestanden, uebersprungen" -- es heisst, dass dieser Waechter
# nichts gemessen hat, und das ist ein Rot.
# **Und der Gegenstand selbst, seit dem 2026-08-31.** Ueber einem Baum ohne `Cargo.toml`
# lief dieser Waechter bis in die erste Stufe und starb dort mit `exit 1` an einer
# `cargo`-Meldung -- also mit der Farbe eines gefundenen Emissionsfehlers. *Ein Erzeuger,
# den es nicht gibt, erzeugt nichts Falsches.*
if [ ! -f "$W/Cargo.toml" ] || ! command -v cargo > /dev/null; then
    echo "== EMISSION: KEIN CARGO-BAUM -- der Differenztest hat NICHTS gemessen =="
    echo "  Weder ein Erzeugnis noch ein Fehler: dieser Lauf hat gar nicht angefangen."
    exit 2
fi

if ! command -v cc > /dev/null; then
    echo "== EMISSION: KEIN CC -- der Differenztest hat NICHTS gemessen =="
    echo "  Ein fehlendes Werkzeug ist kein bestandener Test. W1: der Ausfall senkt die"
    echo "  Zahl, er laesst sie nicht unberuehrt."
    exit 2
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

# **Und die dritte Sprechprobe entscheidet, OB Stufe 6b ueberhaupt etwas messen kann**
# (2026-09-02). Sie ist die einzige, die nicht rot faerbt, wenn sie nicht haelt -- weil ihre
# Antwort eine Eigenschaft der MASCHINE ist und keine des Baums.
#
# Drei Ausgaenge, und alle drei sind verschieden:
#
#   * ASan uebersetzt nicht, oder ein sauberes Programm bricht vor `main` ab
#     -> `ASAN_LAEUFT=0`. Auf dem Arbeitsrechner (gehaerteter Kern) ist das der Fall: der
#        Schattenspeicher kollidiert mit der Speicherkarte. Stufe 6b sagt dann je Einheit
#        `NICHT GEFAHREN`, und die Schlusszeile zaehlt sie. **Kein Haken.**
#   * ASan startet, faengt aber einen echten Heap-Ueberlauf NICHT -> ebenfalls `0`, und das
#     ist der wichtigere Zweig: *ein Sanitizer, der laeuft und nichts findet, ist die
#     schlimmste Antwort von allen* (`W1`, und die Regel des Hauses ueber fehlende Werkzeuge).
#   * beides haelt -> `ASAN_LAEUFT=1`, und Stufe 6b misst.
ASAN_LAEUFT=0
sprechprobe_asan() {
    local d; d="$(mktemp -d)"
    cat > "$d/sauber.c" <<'PROBE_S'
#include <stdio.h>
#include <stdlib.h>
int main(void) { char *p = malloc(4); p[0] = 1; printf("%d\n", (int)p[0]); free(p); return 0; }
PROBE_S
    # **Die Groesse und der Index sind `volatile`, und das ist der ganze Trick.** Mit
    # `malloc(4)` und `p[7]` als Konstanten faltet `gcc -O1` die Belegung weg, ASan sieht
    # keinen Heap mehr und schweigt -- **und eine schweigende Gegenprobe liest sich wie eine
    # Maschine ohne ASan.** Genau so ist diese Sprechprobe am 2026-09-02 auf `fisch` zuerst
    # gescheitert, wo ASan in Wahrheit tadellos laeuft. *Ein Messgeraet, dessen Gegenprobe
    # der Optimierer entfernt, meldet die Abwesenheit seines eigenen Gegenstands.*
    cat > "$d/kaputt.c" <<'PROBE_K'
#include <stdio.h>
#include <stdlib.h>
volatile int n = 4;
volatile int k = 7;
int main(void) {
    char *p = malloc((size_t)n);
    if (!p) return 2;
    p[k] = 1;
    printf("%d\n", (int)p[k]);
    free(p);
    return 0;
}
PROBE_K
    if ! cc -std=c11 -O1 -fsanitize=address -o "$d/sauber" "$d/sauber.c" 2>/dev/null; then
        echo "  Sprechprobe A: KEIN ASAN -- Stufe 6b kann nichts messen (nicht uebersetzbar)"
    elif ! ASAN_OPTIONS=detect_leaks=0 "$d/sauber" > /dev/null 2>&1; then
        echo "  Sprechprobe A: ASan STARTET NICHT auf dieser Maschine (Schattenspeicher)"
        echo "                 -- Stufe 6b meldet je Einheit NICHT GEFAHREN, kein Haken."
    elif ! cc -std=c11 -O1 -fsanitize=address -w -o "$d/kaputt" "$d/kaputt.c" 2>/dev/null; then
        echo "  Sprechprobe A: KEIN ASAN fuer die Gegenprobe -- Stufe 6b bleibt aus"
    elif ASAN_OPTIONS=detect_leaks=0 "$d/kaputt" > /dev/null 2>&1; then
        echo "  Sprechprobe A: GESCHEITERT -- ein Heap-Ueberlauf kam DURCH, ASan schweigt."
        echo "                 Ein Werkzeug, das laeuft und nichts findet, ist die schlimmste Antwort."
    else
        ASAN_LAEUFT=1
        echo "  Sprechprobe A: ok (sauber laeuft, ein Heap-Ueberlauf faellt)"
    fi
    rm -rf "$d"
}

LETZTE_STUFE="der Sprechprobe des Kopfes"
echo "== Sprechprobe: koennen die neuen Stufen ueberhaupt fallen? =="
if ! sprechprobe_ub; then
    echo "== EMISSION: die Sprechprobe haelt nicht -- ein Haken ohne Messung ist schlimmer als keiner =="
    exit 2
fi
sprechprobe_asan
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

# **`--absenkung`: der Waechter beantwortet die Frage, auf der `H` steht** (2026-08-31).
# -------------------------------------------------------------------------------------
# `zaehle-pflichten.py` las die Absenkungsspalte bis heute **am QUELLTEXT dieser Datei** ab:
# `^lauf "fragment(\d+)"`, an der blossen Anwesenheit der Zeile. **Nicht daran, ob der Lauf
# haelt.** Am 2026-08-31 stand `F06` an `N043` (`measures eich`, ein Traeger, den es nicht
# gibt), dieser Waechter war deswegen zu Recht ROT -- und `H` sagte weiter 4.
#
# > *Dieselbe Familie wie `W25`, eine Stufe weiter: dort trug eine richtige Zahl eine
# > ungemessene BESCHRIFTUNG, hier trug eine Zahl eine ungemessene VORAUSSETZUNG.* Solange
# > die Zeile steht, kann der Lauf fallen und die Zahl bleibt.
#
# In diesem Modus laufen NUR die `fragment*`-Durchstiche, und **ein gefallener ist ein
# ERGEBNIS und kein Abbruch**: der Zaehler braucht alle sechs Antworten, nicht die erste.
# Je Fragment steht danach eine Zeile `DURCHSTICH fragmentN HAELT` oder `… FAELLT` da.
NUR_ABSENKUNG=""
for _a in "$@"; do
    case "$_a" in
        --absenkung) NUR_ABSENKUNG=1 ;;
        *) echo "unbekanntes Argument: $_a -- es gibt nur --absenkung" >&2; exit 2 ;;
    esac
done

lauf() {          # $1 Name  $2 Quelle  $3 Treiber  $4 Erwartet  $5 Gift-sed  $6 Zeugnis
    local name="$1"
    if [ -n "$NUR_ABSENKUNG" ]; then
        case "$name" in fragment*) ;; *) return 0 ;; esac
        absenkung_messen "$@"
        return 0
    fi
    # **Die Zahl wird GEZAEHLT, nicht gepflegt** (2026-08-20). Sie stand als `17` in der
    # Schlusszeile, waehrend achtzehn Einheiten liefen -- dieselbe Klasse wie die Liste, die
    # eine Regel wurde, nur eine Ebene hoeher. *Eine Kennzahl, die jemand nachtragen muss,
    # ist irgendwann falsch.*
    N_DURCHGESTOCHEN=$((N_DURCHGESTOCHEN + 1))
    LETZTE_STUFE="Differenztest $name"
    lauf_kern "$@"
}

# Ein Durchstich, dessen Fall PROTOKOLLIERT statt abgebrochen wird.
#
# **`set -e` muss im Kind ausdruecklich wieder an.** Eine Verbundanweisung links von `||`
# laeuft mit abgeschaltetem `errexit`, und das gilt bis in die Unterschale hinein -- ohne das
# `set -e` liefe `lauf_kern` dort mit einer anderen Fehlersemantik als im vollen Lauf.
# *Ein Messmodus, der anders faellt als der gemessene Lauf, misst den Modus.*
absenkung_messen() {
    local name="$1" rc=0
    ( set -e; lauf_kern "$@" ) > "$ARB/$name.protokoll" 2>&1 || rc=$?
    if [ "$rc" = 0 ]; then
        echo "DURCHSTICH $name HAELT"
    else
        echo "DURCHSTICH $name FAELLT   (Ruecklauf $rc)"
        sed 's/^/      /' "$ARB/$name.protokoll"
    fi
}

lauf_kern() {     # $1 Name  $2 Quelle  $3 Treiber  $4 Erwartet  $5 Gift-sed  $6 Zeugnis
    local name="$1" quelle="$2" treiber="$3" erwartet="$4" gift="$5" zeugnis="$6"
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

    # 6b. **ASan, und bis zum 2026-09-02 war das eine NICHT GEFAHRENE Probe.**
    #
    #     Der Kommentar an Stufe 6 sagte, warum: auf dem Arbeitsrechner (gehaerteter Kern)
    #     kollidiert ASans Schattenspeicher mit der Speicherkarte, und der Lauf bricht vor
    #     `main` ab. `TODO.md` fuehrte die Zeile als offen und nannte sie **„ortsgebunden,
    #     nicht schwer"**. Der Ort ist `ki-pc-fisch-101`, wo ASan laeuft -- nachgemessen mit
    #     einem Heap-Ueberlauf, den er faengt, und einem sauberen Programm, das er durchlaesst.
    #
    #     **Die Fallunterscheidung steht deshalb im Waechter und nicht im Kopf des Fahrers**,
    #     und sie faellt auf die Seite von `W1`: wo ASan nicht startet, sagt diese Zeile
    #     `NICHT GEFAHREN` und faerbt den Waechter NICHT gruen fuer etwas, das nie lief.
    #     *Eine uebersprungene Probe senkt die Zahl, sie laesst sie nicht unberuehrt.*
    #
    #     `detect_leaks=0`: die Erzeugnisse belegen bewusst und geben nichts zurueck -- ein
    #     Leck ist hier keine Aussage ueber den Erzeuger.
    if [ "$ASAN_LAEUFT" = "0" ]; then
        echo "  6b. ASan:      NICHT GEFAHREN -- ASan startet auf diesem Rechner nicht"
        # **Gezaehlt wird in eine DATEI und nicht in eine Variable**, weil `lauf_kern` in
        # einer Subshell laeuft (`( set -e; lauf_kern … )`): ein `$((x + 1))` darin stirbt
        # mit ihr, und die Schlusszeile haette `0 von 0` gemeldet -- eine leere
        # Grundgesamtheit, die wie ein Urteil aussieht (`W17`).
        echo "$name" >> "$ARB/asan-ungefahren"
    elif ! cc -std=c11 -O1 -fsanitize=address,undefined -fno-sanitize-recover=all \
            -I"$ARB" -o "$ARB/$name-probe-as" "$ARB/$name-treiber.c" 2> "$ARB/ccfehler4"; then
        echo "  6b. ASan:      GESCHEITERT beim Uebersetzen"; head -20 "$ARB/ccfehler4"; exit 1
    else
        local ist_as
        ist_as="$(ASAN_OPTIONS=detect_leaks=0 "$ARB/$name-probe-as" 2> "$ARB/asfehler")" || {
            echo "  6b. ASan:      SCHLAEGT AN -- ein Speicherfehler im erzeugten C"
            head -20 "$ARB/asfehler"; exit 1
        }
        if [ -s "$ARB/asfehler" ]; then
            echo "  6b. ASan:      MELDUNG auf stderr"; head -20 "$ARB/asfehler"; exit 1
        fi
        if [ "$ist_as" != "$ist" ]; then
            echo "  6b. ASan:      ANDERES ERGEBNIS"; echo "     $ist / $ist_as"; exit 1
        fi
        echo "  6b. ASan:      ok (kein Fund, gleiches Ergebnis)"
        echo "$name" >> "$ARB/asan-gefahren"
    fi

    # 7. **Das Uebersetzungszeugnis** -- K100.4, Weg (b). Die Differenztests messen EIN
    #    Ergebnis; das Zeugnis zaehlt auf, worauf die Uebersetzung ruht. Die Bedingung hier ist
    #    die Kreuzprobe: **was der Erzeuger absenkt, muss das Zeugnis einordnen.** Steht eine
    #    Form in keiner Einordnung, hat der Erzeuger etwas abgesenkt und es niemandem gesagt.
    if ! cargo run -q --manifest-path "$W/Cargo.toml" --bin gabbro -- zeugnis "$quelle" \
            > "$ARB/$name.zeugnis" 2> "$ARB/zfehler"; then
        echo "  7. Zeugnis:    GESCHEITERT"; cat "$ARB/zfehler"; exit 1
    fi
    # **`UNCLASSIFIED` statt `UNZUGEORDNET` seit dem 2026-08-31** -- dieselbe Bewegung
    # wie bei `templates` darunter: das Zeugnis ist ein Bericht und englisch, und diese
    # Zeile liest ihn ab. *Ein Muster, das nach einer Uebersetzung nichts mehr findet,
    # meldet stumm null.*
    if grep -q "UNCLASSIFIED" "$ARB/$name.zeugnis"; then
        echo "  7. Zeugnis:    UNCLASSIFIED -- der Erzeuger senkt eine Form ab, die keine"
        echo "                 Einordnung kennt. Die Vertrauensflaeche ist groesser als gebucht."
        grep -A3 "UNCLASSIFIED" "$ARB/$name.zeugnis"; exit 1
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
        echo "  8. Sprechprobe: UEBERSEHEN -- ein veraendertes Erzeugnis liefert dasselbe?"; exit 2
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
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 1 templates (0 of them UNPROVED), 5 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
    exit 2
fi
echo "  (F7: der eingefrorene Ausschnitt steht vollstaendig in der Arbeitsfassung"
echo "       -- und eine fehlende Zeile faellt auf, Sprechprobe ok)"
lauf "fragment7" "$W/messung/fragmente/F07.gab" "$TREIBER7" "123456" \
     's/    ipc_tabellen();/    \/* geloescht *\//' \
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 0 templates (0 of them UNPROVED), 4 direct forms, 7 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 3 templates (2 of them UNPROVED), 5 direct forms, 2 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
     "1 assumptions (0 of them NOT FALSIFIABLE, 1 UNCOVERED -- named a probe that does not exist as a program), 2 templates (0 of them UNPROVED), 7 direct forms, 2 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
    exit 2
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
     "3 assumptions (1 of them NOT FALSIFIABLE, 2 UNCOVERED -- named a probe that does not exist as a program), 3 templates (0 of them UNPROVED), 1 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 1 templates (0 of them UNPROVED), 0 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
    exit 2
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
# **2 -> 3 assumptions on 2026-09-01, and the OBJECT grew.** `dma_kohaerent` was a
# CONJUNCTION under one name -- coherence AND ordering, two independent claims, one
# falsifier -- and it is now two assumptions, each with `arch x86_64` and its own probe.
# `F04.gab` names it, so its certificate counts one more. *The certificate got longer
# because the trust base got HONEST, not because it grew.*
lauf "fragment4" "$W/messung/fragmente/F04.gab" "$TREIBER4" \
     "42 1 7 99" \
     's/% q->n/% 1/g' \
     "3 assumptions (0 of them NOT FALSIFIABLE, 3 UNCOVERED -- named a probe that does not exist as a program), 2 templates (0 of them UNPROVED), 7 direct forms, 3 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 4d. Das Fragment F6: die Stack-Wasserstandsmarke, und sie MISST DEN INDEX ------------
#
# **Die erste der fuenf offenen Absenkungspflichten (`H`), die den Ausfuehrungsweg gehen
# kann.** Bis zum 2026-08-30 ging sie nicht: der Erzeuger senkte den Feldindex von
# `elems of` als `uint32_t` ab -- eine Kopie aus `slots of` --, und `w != MUSTER` mit
# `MUSTER = 0xdead_beef_dead_beef` war damit *comparison is always true due to limited
# range*. `-Wextra -Werror` nahm es nicht an. **Mit `uint64_t` uebersetzt dasselbe C.**
#
# ERWARTUNG, ABGELEITET AUS DEM AUSSCHNITT -- HINGESCHRIEBEN, BEVOR SIE GEMESSEN WURDE
# ------------------------------------------------------------------------------------
# *Sonst misst dieser Lauf den Erzeuger gegen sich selbst.* Die Ableitung ruht auf genau
# einer Sprachentscheidung: **`elems of` bindet einen INDEX** (`SYNTAX.md`:635, «B12»,
# entschieden 2026-08-20). Also laeuft `w` ueber 0, 1, …, 8191, und `MUSTER` ist
# 16045690984833335023. Schon der erste Durchgang nimmt den `return`:
#
#     unberuehrt(s)           == 0            fuer JEDES s -- der Rumpf liest `s` nie
#     messen_benutzt(s, art)  == s.len - 0    == s.len
#     pruefe_all_done()       == true         (`can_fail { return true; }`)
#
# Daraus faellt die Eichung des Ausschnitts, und zwar an ZWEI verschiedenen Stellen, je
# nachdem was `eichfeld()` liefert:
#
#     f.len == 0      1. `unberuehrt(f) != 0`             -> 0 != 0, weiter
#                     2. `muster_schreiben(f)`            -> gerufen  (1)
#                     3. `unberuehrt(f) != f.len`         -> 0 != 0, weiter
#                     4. `beruehre(f, 64)`                -> gerufen  (1)
#                     5. `unberuehrt(f) != (8192-64)*8`   -> 0 != 65024  -> FALSE
#
#     f.len != 0      1. weiter · 2. gerufen (1) · 3. `0 != 4096` -> FALSE
#                     `beruehre` wird NICHT mehr gerufen (0)
#
# > **Und das ist der eigentliche Befund dieses Durchstichs, nicht sein Nebenprodukt.**
# > Der Ausschnitt vom 2026-08-14 wurde mit der ELEMENTlesart geschrieben; Gabbro hat sich
# > 2026-08-20 fuer den INDEX entschieden. **Die Eichung, die der Ausschnitt selbst
# > mitbringt, um sein Messgeraet zu pruefen, schlaegt an** -- an genau dem Unterschied.
# > *Ein Fragment, das seine eigene Falschheit meldet, ist der beste Fall, den es hier gibt:
# > das erzeugte C rechnet, was das Fragment SAGT, und was es sagt, ist nicht, was sein
# > Schreiber meinte.* Der Durchstich misst das erste und nennt das zweite.
#
# Die Stuempfe sind darum EHRLICH: `muster_schreiben` schreibt das Muster wirklich in alle
# 8192 Worte, `beruehre` macht die obersten `tiefe` Worte schmutzig. **Ein Stumpf, der
# nichts schreibt, koennte die Indexlesart von der Elementlesart nicht unterscheiden** --
# unter der Elementlesart lieferte Schritt 2 dann 8192*8 und Schritt 4 genau 65024.
#
# `check kstack` haengt an keiner der beiden Lesarten; er wird ueber die Stuempfe belegt:
#
#     g fehlt                                  -> false   (`let … else`)
#     f fehlt                                  -> false
#     g=65536 f=4096                           -> false   (4096 < 65536/8)
#     g=65536 f=8192  irq.tiefe_max=0          -> true    (0 + 8192 <= 8192)
#     g=65536 f=8192  irq.tiefe_max=1          -> false   (8193 <= 8192)
#     g=65536 f=16384 irq.tiefe_max=8192       -> true    (16384 <= 16384)
#     g=65536 f=16384 irq.tiefe_max=8193       -> false   (16385 <= 16384)
schneide "$W/dokumente/FRAGMENTE.md" "module kernel::kstackmark" > "$ARB/f6.gab"
if ! grep -q "traverse w of s over elems of s.worte" "$ARB/f6.gab"; then
    echo "== EMISSION: F6 NICHT GESCHNITTEN -- der Waechter misst seine eigene Ablage =="
    exit 1
fi
if [ -n "$(verlorene_zeilen "$ARB/f6.gab" "$W/messung/fragmente/F06.gab")" ]; then
    echo "== EMISSION: F06.gab hat eine Zeile des eingefrorenen Ausschnitts VERLOREN =="
    verlorene_zeilen "$ARB/f6.gab" "$W/messung/fragmente/F06.gab" | head -10
    exit 1
fi
grep -v "atomic tiefster" "$W/messung/fragmente/F06.gab" > "$ARB/f6-kurz.gab"
if [ -z "$(verlorene_zeilen "$ARB/f6.gab" "$ARB/f6-kurz.gab")" ]; then
    echo "== EMISSION: Sprechprobe F6 haelt nicht -- eine entfernte Ausschnittzeile faellt"
    echo "             nicht auf. Dieser Vergleich misst NICHTS. =="
    exit 2
fi
echo "  (F6: der eingefrorene Ausschnitt steht vollstaendig in der Arbeitsfassung"
echo "       -- und eine fehlende Zeile faellt auf, Sprechprobe ok)"
TREIBER6='#include <stdio.h>
#include "@ERZEUGT@"

/* Die sechs fremden Rumpfe. Der Ausschnitt RUFT sie und deklariert sie nicht; F06.gab
 * traegt die `extern fn`-Zeilen nach, die Koerper schuldet der Rufer -- hier also dieser
 * Treiber. */
static Stack f6_feld;
static unsigned f6_muster_rufe;
static unsigned f6_beruehre_rufe;
static uint64_t f6_g_wert;
static uint64_t f6_f_wert;
static bool f6_g_ok;
static bool f6_f_ok;

Stack * eichfeld(void) { return &f6_feld; }

void muster_schreiben(Stack *s) {
    f6_muster_rufe++;
    for (uint64_t k = 0; k < STACK_WORTE; k++) { s->worte[k] = MUSTER; }
}

/* Der Stack waechst nach unten: „Tiefe" sind die HOECHSTEN Indizes. Unter der
 * Elementlesart lieferte `unberuehrt` danach genau (8192 - tiefe) * 8 -- die Zahl, die der
 * Ausschnitt in Schritt 4 seiner Eichung erwartet. */
void beruehre(Stack *s, uint64_t tiefe) {
    f6_beruehre_rufe++;
    for (uint64_t k = 0; k < tiefe && k < STACK_WORTE; k++) { s->worte[STACK_WORTE - 1 - k] = 0; }
}

bool eichung_lief(void) { return true; }

bool groesse_gemessen(uint64_t *wert, NichtGemessen *grund) {
    if (!f6_g_ok) { *grund = NichtGemessen_Fehlt; return false; }
    *wert = f6_g_wert;
    return true;
}

bool frei_min_gemessen(uint64_t *wert, NichtGemessen *grund) {
    if (!f6_f_ok) { *grund = NichtGemessen_Fehlt; return false; }
    *wert = f6_f_wert;
    return true;
}

static int kstack_mit(uint64_t g, bool g_ok, uint64_t f, bool f_ok, uint64_t im) {
    f6_g_wert = g; f6_g_ok = g_ok; f6_f_wert = f; f6_f_ok = f_ok; irq.tiefe_max = im;
    return pruefe_kstack() ? 1 : 0;
}

int main(void) {
    /* A -- `unberuehrt` an einem FRISCHEN und an einem voll mit MUSTER beschriebenen Feld.
     *      Zweimal 0: der Vergleich trifft den Index, nicht das Wort. */
    printf("%llu ", (unsigned long long)unberuehrt(&f6_feld));
    muster_schreiben(&f6_feld);
    printf("%llu ", (unsigned long long)unberuehrt(&f6_feld));

    /* B -- `messen_benutzt` == s.len - unberuehrt(s) == s.len */
    f6_feld.len = 4096;
    printf("%llu ", (unsigned long long)messen_benutzt(&f6_feld, Stackart_El0));
    printf("%llu ", (unsigned long long)messen_benutzt(&f6_feld, Stackart_Kern));

    /* C -- das Tor `all_done` */
    printf("%d ", pruefe_all_done() ? 1 : 0);

    /* D -- die Eichung des Ausschnitts, zweimal, und die Rufzaehler sagen WO sie faellt */
    f6_feld.len = 0; f6_muster_rufe = 0; f6_beruehre_rufe = 0;
    printf("%d ", pruefe_kstack_eichung() ? 1 : 0);
    printf("%u %u ", f6_muster_rufe, f6_beruehre_rufe);
    f6_feld.len = 4096; f6_muster_rufe = 0; f6_beruehre_rufe = 0;
    printf("%d ", pruefe_kstack_eichung() ? 1 : 0);
    printf("%u %u ", f6_muster_rufe, f6_beruehre_rufe);

    /* E -- `check kstack`, sieben Belegungen: beide Fehlerkanaele, die Schranke und die
     *      Grenze in beide Richtungen */
    printf("%d ", kstack_mit(0, false, 0, false, 0));
    printf("%d ", kstack_mit(65536, true, 0, false, 0));
    printf("%d ", kstack_mit(65536, true, 4096, true, 0));
    printf("%d ", kstack_mit(65536, true, 8192, true, 0));
    printf("%d ", kstack_mit(65536, true, 8192, true, 1));
    printf("%d ", kstack_mit(65536, true, 16384, true, 8192));
    printf("%d\n", kstack_mit(65536, true, 16384, true, 8193));
    return 0;
}
'
# **Das Gift loescht den Ruf von `muster_schreiben` aus der Eichung** -- dieselbe Klasse wie
# bei F7: eine Anweisung faellt weg, das C uebersetzt, und die Eichung schlaegt weiter an.
# *Nur die Rufzaehler sehen es* -- und genau darum stehen sie in der Erwartung.
lauf "fragment6" "$W/messung/fragmente/F06.gab" "$TREIBER6" \
     "0 0 4096 4096 1 0 1 1 0 1 0 0 0 0 1 0 1 0" \
     's/    muster_schreiben(f);/    \/* geloescht *\//' \
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 2 templates (0 of them UNPROVED), 13 direct forms, 6 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 4e. Das Fragment F9: der Abstieg, und die Schranke steht in der DEKLARATION ---------
#
# **F9 ist der erste Durchstich, dessen Arbeitsfassung dem eingefrorenen Ausschnitt Zeilen
# WEGNIMMT, und das wird hier gesagt statt umgangen** (2026-09-03).
#
# Die anderen Fragmentlaeufe pruefen mit `verlorene_zeilen`, dass keine Ausschnittzeile
# fehlt -- *ergaenzen erlaubt, weglassen nicht.* F9 kann das nicht: der Ausschnitt schreibt
# die neun Merkmalsbits in ein `device … at normal`, und der Erzeuger sagt dazu, dass ein
# Zugriff in den gewoehnlichen Raum kein Geraetezugriff ist. **Die Absage hat recht**, also
# ist der Ausschnitt die falsche Form und nicht der Erzeuger. Dasselbe gilt fuer
# `costs <= 4096 ops` ueber `traverse … over mappings of`: `SPRACHE.md` §5.4 sagt seit
# Stufe 3, dass eine Laufzeit-Traversierung ueber diese Domaene **keine Kostenzusage tragen
# kann** -- der Pruefer rechnete 137 438 953 472 gegen zugesagte 4 096.
#
# Statt „nichts fehlt" prueft dieser Lauf darum das SCHAERFERE: **jede fehlende Zeile muss
# eine der benannten sein.** Eine Zeile, die niemand aufgeschrieben hat, faellt genauso auf
# wie bei den anderen -- und wer eine der benannten wieder aufnimmt, muss sie hier streichen.
schneide "$W/dokumente/FRAGMENTE.md" "module caprock::mmu" > "$ARB/f9.gab"
if ! grep -q "walk Seitenabstieg levels EBENEN" "$ARB/f9.gab"; then
    echo "== EMISSION: F9 NICHT GESCHNITTEN -- der Waechter misst seine eigene Ablage =="
    exit 1
fi
# Die benannten Streichungen, eine je Zeile -- und jede mit ihrem Grund im Kopf von F09.gab.
cat > "$ARB/f9-gestrichen" <<'F9_WEG'
    roh : u64 embeds [51:12] scale 4096,   -- der Rahmen: Bits 51..12, mal 4096
-- Die neun Bits, einzeln benannt. `A` und `D` schreibt die Hardware -- sie stehen als
-- `reserved`, weil ein Schreiben von uns ein Fehler wäre.
device Seitentabelle(basis : Pa) at normal {
    reg EINTRAG : u64 @0x0 class rw fields {
        P @0, RW @1, US @2, PWT @3, PCD @4, A @5, D @6, PS @7, NX @63,
    }
    down : roh when EINTRAG.PS == 0,
    leaf : EINTRAG.PS == 1,
-- Die Schranke faellt aus `levels` mal `node`-Laenge: 4 Ebenen zu 512 Eintraegen.
impl fn rechte_pruefen(w : ptr<normal, r> Seitenabstieg) -> bool
    effects { reads w }
    costs   <= 4096 ops
    traverse abbildung over mappings of w by unvisited
        touches reads w
    {
        if abbildung.level == 3 {
            return true;
        }
    }
    return false;
F9_WEG
# **Die geschweifte Klammer und die Leerzeile tragen keine Aussage** -- ein `format` oder eine
# Typliste kann wachsen, also verschiebt sich ihr Ende. Alles andere wird verglichen.
#
# **EIN Vergleicher fuer alle Fragmente, die etwas streichen** (W7). F9 war der erste, F1 der
# zweite, und eine zweite Abschrift derselben Schleife waere das zweite Register ueber
# derselben Sache.
ungebuchte_streichung() {   # $1 Ausschnitt  $2 Arbeitsfassung  $3 Buchungsliste
    diff "$1" "$2" | sed -n 's/^< //p' | while IFS= read -r z; do
        case "$z" in ""|"}"|"    }") continue ;; esac
        # **`--` vor dem Muster, und das ist kein Schoenheitsfehler:** jede zweite
        # gebuchte Zeile faengt mit `--` an (Gabbros Kommentarzeichen), und `grep`
        # las sie als Option. *Ein Waechter, der an seinem eigenen Gegenstand
        # scheitert, meldet jede Zeile als ungebucht.*
        grep -Fxq -- "$z" "$3" || printf '%s\n' "$z"
    done
}
# $1 Kurzname  $2 Ausschnitt  $3 Arbeitsfassung  $4 Buchungsliste  $5 Sprechprobenmuster
buchung_pruefen() {
    if [ -n "$(ungebuchte_streichung "$2" "$3" "$4")" ]; then
        echo "== EMISSION: $1 hat eine UNGEBUCHTE Zeile des Ausschnitts verloren =="
        ungebuchte_streichung "$2" "$3" "$4" | head -10
        exit 1
    fi
    grep -v "$5" "$3" > "$ARB/$1-kurz.gab"
    if [ -z "$(ungebuchte_streichung "$2" "$ARB/$1-kurz.gab" "$4")" ]; then
        echo "== EMISSION: Sprechprobe $1 haelt nicht -- eine entfernte, NICHT gebuchte"
        echo "             Ausschnittzeile faellt nicht auf. Dieser Vergleich misst NICHTS. =="
        exit 2
    fi
    echo "  ($1: was dem Ausschnitt fehlt, ist genau das Gebuchte -- und eine ungebuchte"
    echo "       fehlende Zeile faellt auf, Sprechprobe ok)"
}
buchung_pruefen "F09" "$ARB/f9.gab" "$W/messung/fragmente/F09.gab" "$ARB/f9-gestrichen" \
                "^const EINTRAEGE: u32 = 512;"
#
# **Was dieser Durchstich misst: den Abstieg, und zwar an der Stelle, an der die Deklaration
# ihn begrenzt.** `walk … levels EBENEN` erzeugt `Seitenabstieg_absteigen` -- eine Schleife
# ueber `levels` Schritte, die je Schritt den Index gegen `node`-Laenge prueft, am Blatt
# haelt und sonst den naechsten Knoten ueber den `embeds`-Rahmen holt.
#
# **Der Aufloeser von Rahmen zu lesbarem Knoten steht im TREIBER**, und das ist keine
# Bequemlichkeit: `walk` sagt, DASS abgestiegen wird, und keine Klausel sagt, wie aus einem
# physischen Rahmen ein lesbarer Knoten wird. Der Erzeuger nimmt ihn darum als Parameter
# entgegen statt ihn zu erfinden. *Genau daran haengt auch die offene Absage von
# `traverse … over mappings of`: eine Laufzeit-Traversierung braucht denselben Aufloeser,
# und in Gabbro gibt es keine Stelle, an der er stuende.*
#
#    Erwartet:  1        -- der Abstieg findet das Blatt: Wurzel[7] steigt ab, Kind[9] ist Blatt
#         2236416        -- `Pte_roh` des Blattes: 0x222 mal 4096, die `embeds … scale`-Rechnung
#               0        -- `rechte_pruefen` auf einem Blatt mit `RW` und ohne `NX`: W^X verletzt
#               1        -- dasselbe auf dem Nachbarblatt mit `NX`: W^X gehalten
#               0        -- der Aufloeser kennt den Rahmen von Wurzel[8] nicht: kein Abstieg
#               0        -- Index 512 an einer Knotenlaenge von 512: die Schranke haelt
TREIBER9='#include <stdio.h>
#include "@ERZEUGT@"
static uint8_t wort[2][512][8];
static Seitenabstieg_knoten knoten[2];
/* Der Aufloeser, den `Seitenabstieg_absteigen` als Parameter verlangt. Er steht von HAND
 * da, weil keine Gabbro-Klausel ihn nennt -- und das ist der Punkt. */
#define KIND_RAHMEN ((uint64_t)0x111u * 4096u)
static bool knoten_zu(uint64_t rahmen, const Seitenabstieg_knoten **k) {
    if (rahmen != KIND_RAHMEN) return false;
    *k = &knoten[1];
    return true;
}
static void setz(int n, int i, uint64_t w) { gabbro_setz_le64(wort[n][i], w); }
int main(void) {
    for (int n = 0; n < 2; n++)
        for (int i = 0; i < 512; i++) {
            knoten[n].eintraege[i].bytes = wort[n][i];
            knoten[n].eintraege[i].len = 8;
        }
    setz(0, 7, ((uint64_t)0x111 << 12) | 1u);                                  /* P, PS = 0 */
    setz(0, 8, ((uint64_t)0x222 << 12) | 1u);                                  /* fremder Rahmen */
    setz(1, 9, ((uint64_t)0x222 << 12) | (1u << 7) | (1u << 1) | 1u);          /* Blatt, RW */
    setz(1, 10, ((uint64_t)0x333 << 12) | (1u << 7) | (1u << 1) | 1u
                | ((uint64_t)1 << 63));                                        /* Blatt, RW+NX */
    const Pte *blatt = 0;
    uint32_t pfad[4] = { 7, 9, 0, 0 };
    int ok = Seitenabstieg_absteigen(&knoten[0], pfad, knoten_zu, &blatt);
    printf("%d %llu %d", ok, (unsigned long long)Pte_roh(blatt), (int)rechte_pruefen(blatt));
    const Pte *b2 = 0;
    uint32_t pfad2[4] = { 7, 10, 0, 0 };
    Seitenabstieg_absteigen(&knoten[0], pfad2, knoten_zu, &b2);
    printf(" %d", (int)rechte_pruefen(b2));
    const Pte *b3 = 0;
    uint32_t pfad3[4] = { 8, 9, 0, 0 };
    printf(" %d", (int)Seitenabstieg_absteigen(&knoten[0], pfad3, knoten_zu, &b3));
    const Pte *b4 = 0;
    uint32_t pfad4[4] = { 512, 0, 0, 0 };
    printf(" %d\n", (int)Seitenabstieg_absteigen(&knoten[0], pfad4, knoten_zu, &b4));
    return 0;
}
'
# **Das Gift dreht `leaf` um.** Danach ist Wurzel[7] (`PS == 0`) das Blatt, der Abstieg
# haelt auf der ersten Ebene, und `Pte_roh` liefert 1118208 statt 2236416. *Ohne diese
# Gegenprobe wuerde die erwartete Zahl nur belegen, dass das Programm nicht konstant ist* --
# sie belegt jetzt, dass die Zahl AUS DEM ABSTIEG kommt und nicht aus dem ersten Eintrag.
lauf "fragment9" "$W/messung/fragmente/F09.gab" "$TREIBER9" \
     "1 2236416 0 1 0 0" \
     's/return (bool)(Pte_PS(it));/return (bool)(!Pte_PS(it));/' \
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 1 templates (0 of them UNPROVED), 5 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 4f. Das Fragment F1: der Kapazitaetsbaum, und der Fehler laeuft bis nach oben --------
#
# **F1 stand an drei Absagen, und keine davon gehoerte Gabbro** (2026-09-03). Zwei `M140`
# meldeten einen Verbund an einem Platz, der eine Zahl erklaert -- `Dma(DmaRef)` an
# `d : DmaObj`, `Reply(ReplyRef)` an `r : ReplyObj`. Beide Seiten stehen im EINGEFRORENEN
# Ausschnitt, vierzig Zeilen auseinander, und widersprechen einander; die dritte Verwechslung
# derselben Sorte (`Memory(Region)` an `MemObj`) bleibt still, weil beide Seiten skalare
# Namen ueber `u64` sind. Die dritte Absage, `N029`, war eine unbezahlte Rechnung:
# `delete_leaf` kann scheitern, und der einzige Rufer sah nicht hin.
#
# **Und hinter der bezahlten Rechnung lagen ZWEI Erzeugerloecher, die vorher niemand sehen
# konnte** -- der Korpus fuehrte `or R` bis dahin nur an `extern fn`. Eine `impl fn` mit
# Fehlerkanal und OHNE Ergebnis hatte gar kein C: der Ruf wurde abgewiesen, und die
# Erfolgsrueckgabe `return true;` schrieb niemand. *Das erste Loch verdeckte das zweite*, und
# `cc -Werror` sagte zu keinem von beiden etwas.
schneide "$W/dokumente/FRAGMENTE.md" "module caprock::cap::space" > "$ARB/f1.gab"
if ! grep -q "spec fn cdt_wohlgeformt" "$ARB/f1.gab"; then
    echo "== EMISSION: F1 NICHT GESCHNITTEN -- der Waechter misst seine eigene Ablage =="
    exit 1
fi
# Die benannten Streichungen, eine je Zeile -- jede mit ihrem Grund im Kopf von F01.gab.
cat > "$ARB/f1-gestrichen" <<'F1_WEG'
    costs     <= 16452480 ops
        delete_leaf(c, o, a, rf, victim);
extern fn free_region(a : ptr<normal, rw> Allok, m : MemObj) effects { writes a } costs <= 32 ops;
extern fn push_dma(rf : ptr<normal, rw> Finalized, d : DmaObj) effects { writes rf } costs <= 8 ops;
extern fn push_reply(rf : ptr<normal, rw> Finalized, r : ReplyObj) effects { writes rf } costs <= 8 ops;
F1_WEG
buchung_pruefen "F01" "$ARB/f1.gab" "$W/messung/fragmente/F01.gab" "$ARB/f1-gestrichen" \
                "^const NOBJECTS : u32 = 4096;"
#
# **Was dieser Durchstich misst.** Vier Slots, ein Baum, ein `revoke` von der Wurzel aus:
#
#     0 (Wurzel)  ->  1  ->  3          Nachordnung: 3, 1, 2
#                 ->  2
#
# Die Nachordnung ist das eine, was der erzeugte Lauf ueber sich selbst behauptet: Blaetter
# zuerst, ohne Stapel, ueber `first_child`/`next_sibling`/`parent`. Der ZWEITE Ruf faehrt den
# Fehlerweg -- ein Objekt mit `refcount == 0` faellt am `narrow … to 1 .. 80255`, und der
# Grund muss durch `delete_leaf` und `revoke` bis in den Treiber laufen.
#
#    Erwartet:  1        -- `revoke` meldet Erfolg
#               1        -- Slot 0 ist NOCH BELEGT: die Wurzel wird durchlaufen, nicht besucht
#           0 0 0        -- Slot 1, 2, 3 sind freigegeben
#               1        -- Objekt 12 stand auf 2 und steht auf 1: kein Finalisierer
#             0 0        -- Objekt 10 und 11 standen auf 1 und sind freigegeben
#               1        -- `push_dma` genau einmal
#               1        -- `push_reply` genau einmal
#               0        -- `free_region` NICHT: Objekt 12 hat den Nullstand nicht erreicht
#     65536 4096        -- die Felder des `DmaRef`, das durch den `match` gereist ist. **Das
#                          ist die Zahl, an der die `M140`-Reparatur haengt**: bis heute
#                          stand hier ein `u64`, und der Verbund waere nicht angekommen
#             0 1        -- der zweite Ruf scheitert, und `Fehler::Buchfuehrung` (= 1) kommt an
TREIBER1='#include <stdio.h>
#include "@ERZEUGT@"
static int n_free, n_dma, n_reply;
static uint64_t dma_phys, dma_len;
void free_region(uint64_t *a, uint64_t m) { (void)a; (void)m; n_free++; }
void push_dma(uint64_t *rf, DmaRef d)     { (void)rf; n_dma++; dma_phys = d.phys; dma_len = d.len; }
void push_reply(uint64_t *rf, ReplyRef r) { (void)rf; (void)r; n_reply++; }
static CapSpace c;
static CapObjects o;
static uint64_t allok, fertig;
static void slot(uint32_t s, uint32_t obj, uint32_t parent, uint32_t kind, uint32_t sib) {
    c.slots[s].used = true;
    c.slots[s].object = obj;
    c.slots[s].parent = parent;
    c.slots[s].first_child = kind;
    c.slots[s].next_sibling = sib;
    c.slots[s].prev_sibling = CapSpace_NONE;
}
int main(void) {
    for (uint32_t i = 0; i < 8; i++) {
        c.slots[i].parent = c.slots[i].first_child = CapSpace_NONE;
        c.slots[i].next_sibling = c.slots[i].prev_sibling = CapSpace_NONE;
    }
    slot(0, 9, CapSpace_NONE, 1, CapSpace_NONE);
    slot(1, 10, 0, 3, 2);
    slot(2, 11, 0, CapSpace_NONE, CapSpace_NONE);
    slot(3, 12, 1, CapSpace_NONE, CapSpace_NONE);
    o.slots[10].used = true; o.slots[10].refcount = 1;
    o.slots[10].kind.marke = ObjectKind_Dma;
    o.slots[10].kind.last.Dma.phys = 65536; o.slots[10].kind.last.Dma.len = 4096;
    o.slots[11].used = true; o.slots[11].refcount = 1;
    o.slots[11].kind.marke = ObjectKind_Reply;
    o.slots[12].used = true; o.slots[12].refcount = 2;
    o.slots[12].kind.marke = ObjectKind_Memory;

    Fehler e = (Fehler)0;
    int ok = revoke(&c, &o, &allok, &fertig, 0, &e);
    printf("%d %d %d %d %d", ok, (int)c.slots[0].used, (int)c.slots[1].used,
           (int)c.slots[2].used, (int)c.slots[3].used);
    printf(" %u %d %d", o.slots[12].refcount, (int)o.slots[10].used, (int)o.slots[11].used);
    printf(" %d %d %d", n_dma, n_reply, n_free);
    printf(" %llu %llu", (unsigned long long)dma_phys, (unsigned long long)dma_len);

    /* Der Fehlerweg. Ein einzelnes Kind mit `refcount == 0` -- der `narrow` faellt, und der
     * Grund muss durch zwei Ebenen bis hierher laufen. */
    slot(0, 9, CapSpace_NONE, 4, CapSpace_NONE);
    slot(4, 13, 0, CapSpace_NONE, CapSpace_NONE);
    o.slots[13].used = true; o.slots[13].refcount = 0;
    Fehler e2 = (Fehler)0;
    int ok2 = revoke(&c, &o, &allok, &fertig, 0, &e2);
    printf(" %d %d\n", ok2, (int)e2);
    return 0;
}
'
# **Das Gift oeffnet die Buchfuehrungsschranke nach unten** -- `>= 1` wird `>= 0`. Der ERSTE
# Ruf aendert sich dadurch nicht (alle drei Zaehlerstaende liegen ueber null); der zweite
# laeuft durch, der Zaehler laeuft unter null um, und `revoke` meldet Erfolg. *Die Gegenprobe
# trifft damit genau die Kette, die dieses Fragment neu gebaut hat: `narrow … else` ->
# Fehlerkanal -> `let … else` -> Weitergabe an den Rufer.*
lauf "fragment1" "$W/messung/fragmente/F01.gab" "$TREIBER1" \
     "1 1 0 0 0 1 0 0 1 1 0 65536 4096 0 1" \
     's/o->slots\[obj\].refcount >= 1/o->slots[obj].refcount >= 0/' \
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 4 templates (1 of them UNPROVED), 13 direct forms, 5 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# -- 4g. Das Fragment F5: der Dienst, und DREI seiner Namen gehoeren C --------------------
#
# **Die drei Absagen an F5 sind nicht an `cc` zu bemerken, und genau darum haelt sie der
# Pruefer** (2026-09-03). `exit`, `signal` und `recv` stehen alle drei im eingefrorenen
# Ausschnitt und bedeuten dort etwas anderes als in C -- `exit() -> never` gegen `void(int)`,
# eine Kapazitaetsbenachrichtigung gegen `__sighandler_t(int, __sighandler_t)`, ein
# seL4-artiger Empfang gegen `ssize_t(int, void *, size_t, int)`. **Die erzeugte Einheit
# bindet keinen dieser Koepfe ein**, also hat der fremde Uebersetzer keinen Konflikt zu
# melden, und der Binder findet das echte Symbol hinter dem, was diese Einheit deklariert
# hat. *Die Absage, die vom fremden Uebersetzer kommen sollte, kann von ihm gar nicht
# kommen.*
#
# Dazu kam, was der Kopf der Datei bestritt: **fuenf Namen, die der Dienstrumpf RUFT, standen
# nirgends** -- und nur einer davon (`decode_op`, am `match`) hatte eine Absage. Die anderen
# vier rief der Rumpf ins Leere, ohne dass ein Pass etwas sagte.
schneide "$W/dokumente/FRAGMENTE.md" "module programs::virtio_blk" > "$ARB/f5.gab"
if ! grep -q "forever dienst" "$ARB/f5.gab"; then
    echo "== EMISSION: F5 NICHT GESCHNITTEN -- der Waechter misst seine eigene Ablage =="
    exit 1
fi
# Die benannten Streichungen, eine je Zeile -- jede mit ihrem Grund im Kopf von F05.gab.
cat > "$ARB/f5-gestrichen" <<'F5_WEG'
    let cfg    = map_window(CFG)    else (e1) { signal(NTFN, 0xD1A6_0001); exit(); }
    let bar    = map_window(BAR)    else (e2) { signal(NTFN, 0xD1A6_0002); exit(); }
    let dmafenster    = map_window(DMA)    else (e3) { signal(NTFN, 0xD1A6_0003); exit(); }
    let teilfenster = map_window(SHARED) else (e4) { signal(NTFN, 0xD1A6_0004); exit(); }
    let pool      = pool_new(dmafenster)    else (e5) { signal(NTFN, 0xD1A6_0000); exit(); }
    let transport = probe_ecam(cfg)  else (e6) { signal(NTFN, 0xD1A6_00FF); exit(); }
    signal(NTFN, 0);
        let m = recv(EP) else (e7) { exit(); }
                -- «B11» hier stuende `leave Stopped;`. Ohne Ausgang bleibt nur `exit()` —
                exit();
extern fn exit() -> never effects { diverges };
extern fn signal(n : u64, w : u64) effects { writes NTFN };
F5_WEG
buchung_pruefen "F05" "$ARB/f5.gab" "$W/messung/fragmente/F05.gab" "$ARB/f5-gestrichen" \
                "^    let mut capacity : u32 = 0;$"
#
# **Was dieser Durchstich misst: die Dienstschleife, einmal ganz herum.** Der Treiber
# schiebt sechs Nachrichten nach -- `Info Read Write Flush Scan Stop` -- und jeder fremde
# Rumpf haengt einen Buchstaben an eine Spur. Die Spur ist damit ein Fingerabdruck der
# ganzen Verteilung, nicht bloss ein Zaehlerstand:
#
#     q  request_flush   p  reply4   1/2  serve_rw mit `m.op`   B  bump_served   S  serve_scan
#
#    Erwartet:  qp12qBpSp -- Info(q,p) Read(1) Write(2) Flush(q,B,p) Scan(S) Stop(p)
#               1 0       -- `benachrichtige` GENAU EINMAL, mit 0: kein Aufbauschritt fiel
#               3 2 2 1 1 -- reply4, request_flush, serve_rw, serve_scan, bump_served
#               4711      -- die Kapazitaet, die `serve_rw` sieht: aus `Info` uebernommen
#               31        -- der Pool, den `bump_served` bekommt: `pool_new(map_window(DMA))`
#               512 77 0  -- das letzte Argument der drei Antworten. **77 ist der
#                            Rueckgabewert von `bump_served`, der in `reply4` einlaeuft**
#
# `1` und `2` sind `m.op` -- **die Zahl, an der die `M134`-Reparatur haengt**: bis heute war
# `recv` als `-> u64` ergaenzt, und ein Verbund mit einem Feld haette nicht reisen koennen.
TREIBER5='#include <stdio.h>
#include <stdlib.h>
#include "@ERZEUGT@"
static char spur[32];
static int sp, n_ntfn, n_reply, n_flush, n_rw, n_scan, n_bump;
static uint64_t letztes_ntfn, letztes_pool, antwort_c[4];
static uint32_t letzte_kap;
static int naechste;
static void merke(char z) { if (sp < 30) spur[sp++] = z; }
bool map_window(uint64_t cap, uint64_t *w, Aufbau *g) { (void)g; *w = cap * 10; return true; }
bool pool_new(uint64_t f, uint64_t *w, Aufbau *g)     { (void)g; *w = f + 1;  return true; }
bool probe_ecam(uint64_t c, uint64_t *w, Aufbau *g)   { (void)g; *w = c + 2;  return true; }
bool empfange(uint64_t ep, Nachricht *m, Aufbau *g) {
    (void)ep; (void)g;
    m->op = (uint64_t)naechste++;
    return true;
}
void reply4(uint64_t ep, Status st, uint64_t a, uint64_t b, uint64_t c) {
    (void)ep; (void)st; (void)a; (void)b;
    if (n_reply < 4) antwort_c[n_reply] = c;
    n_reply++; merke((char)112);
}
void benachrichtige(uint64_t n, uint64_t w) { (void)n; n_ntfn++; letztes_ntfn = w; }
Op decode_op(uint64_t w) { Op o; o.marke = (Op_marke)w; return o; }
uint32_t request_flush(uint64_t t, uint64_t pool) { (void)t; (void)pool; n_flush++; merke((char)113); return 4711; }
void serve_rw(uint64_t ep, uint64_t t, uint64_t pool, uint64_t f, Nachricht m, uint32_t kap) {
    (void)ep; (void)t; (void)pool; (void)f;
    n_rw++; letzte_kap = kap; merke((char)(48 + (int)m.op));
}
void serve_scan(uint64_t ep, uint64_t t, uint64_t pool) { (void)ep; (void)t; (void)pool; n_scan++; merke((char)83); }
uint64_t bump_served(uint64_t pool) { n_bump++; letztes_pool = pool; merke((char)66); return 77; }
_Noreturn void watchdog_schlug_an(void) { printf("WACHHUND\n"); exit(2); }
_Noreturn void dienst_abbruch(void) {
    spur[sp] = 0;
    printf("%s %d %llu %d %d %d %d %d %u %llu %llu %llu %llu\n",
           spur, n_ntfn, (unsigned long long)letztes_ntfn, n_reply, n_flush, n_rw,
           n_scan, n_bump, letzte_kap, (unsigned long long)letztes_pool,
           (unsigned long long)antwort_c[0], (unsigned long long)antwort_c[1],
           (unsigned long long)antwort_c[2]);
    exit(0);
}
int main(void) { run(0); }
'
# **Das Gift nimmt dem `Flush`-Zweig seinen Ruf von `bump_served`.** Das C uebersetzt, die
# Schleife laeuft genauso weit, und nur der Wert, der in die Antwort einlaeuft, ist weg:
# aus `qp12qBpSp … 1 … 31 … 77` wird `qp12qpSp … 0 … 0 … 0`. *Ohne diese Gegenprobe belegten
# dreizehn Zahlen nur, dass das Programm nicht konstant ist.*
lauf "fragment5" "$W/messung/fragmente/F05.gab" "$TREIBER5" \
     "qp12qBpSp 1 0 3 2 2 1 1 4711 31 512 77 0" \
     's/reply4(EP, Status_Ok, 0, 0, bump_served(pool));/reply4(EP, Status_Ok, 0, 0, 0);/' \
     "1 assumptions (0 of them NOT FALSIFIABLE, 1 UNCOVERED -- named a probe that does not exist as a program), 1 templates (0 of them UNPROVED), 10 direct forms, 15 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 2 templates (0 of them UNPROVED), 7 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 1 templates (0 of them UNPROVED), 2 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 2 templates (0 of them UNPROVED), 1 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"


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
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 1 templates (0 of them UNPROVED), 4 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"


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
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 1 templates (0 of them UNPROVED), 6 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"


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
     "2 assumptions (0 of them NOT FALSIFIABLE, 2 UNCOVERED -- named a probe that does not exist as a program), 0 templates (0 of them UNPROVED), 6 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 1 templates (0 of them UNPROVED), 4 direct forms, 3 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"


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
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 1 templates (0 of them UNPROVED), 0 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 2 templates (1 of them UNPROVED), 5 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 1 templates (0 of them UNPROVED), 6 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
     "1 assumptions (1 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 2 templates (1 of them UNPROVED), 3 direct forms, 2 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
     "1 assumptions (0 of them NOT FALSIFIABLE, 1 UNCOVERED -- named a probe that does not exist as a program), 2 templates (1 of them UNPROVED), 4 direct forms, 2 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 0 templates (0 of them UNPROVED), 5 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 2 templates (0 of them UNPROVED), 2 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 2 templates (0 of them UNPROVED), 7 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

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
     "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 1 templates (0 of them UNPROVED), 9 direct forms, 0 foreign bodies (0 state their duty), 0 narrowings from foreign contracts"

# **Die Sprechprobe des Absenkungsmodus, und sie faellt an der Stufe, auf die es ankommt.**
# ---------------------------------------------------------------------------------------
# *Ein Zaehler, der nicht falsch antworten kann, misst nichts* (R14) -- und dieser hier steht
# unter `H`, der Zahl, auf der K100s erstes Tor definiert ist.
#
# Das Gift TAUSCHT zwei Bootschritte von `F07`: `ipc_tabellen` und `autoritaet_melden`
# wechseln die Reihenfolge, die Linearitaet bleibt heil (`p2 -> p3 -> p4`). **Damit prueft
# das Fragment sauber, es emittiert, es UEBERSETZT ohne eine Warnung -- und erst der
# AUSGEFUEHRTE Lauf sagt `124356` statt `123456`.** Genau das ist die Aussage, die der
# Zaehler braucht: nicht dass eine Zeile dasteht, sondern dass das erzeugte C rechnet, was
# das Fragment sagt.
#
# *Ein Gift, das schon beim Pruefen faellt, haette dieselbe Antwort aus einem anderen Grund
# gegeben -- und dann bliebe unbelegt, dass die Ausfuehrungsstufe ueberhaupt mitzaehlt.*
if [ -n "$NUR_ABSENKUNG" ]; then
    echo
    sed -e 's/^    let p3 = ipc_tabellen(p2);$/    let p3 = autoritaet_melden(p2);/' \
        -e 's/^    let p4 = autoritaet_melden(p3);$/    let p4 = ipc_tabellen(p3);/' \
        "$W/messung/fragmente/F07.gab" > "$ARB/f7-vertauscht.gab"
    if cmp -s "$W/messung/fragmente/F07.gab" "$ARB/f7-vertauscht.gab"; then
        echo "SPRECHPROBE GESCHEITERT: das Gift veraendert F07 gar nicht -- die Probe hat"
        echo "  NICHTS gemessen, und ein Gleichstand belegt dann nichts."
        exit 2
    fi
    sp_rc=0
    ( set -e; lauf_kern "sprechprobe7" "$ARB/f7-vertauscht.gab" "$TREIBER7" "123456" \
        's/    ipc_tabellen();/    \/* geloescht *\//' \
        "0 assumptions (0 of them NOT FALSIFIABLE, 0 UNCOVERED -- named a probe that does not exist as a program), 0 templates (0 of them UNPROVED), 4 direct forms, 7 foreign bodies (0 state their duty), 0 narrowings from foreign contracts" \
    ) > "$ARB/sprechprobe7.protokoll" 2>&1 || sp_rc=$?
    if [ "$sp_rc" = 0 ]; then
        echo "SPRECHPROBE GESCHEITERT: ein Durchstich mit VERTAUSCHTEN Bootschritten HAELT."
        echo "  Dann sagt die Zeile DURCHSTICH ... HAELT nichts ueber den Lauf aus."
        exit 2
    fi
    echo "SPRECHPROBE ok (der vertauschte Durchstich faellt, Ruecklauf $sp_rc)"
    sed -n -e 's/^  \(4\. Ergebnis:.*\)$/      \1/p' \
           -e 's/^ *\(erwartet:.*\)$/        \1/p' \
           -e 's/^ *\(bekommen:.*\)$/        \1/p' "$ARB/sprechprobe7.protokoll"
    echo
    echo "== ABSENKUNG: gemessen -- nur die Fragment-Durchstiche, Stufe 9 und 10 nicht =="
    GANZ_DURCH=1
    exit 0
fi

# **Und die Aussage, auf die es bei einem Gatter ankommt: es steht NICHT im C.**
#
# *Ein Gatter, das im C landet, ist kein Gatter* -- ein `#if` haette den ganzen Block
# mitgeliefert und nur den Praeprozessor darueber entscheiden lassen. Hier wird der Baum vor
# dem Erzeuger gefiltert (`gatter::ohne_gatter`), und was das heisst, wird hier gezaehlt.
LETZTE_STUFE="Baugatter"
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
    echo "                 Diese Zaehlung misst NICHTS."; exit 2
fi
echo "  Geruestnamen:  ok (0 im Auslieferungs-C, $n_pr_g im Pruefbau-C)"
echo "  Zeilen:        $(grep -c '' "$ARB/g52-aus.c") gegen $(grep -c '' "$ARB/g52-pruef.c")"
# **Und der Pruefbau muss auch UEBERSETZEN.** Ein Gatter, das nur den kleineren Bau richtig
# macht, verlegt den Fehler in den Bau, in dem die Pruefungen laufen.
if ! cc -std=c11 -Wall -Wextra -Werror -c -o /dev/null "$ARB/g52-pruef.c" 2> "$ARB/g52err"; then
    echo "  Pruefbau cc:   GESCHEITERT"; head -10 "$ARB/g52err"; exit 1
fi
echo "  Pruefbau cc:   ok (-Werror, und die Probe pruefe_puffer_haelt steht darin)"

# **OFFENER BEFUND, aufgedeckt am 2026-08-31 und NICHT gebucht** -- `messung/tor-proben/`.
# ---------------------------------------------------------------------------------------
# Sechs der zwoelf Torproben emittieren C, das nicht uebersetzt:
#
#     bool pruefe_c(void) { ... return; ... }
#     error: 'return' with no value, in function returning non-void [-Werror=return-type]
#
# Alle zwoelf schreiben `can_fail { if k >= 3 { return; } }`. **Ein `can_fail`-Block ist eine
# PROBE und liefert ein `bool`; ein leeres `return` darin hat keinen Wert** -- und kein Pass
# sagt es. `gabbro pruefe` meldet `0 errors, 0 hints`, der Erzeuger schreibt die Zeile
# unveraendert ins C, und `cc -Werror=return-type` ist der einzige Leser. *Dieselbe Familie
# wie `N040`, `N041` und `N043`: eine falsche BESTAETIGUNG, und das dritte Werkzeug findet
# sie.* Die anderen sechs verdecken es -- sie werden schon aus einem anderen Grund abgelehnt.
#
# **Und warum es zwei Wochen niemand gesehen hat, ist der zweite Befund:** Stufe 9 wurde
# nicht erreicht. `pruefe-emission.sh` starb an `F06`s `N043` in Zeile 901 mit `exit 1`, und
# die Stufen 9 und 10 liefen nie -- *ohne dass eine Zeile sagte, was nicht gemessen wurde.*
# Der Ruecklaufwert `1` sah aus wie ein Stufenbefund und war zugleich ein Abbruch fuer alles
# dahinter. **Genau die Klasse, die `messung/RUECKLAUFWERTE.md` unter „Was offen bleibt"
# fuehrt: ein Waechter, dessen Vorbedingung MITTEN im Lauf wegbricht.**
#
# *Nicht als Ausnahme gebucht.* Die Liste unten ist leer und soll es bleiben; sechs Dateien
# hineinzuschreiben machte aus einer Erzeugerluecke eine gruene Zeile. Der Waechter bleibt
# rot, bis die Regel steht oder die Proben `return false;` schreiben -- beides gehoert dem,
# der `messung/tor-proben/` und die `check`-Regeln fuehrt.
#
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
LETZTE_STUFE="Stufe 9 (jede emittierende Datei uebersetzt)"
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

# **Die REICHWEITE der Regel endete bis zum 2026-08-31 an `beispiele/`** -- und darin lag
# genau die Luecke, gegen die die Regel gebaut ist, eine Ebene hoeher.
#
# `messung/fragmente/F06.gab` emittierte 161 Zeilen und fiel bei `cc -Werror=type-limits`:
# *"comparison is always true due to limited range"*. **Die Datei liegt seit dem 2026-08-14
# im Baum, und keine Stufe hat gefragt** -- weil sie unter `messung/` liegt und nicht unter
# `beispiele/`.
#
# > *Eine Regel, deren Gegenstand die Sprache ist und deren Reichweite ein Verzeichnis, misst
# > das Verzeichnis.* Dieselbe Bauart wie die Liste, die diese Regel abgeloest hat.
#
# `messung/*/*.gab` kommt dazu: Fragmente, ABI-Proben, Treiber, Netz, Grenze, Caprock. Was
# `C001` sagt, faellt wie zuvor aus dem Nenner -- eine Weigerung ist eine ehrliche Antwort.
#
# =======================================================================================
# **Und am Abend desselben Tages endet sie an gar keinem Verzeichnis mehr** (2026-08-31).
#
# `pruefe-grammatiktafel.py` stellt seit heute dieselbe Frage -- und sah **88** Dateien, wo
# diese Stufe **83** sah. *Zwei Register ueber derselben Sache sind `W7`*, und hier sagte das
# eine `83 von 83`, waehrend das andere eine Datei kannte, die es nicht sah. Nachgemessen ueber
# alle 431 `.gab` des Baumes (`messung/REICHWEITE-DER-REGEL.md`):
#
#     R9  `beispiele/*.gab` + `messung/*/*.gab`      109 Dateien     83 davon emittieren
#     RT  der ganze Baum, ohne target/.claude/.lake  431 Dateien     88 davon emittieren
#     RT \ R9  322          R9 \ RT  0
#
# Die letzte Null ist die tragende: **diese Stufe sah keine Datei, die die Tafel nicht auch
# sah** -- eine echte Teilmenge. Die fuenf fehlenden emittierenden waren `gift/286`,
# `gift/413`, `messungen/narrow`, `messungen/tabelle`, `programmlogik/beispiel/lager`, und
# **`gift/413` uebersetzt nicht.** *Eine Regel, die ueber einer Teilmenge haelt, haelt ueber
# der Teilmenge.*
#
# ## Warum die Grenze nicht am Verzeichnis `gift/` bleibt
#
# Das Argument dafuer laege nahe: *Giftproben emittieren mit Absicht kaputtes C.* Gemessen ist
# es falsch, und nicht knapp -- **2 von 317 Giftproben emittieren ueberhaupt**, die anderen 315
# weist der Pruefer oder `C001` ab und sie kommen am C-Tor nie an. Der Filter *„emittiert
# vollstaendig"* schliesst sie laengst aus, und aus dem richtigen Grund. Eine Verzeichnisregel
# schloesse zusaetzlich `gift/286` aus, **das gruen uebersetzt**, und `gift/413`, **das die
# einzige Fundstelle dieser Regel im ganzen Baum ist.**
#
# ## Die Grenze steht jetzt an dem, was die DATEI ueber sich selbst sagt
#
# `gift/413` traegt `-- erwartet: cc` in der ersten Zeile: der Pruefer muss schweigen **und**
# `cc` muss ablehnen (`crates/gabbro-check/tests/beispiele.rs`). Fuer so eine Datei ist die
# Regel dieser Stufe **umgekehrt**, und darum steht sie nicht in `ausnahme_grund()`:
#
#     -- erwartet: cc      das C MUSS fallen.  Faellt es nicht, beisst die Probe nicht mehr.
#     alles andere         das C MUSS stehen.
#
# **Die Ausnahmeliste bleibt damit leer, und das ist kein Kunstgriff.** Ein Eintrag dort waere
# ein *Befund mit Adresse*, der einmal ablaeuft; `-- erwartet: cc` ist keiner -- es ist die
# Zusage der Datei, dass ihr C fallen soll. Eine Liste haette ausserdem einen Eintrag je
# `-- erwartet: cc`-Probe gebraucht, **also ein zweites Register des Giftkorpus** -- genau das
# `W7`, gegen das diese Ausdehnung gebaut ist. *Dieselbe Bewegung wie am 2026-08-20: die REGEL,
# nicht die Liste.*
#
# Und die Umkehrung misst in beide Richtungen: **eine `-- erwartet: cc`-Probe, deren C
# ploetzlich uebersetzt, ist ein Rot** -- entweder ist der Erzeugerfehler geheilt (dann gehoert
# die Probe fort) oder sie trifft nicht mehr. *Eine Probe, die nicht mehr beissen kann, liest
# sich wie eine, die es nie konnte.*
#
# =======================================================================================
# **AND THE RULE ASKS A SECOND COMPILER FAMILY SINCE 2026-09-02.**
#
# `cc` is a symlink on `gcc` on both machines this tree is measured on -- gcc 16.2.1 here and
# gcc 13.3.0 on `ki-pc-fisch-101`. Every green line of this stage until today therefore said
# *"it compiles with gcc"*, and nothing said so.
#
# The occasion is a generator defect that reached the tree at `0e328c7`: an `exchange update`
# body answering on one path only handed the compare-exchange a value the emitter never wrote.
# `gabbro pruefe` said `0 errors`, `gabbro emit` left with `0`, and `cc -Wall -Wextra` was
# silent at `-O0`, `-O1` AND `-O2` -- *the whole of what this stage asked.* The second family
# names it in one line, and with the SAME flag word this stage already uses:
#
#     error: variable '_cn1' is used uninitialized whenever 'if' condition is false
#            [-Werror,-Wsometimes-uninitialized]
#
# **The added flag set is EMPTY, and that is the whole finding of the census behind this
# block** (2026-09-02, 120 emitting units, both machines, clang 18.1.3 and clang 22.1.8):
#
#     clang -std=c11 -Wall -Wextra              0 diagnostics over 120 of 120 units
#     + -Wsometimes-uninitialized               0 -- and it is INSIDE `-Wall` already
#     + -Wconditional-uninitialized             0
#     + -Wshadow                                0
#     + seven -Wtautological-*                  0
#     + -Wcast-align                          100 over 15 units -- and gcc's
#                                               `-Wcast-align=strict` names the IDENTICAL
#                                               15 units with identical per-unit counts,
#                                               so it is not a family difference at all
#     + -Wunreachable-code-aggressive          37 over 10 units -- every one the emitter's
#                                               deliberate terminator after a block that
#                                               already answers. A gate red on 10 of 120
#                                               units on its first day is not a gate.
#
# **`8` stood there until 2026-09-02 and the unit count was wrong; the hit count was not.**
# Re-measured on both machines, clang 18.1.3 and clang 22.1.8, same cache of emitted C:
# 37 hits over **10** units -- `beispiele/08`, `13`, `31`, `34`, `39`, `40`, `41`, `42`, `48`
# and `messung/fragmente/F08`, split over four sub-tags (`-break` 24/6, plain 7/5,
# `-return` 5/3, `-loop-increment` 1/1). *Four tag-wise unit counts are not one unit count:
# they sum to 15, their union is 10, and 8 is neither.* The conclusion above is untouched
# by the correction, and it is worth saying that it is untouched rather than quietly fixing
# the digit: a number that changes without moving its argument was carrying no weight.
#
# *One switch that catches a wrong value going into a CAS is worth more than twenty that
# catch braces* -- and here the one switch is not a switch, it is the second compiler.
# `-Wsometimes-uninitialized` rides in on `-Wall`; naming it would add a word and nothing else.
#
# **Why HERE and not in `pruefe-uebersetzerfamilie.py`, which already runs both families.**
# That tool books `0 differences` and its zero is TRUE. Three measured reasons, and the third
# is the one that settles it:
#
#   1. Its flags were never the problem -- they are this stage's flags, and they name the
#      defect verbatim on both machines.
#   2. Its population is *`.gab` files in the tree that emit today*. The defect lived in
#      `emit.rs`; no committed unit triggered it, so the corpus never held it.
#   3. And the corpus never CAN hold it. The one file that carries the shape --
#      `beispiele/gift/658-an-update-body-that-falls-through.gab`, written by the same
#      commit -- is `-- erwartet: C001`: the emitter refuses it, so it never emits and falls
#      out of that tool's denominator. **The probe that documents the defect is invisible to
#      the instrument that would have named it.**
#
# > *A corpus differ can only find a generator defect that some committed file happens to
# > trigger.* It is a census over what is already in the tree, and it runs after the fact.
# > A gate runs at the moment a unit arrives. They are two questions, and this is the one
# > that was not being asked.
#
# `clang` exists on both machines and the census is identical across four major versions
# (18.1.3 against 22.1.8, same 137 hits, same units, same counts), so a gate that leans on it
# runs where this tree is measured. **A missing `clang` colours this stage red** -- W1, the
# same reading the head of this file gives a missing `cc`: an absent tool is not a passed
# test, and 120 green lines would then be a statement about gcc and about nothing else.
n_emit=0; n_ok=0; n_aus=0; n_umg=0; schlecht=0
n_clang_ok=0; n_umg_nur_cc=0; umg_nur_cc=""
# `set -e` reads an `a && b` whose `a` fails as a failed command, so this is an `if`.
HAT_CLANG=0
if command -v clang > /dev/null; then HAT_CLANG=1; fi
n_emit_b=0; n_emit_g=0; n_emit_m=0; n_emit_n=0; n_emit_p=0; n_emit_x=0; rest_x=""
# **Der `find` bildet die Reichweite der Tafel NACH, und zwar ueber Namen statt ueber Pfade.**
# `-name` sieht nur den letzten Bestandteil; ein Muster auf den ganzen Pfad haette denselben
# Fehler gemacht wie der erste Auszaehler der Tafel, deren Wurzel selbst
# `…/.claude/worktrees/agent-X` heisst -- *dort passte der absolute Pfad auf jede Datei, und
# der Korpus ging auf null.*
while IFS= read -r q; do
    d="${q#"$W"/}"
    if ! cargo run -q --manifest-path "$W/Cargo.toml" --bin gabbro -- emit "$q" \
            > "$ARB/regel.c" 2>/dev/null || [ ! -s "$ARB/regel.c" ]; then
        continue          # `C001` weigert sich -- eine Weigerung ist eine ehrliche Antwort.
    fi
    n_emit=$((n_emit + 1))
    # `beispiele/gift/*` steht VOR `beispiele/*`: in einem `case`-Muster ueberspringt `*`
    # sehr wohl einen `/`, anders als im Glob der Shell.
    case "$d" in
    beispiele/gift/*) n_emit_g=$((n_emit_g + 1)) ;;
    beispiele/*)      n_emit_b=$((n_emit_b + 1)) ;;
    messung/*)        n_emit_m=$((n_emit_m + 1)) ;;
    messungen/*)      n_emit_n=$((n_emit_n + 1)) ;;
    programmlogik/*)  n_emit_p=$((n_emit_p + 1)) ;;
    *)                n_emit_x=$((n_emit_x + 1)); rest_x="$rest_x $d" ;;
    esac
    umgekehrt=0
    [ "$(head -1 "$q")" = "-- erwartet: cc" ] && umgekehrt=1
    if cc -std=c11 -Wall -Wextra -Werror -c -o /dev/null "$ARB/regel.c" 2> "$ARB/regelerr"; then
        if [ "$umgekehrt" = "1" ]; then
            echo "  PROBE BEISST NICHT MEHR: $d sagt \`-- erwartet: cc\`, und cc nimmt das C an."
            echo "        Entweder ist der Erzeugerfehler geheilt -- dann gehoert die Probe fort --"
            echo "        oder sie trifft nicht mehr. Beides ist ein Befund, keines ein gruener Lauf."
            schlecht=1
        else
            n_ok=$((n_ok + 1))
            # **The second family, and the SAME flag word.** A different flag set here would
            # measure the flags and not the family (the census above says the extra switches
            # yield nothing a reader would act on).
            if [ "$HAT_CLANG" = "1" ]; then
                if clang -std=c11 -Wall -Wextra -Werror -c -o /dev/null "$ARB/regel.c" \
                        2> "$ARB/clangerr"; then
                    n_clang_ok=$((n_clang_ok + 1))
                else
                    echo "  NUR CLANG LEHNT AB: $d -- cc nimmt dasselbe C an."
                    echo "        Das ist kein Stilbefund: die Familien lesen denselben Text, und"
                    echo "        eine Meldung, die nur eine von beiden kennt, hat der Erzeuger"
                    echo "        trotzdem verdient. Nachsehen mit:"
                    echo "        ./target/debug/gabbro emit $d | clang -std=c11 -Wall -Wextra -Werror -c -o /dev/null -"
                    head -3 "$ARB/clangerr" | sed 's/^/      /'
                    schlecht=1
                fi
            fi
            if grund="$(ausnahme_grund "$d")"; then
                echo "  ABGELAUFENE AUSNAHME: $d uebersetzt jetzt -- der Eintrag gehoert geloescht"
                echo "                        (stand da als: $grund)"
                schlecht=1
            fi
        fi
    elif [ "$umgekehrt" = "1" ]; then
        n_umg=$((n_umg + 1))
        echo "  umgekehrte Probe  $d -- \`-- erwartet: cc\`, und cc lehnt ab. Sie beisst:"
        head -1 "$ARB/regelerr" | sed 's/^/      /'
        # **A poison probe whose bite depends on the compiler family measures the family.**
        # The marker says `cc` and this branch keeps its verdict, so clang does not colour
        # the single file -- the COUNT does, one mark below, and it is debt.
        if [ "$HAT_CLANG" = "1" ] \
           && clang -std=c11 -Wall -Wextra -Werror -c -o /dev/null "$ARB/regel.c" 2>/dev/null
        then
            n_umg_nur_cc=$((n_umg_nur_cc + 1)); umg_nur_cc="$umg_nur_cc $d"
        fi
    elif grund="$(ausnahme_grund "$d")"; then
        n_aus=$((n_aus + 1))
        echo "  ausgenommen  $d -- $grund"
    else
        echo "  UEBERSETZT NICHT: $d"
        head -3 "$ARB/regelerr" | sed 's/^/      /'
        schlecht=1
    fi
done < <(find "$W" \( -name target -o -name .claude -o -name .lake \
                    -o -name arbeitsprotokoll \) -prune \
              -o -name '*.gab' -print | sort)
n_nenner=$((n_emit - n_umg))
echo "  $n_ok von $n_nenner emittierenden Dateien uebersetzen; $n_aus benannte Ausnahmen,"
echo "  $n_umg umgekehrte Proben (\`-- erwartet: cc\`) -- zusammen $n_emit, die emittieren"
echo "  ($n_emit_b beispiele/, $n_emit_g beispiele/gift/, $n_emit_m messung/*/,"
echo "   $n_emit_n messungen/, $n_emit_p programmlogik/, $n_emit_x sonst -- SECHS Marken)"

# **Mark: reverse probes that bite under `cc` ALONE.** They are DEBT, not an achievement --
# pulled onto the measured stand, and the number may only fall.
#
# **Booked at 1 on 2026-09-02**: `beispiele/gift/642-a-forever-loop-in-a-function-that-
# answers.gab`. `cc` rejects it with `no return statement in function returning non-void`
# (`-Werror=return-type`); `clang` stays silent because it sees that the `for (;;)` never
# falls out. *The probe therefore says something about gcc and not about the artefact.* The
# nine others are rejected by both and are untouched by this -- measured under clang 18.1.3
# and 22.1.8 with the same result.
#
# The repair belongs to the probe and not to this guardian: either it carries a reason both
# families read, or its own first line says which family it means.
#
# **1 -> 0 on 2026-09-03, and it took neither of the two repairs the note offered.** `642`
# stopped being a reverse probe altogether: the emitter now refuses the shape by name
# (`D2`), the file is headed `-- erwartet: C001`, and no compiler is asked about it any
# more. *The debt is discharged at its source rather than papered over at the measurement* --
# and the disagreement between the families is settled the honest way, because the one
# family that was silent was silent for a REASON: clang sees the `for (;;)` never falls out.
# **So did the emitter, and it wrote the declaration anyway.**
MARKE_UMG_NUR_CC=0

# **The SECOND family, and its number stands BESIDE the first one and not instead of it.**
if [ "$HAT_CLANG" = "1" ]; then
    echo "  $n_clang_ok von $n_ok, die cc annimmt, nimmt auch \`clang\` an"
    echo "  ($(clang --version 2>/dev/null | head -1) gegen $(cc --version 2>/dev/null | head -1))"
    # **The number stands there EVERY run and not only when it misses the mark.** A ratchet
    # that says nothing while it holds leaves the reader guessing whether it measured.
    echo "  $n_umg_nur_cc von $n_umg umgekehrten Proben beissen nur unter \`cc\`"
    echo "  (Marke $MARKE_UMG_NUR_CC -- SCHULD, gezogen und nicht geheilt)"
else
    # W1, the same reading the head of this file gives a missing `cc`.
    echo "  ZWEITE FAMILIE: \`clang\` gibt es auf dieser Maschine nicht -- die $n_ok gruenen"
    echo "                  Zeilen darueber sind eine Aussage ueber GCC und ueber sonst nichts."
    echo "                  Ein fehlendes Werkzeug ist kein bestandener Test (W1)."
    schlecht=1
fi

if [ "$HAT_CLANG" = "1" ] && [ "$n_umg_nur_cc" -ne "$MARKE_UMG_NUR_CC" ]; then
    if [ "$n_umg_nur_cc" -gt "$MARKE_UMG_NUR_CC" ]; then
        echo "  RATSCHE GEBROCHEN: $n_umg_nur_cc umgekehrte Proben beissen nur unter \`cc\`,"
        echo "                     gebucht ist $MARKE_UMG_NUR_CC. Eine Probe, die nur unter EINER"
        echo "                     Familie beisst, misst die Familie:$umg_nur_cc"
    else
        echo "  FUND: nur noch $n_umg_nur_cc statt $MARKE_UMG_NUR_CC umgekehrte Proben beissen"
        echo "        allein unter \`cc\` -- die Marke gehoert nachgezogen (der gute Fall, und"
        echo "        trotzdem ein Befund)."
    fi
    schlecht=1
fi

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
# **52 -> 53 am 2026-08-30**: `beispiele/54-divergenz-leckt-nicht.gab` kam dazu -- die
# Datei, an der `m2::endet` einen divergierenden Zweig nicht mehr als Leck ablehnt
# (`messung/ABSTIEG.md`). Sie emittiert und uebersetzt, also gehoert sie in den NENNER.
#
# **ZWEI Marken seit dem 2026-08-31, und nicht eine Summe.** Eine Summe ueber zwei
# Verzeichnissen laesst sich ausgleichen: eine Datei verlaesst `beispiele/`, eine kommt in
# `messung/` dazu, und die Zahl steht still. *Genau die Bewegung, gegen die diese Ratsche
# gebaut ist* -- also steht sie je Wurzel da.
#
# **53 -> 54 am 2026-08-31**: `beispiele/53-zwei-orte.gab` kam dazu. `breaking I { … }`
# senkt seit diesem Tag ab -- die Weigerung stand auf *„emitting it would drop the region"*,
# und `gabbro pflichten` bucht die Erhaltungspflicht laengst (`messung/ZWEI-ABSAGEN.md`).
#
# **54 -> 57 am selben Abend, und der Grund steht hier statt in einem Merge:** die drei
# Programme fuer die Quantorendomaenen `chain`, `queue` und `threads` (`beispiele/55`-`57`,
# `messung/QUANTORENDOMAENEN.md`). Der Waechter hat sie selbst gemeldet -- *„FUND: 57 statt 54
# emittierende Dateien in beispiele/ -- die Marke gehoert nachgezogen (der gute Fall, und
# trotzdem ein Befund)"* -- und genau so ist sie nachgezogen: **der Gegenstand ist gewachsen,
# also darf die Zahl steigen, und der Grund steht an der Marke.**
# **57 -> 62 on 2026-09-01, and the OBJECT grew.** Five clean examples came with the
# night's work: `58` (free list, two forms), `59` (an entry that hardware throws), `60` (an
# assumption naming its machine), `61` (`~`), `62` (`u32::max` in an expression). Every one
# is the counterprobe a build was not allowed without.
# **62 -> 63 on 2026-09-01, and the object grew by the one example that had been
# impossible**: `beispiele/63-druckt.gab`, the first Gabbro program that PRINTS. Until that
# day `N041` refused every `extern fn` on a name C owns, and `putchar`, `puts` and `printf`
# are all three such names -- so the corpus had no program with output at all.
# **63 -> 64 on 2026-09-02, and the object grew by the SECOND printing program**:
# `beispiele/64-writes-a-whole-buffer.gab` writes a whole buffer through ONE `write(fd, p, n)`
# instead of a `putchar` per byte. It is the counter-form of `N052`: what is bound is what
# carries its end in the SIGNATURE, and `requires n <= KAP` is the obligation `M115` then
# discharges at the call site. *A terminator scan leaves nothing to discharge.*
# **64 -> 65 on 2026-09-02, and the object grew by a SPACE the emitter used to refuse whole**:
# `beispiele/65-port-space.gab`, a 16550 at COM1 as a `device … at port`. Every access form in
# it lowers to an `in`/`out` instruction -- register read, register write, field read, an
# acknowledgement, a bit-field read-modify-write, a `transition` -- where the emitter used to
# answer `C001` for all of them at once. *Rule A's second half: no refusal without a measured
# defect, and the defect under this one had been repaired.*
MARKE_EMIT=65
# **22 aus `messung/*/*.gab`, gemessen 2026-08-31** -- 6 Fragmente (F02, F04, F06, F07, F08,
# F10), 4 W24-Proben dieses Tages (`messung/proben/`), **2 aus der Grammatik geschriebene
# Dateien** (`messung/grammatik/`), 5 ABI-Proben, 2 Caprock, Grenze, Netz, Treiber.
# `F06` ist die Datei, die die Ausdehnung ueberhaupt ausgeloest hat: sie emittierte und
# uebersetzte NICHT, und keine Stufe hat sie je angesehen.
#
# **19 -> 22 am selben Tag, und der Zuwachs ist der Ertrag von `pruefe-grammatiktafel.py`:**
# die zwei `messung/grammatik/`-Dateien schliessen NEUN Terminale, die die Grammatik erlaubt
# und die kein Programm des Baumes je geschrieben hatte -- `i8`, `i16`, `i32`, `i64`, `f32`,
# `and`, `port`, `rc`, `seq`. *Was 0 Fundstellen hat, ist nicht geprueft, sondern
# unerreichbar* -- und keine dieser neun Absenkungen war je gelaufen.
#
# **22 -> 25 am 2026-08-31, Bahn F5.** Drei Gegenproben aus `messung/proben/`, und jede ist
# die freundliche Seite einer neuen Absage -- *eine Regel, die 558 Namen oder jeden
# Feldzugriff abweist, ist nur dann eine Regel und keine Wand, wenn die Nachbarn durchgehen:*
#
#   `probe-c-namen-frei.gab`       `read` `write` `open` `close` `signal` -- POSIX, nicht C,
#                                  und damit KEINE Namen, die `N041` vergeben nennt
#   `probe-feldzugriffe-frei.gab`  Verbundfeld, Registerfeld und GERAETEPARAMETER -- die
#                                  dritte Lage hat `M134` im ersten Bau widerlegt
#   `probe-let-ohne-leser.gab`     die ungelesene `let`-Bindung, die jetzt `(void)r2;`
#                                  absenkt statt abgewiesen zu werden
# **25 -> 29 am 2026-08-31, und das ist ein Zuwachs des GEGENSTANDS.** Vier aus der
# Grammatik geschriebene Programme kamen dazu (`messung/grammatik/`), damit kein Wort der
# EBNF mehr an einer einzigen Datei haengt -- die Einsamkeitszahl fiel von 25 auf 0. Der
# Waechter nennt es selbst *„der gute Fall, und trotzdem ein Befund"*: eine Marke, die
# steigt, weil mehr uebersetzt, ist keine gelockerte Ratsche. *Der Grund steht hier, damit
# die naechste Sitzung nicht eine Lockerung liest.*
# **29 -> 30 on 2026-08-31.** A counter-probe to `N042`
# (`messung/proben/probe-erzeugernamen-frei.gab`): six words that LOOK like a suffix the
# generator adds and are none -- `fn gueltig`, `const Kappe_speicher`, `type Baum_knoten`, a
# field `setz_b` without a field `b`, a field `marke` in a `format`, a variant `gueltig` in a
# `tagged type`. *A word list would have refused all six*, and that is exactly why `N042`
# enumerates the names the generator forms instead of forbidding words. The probe emits and
# compiles -- the same good case as above.
# **30 -> 31 on 2026-08-31, and the file that came in is a COUNTER-PROBE to a narrowing.**
# `messung/stille-proben/m6-order.gab` writes `atomic ZAEHLER : u32 relaxed` next to
# `const ZAEHLER_ORDER`. Until that day `N042` refused it, and the refusal had no defect
# under it: the emitter writes `#define {A}_ORDER` only where the ordering is not
# `relaxed`-without-payload, so the unit held exactly ONE `ZAEHLER_ORDER` -- the writer's --
# and `cc -Werror` took it. **That this file EMITS is now the measurement**: an emitted unit
# is one the checker let through, so stage 9 holds both halves of the narrowing at once.
# *Its six brothers in that directory do NOT emit, because `N042` refuses them -- which is
# what they are there to show.*
#
# **30 -> 31 on 2026-08-31, and it is a GROWING SUBJECT again.**
# `messung/proben/probe-neun-domaenen.gab` carries all NINE quantifier domains in one unit,
# each in an `ensures` -- the carrier on which `messung/DOMAENENNAMEN.md` sets its 32
# falsifications, and the one place where `fields of` stands in a program at all (it had
# ZERO sites in the whole corpus). It emits and compiles.
#
# > *And it did not, in its first cut.* The `walk` descended through a `reserved` field, and
# > the generator emitted a call to an accessor it does not generate -- `implicit declaration
# > of function 'Wort_rest'`. **Stage 9 caught it, and no other stage would have**: `gabbro
# > pruefe` said 0 errors and `gabbro emit` said 0 `C001` over exactly that text. A
# > measurement carrier that does not compile measures the checker and nothing else.
# **UNGEPRUEFT ueber der VEREINIGUNG, 2026-08-31.** Beide Bahnen massen 30 -> 31, jede fuer
# eine ANDERE Datei; die Vereinigung ist damit hoeher, und Stufe 9 bricht vorher an `F06`
# ab (`N043`). *Eine Marke, die niemand gemessen hat, waere schlimmer als eine, die faellt* --
# also steht hier die belegte Zahl, und der naechste volle Lauf nennt die richtige als FUND.
#
# **31 -> 38, und der naechste volle Lauf war der vom 2026-08-31 nach `F06`s Heilung.** Der
# Waechter hat die Zahl selbst als FUND genannt (*"38 statt 31 emittierende Dateien in
# `messung/*/` -- die Marke gehoert nachgezogen"*). Die Zeile stand ZWEIMAL untereinander da,
# beide Male mit 31 -- der Merge hat sie doppelt gelegt, und die zweite ueberschrieb die
# erste mit demselben Wert. *Ein Doppeleintrag, der nicht auffaellt, weil beide Zweige
# dasselbe massen, ist der Vorbote eines, bei dem sie es nicht tun.*
#
# **38 -> 39 on 2026-08-31**, and the subject grew by one file:
# `messung/proben/probe-stellungen.gab` -- the nine quantifier domains in `requires`, in an
# `invariant` and in the body of a `spec fn`, the carrier of the position measurement in
# `messung/DOMAENENSTELLUNGEN.md`. It is annotations only, so it lowers to C and compiles.
# *A floor that lags behind the corpus is slack, not safety.*
#
# **39 -> 40 on 2026-08-31**, same reason and one file further:
# `messung/proben/probe-probenurteil-schleife.gab` -- a probe whose only exits stand inside
# a `forever`, the carrier of the `N045` measurement. It checks green since the false
# refusal there was repaired, so it lowers to C and compiles.
# **40 -> 45 on 2026-09-01**, same movement: the measurement probes for certificate
# injectivity, two-gibibyte linking, witness duty, wildcard reset and loop-promise shadowing.
# **45 -> 46 on 2026-09-01** (`OB5`): `messung/einheit-proben/prog-vorrat.gab`, the carrier
# file of the two-unit program. It declares a table and no body, so it lowers alone; its
# three companions do NOT -- two need the other file of their unit and one needs the `.gabi`
# across the unit boundary. *A corpus of units has files that only translate together, and
# this ratchet counts the ones that do not have to.*
# **46 -> 47 on 2026-09-01**: `messung/proben/probe-extern-bindet-c.gab`, the counter-probe
# to `N046` -- five `extern fn` on names C already declares, each with the signature C knows.
# It lowers alone and compiles, which is the whole claim it makes.
# **47 -> 52 on 2026-09-01, and the five files are the `B001` entry corpus** (`1c9243c`).
# `probe-eintritt.gab` is the hosted entry itself, `-ungebunden` the rebuilt speaking probe
# for the LINK step; both lower and compile. The other three -- `-parameter`, `-privat`,
# `-zwei` -- carry `-- erwartet: cc` and stand in this denominator exactly the way
# `gift/414` does: they emit, and their C MUST fall. *The object grew by five, and the
# ratchet counts emitting files, not passing ones.*
# **The number stays 52 on 2026-09-02, and it is a DIFFERENT 52 -- two files traded places,
# and each move is worth its own line.**
#
# Measured, not assumed: the base binary of `178e260` emits **51** files under `messung/`,
# so this mark was ALREADY broken at master, in the direction its own message names -- *a
# file has LEFT emission.* The file is `messung/fragmente/F01.gab`, and it left through
# `D021` (`fb258db`): the pass now refuses a place's base name that no declaration carries,
# and `F01` had named `WURZEL` into the void since it was written. **That is the good
# direction** -- the checker catches it before the emitter is asked -- and nobody pulled the
# mark down behind it.
#
# The file that arrives is `messung/proben/probe-port-nachfrage.gab`. It was written to
# measure the demand that `emit.rs`'s `at port` refusal named as its own condition -- *"zero
# `device … at port` in 426 files"* -- and it checked with 0 errors and refused at the
# emitter, which is why it was not in this number. It lowers since the `in`/`out` work.
#
# > *A number that is right again for a reason it was not booked for is exactly the case
# > this file's own ratchet message warns about,* so it is written out rather than left to
# > look like nothing happened.
#
# **-> 53 the same day, and the third file is a REGRESSION probe.**
# `messung/proben/probe-griffname-doppelt.gab` holds a device handle bound by `let` under a
# name another function takes as a pointer -- the shape in which `geraetezeiger` beat
# `geraetewerte` and the artefact wrote `c->basis` about a value. Checker silent, emitter
# exit 0, `cc` refusing: the one reader was the C compiler, and this stage is where it now
# reads at every run.
# **53 -> 54 on 2026-09-03**: `messung/proben/probe-literal-past-the-signed-end.gab`, which
# arrived from `beispiele/gift/643`. Its program was always correct Gabbro; what was wrong
# was the C, which carried `18446744073709551615` with no `u` on it. **A file that stops
# being poison does not stop being a probe** -- here it holds the emitter to writing the
# suffix, under `-Werror`, at every run of stage 9.
# **54 -> 55 on 2026-09-03**: `messung/proben/probe-static-past-the-signed-end.gab`, and it
# is the SAME repair one slot further along. `D3` named nine sinks and closed seven; the
# `static` initialiser was one of the two it missed, because the suffix grew in the
# expression path and a `static` value never travels it. *A repair reported by the slot it
# was found at, rather than by the slots its own count names, leaves a residue* --
# `messung/ERZEUGERREST.md` §4. This file holds the eighth sink under `-Werror` at every run.
# (die 55 von `master` steht in der Notiz darueber; die zusammengefuehrte Zahl wird GEMESSEN)
# **54 -> 56 on 2026-09-03, and BOTH are fragments that Gabbro used to refuse.**
# `messung/fragmente/F09.gab` and `messung/fragmente/F01.gab` emit since the `H = 0` work:
# F9 after `walk … levels` learned to read a `const` name and its `device … at normal` was
# replaced by the `format` that word belongs in, F1 after three `extern fn` lines were made
# to agree with the `tagged type` forty lines above them and `N029` was paid. *A mark that
# rises because a REFUSAL was right and the corpus was wrong* -- and stage 9 now holds the
# C of both against `-Werror` at every run.
#
# **56 -> 57 the same day, and the third one is a REGRESSION probe.**
# `messung/proben/probe-fehlerkanal-ohne-ergebnis.gab` holds an `or R` at an `impl fn`
# WITHOUT a result -- the shape that had no C at all until 2026-09-03, because the call
# side of `let … else` asked for the type of a result the declaration does not have.
# *It is a clean probe and not a poison on purpose:* the counter-direction that remains
# is `N028`'s, and the checker says it before the emitter gets there, so a poison on it
# would only raise the `verdeckt` mark of `zaehle-gifttreffer.py`. **This stage is the
# reader instead** -- if the refusal comes back, the file stops emitting and this mark
# falls.
#
# **57 -> 58, und die dritte Fragmentdatei desselben Tages.**
# `messung/fragmente/F05.gab` emittiert, seit drei Namen umbenannt sind, die C schon
# vergeben hat (`exit`, `signal`, `recv`) und fuenf gerufene Ruempfe deklariert sind,
# die der eingefrorene Dienstrumpf nie nannte. *Keine dieser Absagen war an `cc` zu
# bemerken* -- die erzeugte Einheit bindet keinen der drei Koepfe ein.
# **58 -> 59 im MERGE, und die Zahl ist GEMESSEN statt addiert.** `master` zog sie um eins
# (der `static`-Initialisierer), die `H = 0`-Spur um vier (F09, F01, F05 und ihre Probe) --
# jede Seite fuer sich gruen, keine Textkollision, weil beide dieselbe Zeile schreiben und
# git zweimal dieselbe Ziffer sieht. **Der Lauf sagt 59.** *Sechster Fall dieser Klasse in
# drei Tagen, und der einzige Griff, der greift, ist der Lauf im zusammengefuehrten Baum.*
#
# **59 -> 61 am 2026-09-03, und diesmal ist es kein Merge-Fall.** Zwei Bahnen legten je eine
# emittierende Probe unter `messung/` ab: `proben/probe-suchschleife-passfach.gab` (das
# Passfach-Vorlauf der Suchschleife) und `proben/unseen-fat-reader2.gab` (der ungesehene
# Port). Der Waechter nennt das selbst *den guten Fall* -- der Gegenstand ist gewachsen,
# also steigt die Marke, und die Begruendung steht hier an ihr statt in einer Notiz daneben.
# *Stufe 9 blieb dabei 128 von 128, und `clang` nimmt dieselben 128.*
MARKE_EMIT_M=61
# **Und drei Marken kommen dazu, weil die Reichweite der ganze Baum ist** (2026-08-31).
# Gemessen, nicht geschaetzt -- `messung/REICHWEITE-DER-REGEL.md`, Abschnitt 3.
MARKE_EMIT_N=2      # `messungen/` -- narrow.gab, tabelle.gab; die Vergleichsmessung gegen C
MARKE_EMIT_P=1      # `programmlogik/` -- beispiel/lager.gab; `betrieb.gab` sagt ab
# **0 -> 1 on 2026-09-01, and this one is not bookkeeping.** `halde.gab` -- the only file
# in the tree at the target scale -- did NOT emit until tonight: it fell at an `L104` false
# alarm, `g is consumed a second time`, because `m2` ran a `narrow … else` arm as
# straight-line code and merged its state into the join. The arm was healed (`f1831fa`), and
# the file has emitted since. *A mark that stood at zero because a false refusal held the
# only witness.*
MARKE_EMIT_X=1      # `halde.gab` -- emittiert seit `f1831fa`, s. den Kasten darueber
#
# **Und `arbeitsprotokoll/` ist ausgenommen, weil es nicht im Baum ist** (2026-08-31). Der
# erste Lauf dieser erweiterten Reichweite meldete `NEUE WURZEL EMITTIERT: 2` -- beide unter
# `arbeitsprotokoll/messungen/`, und `.gitignore`:11 haelt das ganze Verzeichnis heraus.
# *Ein Waechter ueber "dem Baum" meint den VERSIONIERTEN Baum;* Arbeitsdateien, die niemand
# ausliefert, in eine Auslieferungsregel zu ziehen, misst die Platte und nicht das Erzeugnis.
# Dieselbe Familie wie `.claude/worktrees/` in der Grundgesamtheit der Grammatiktafel.
#
# **`beispiele/gift/` bekommt eine DECKE und keine Ratsche, und die Richtung ist der Ertrag.**
# In `beispiele/` heisst eine Datei weniger: der Erzeuger hat eine Form verloren -- schlecht.
# In `gift/` heisst eine Datei weniger: **der Pruefer faengt jetzt eine Probe mehr, bevor sie
# ueberhaupt emittiert** -- gut, und genau das Ziel des Korpus. Am selben Tag ist es passiert:
# `gift/45-pub-wo-es-nicht-steht.gab` fiel durch den neuen Pass `P041` aus der Emission.
#
# *Eine Ratsche misst nicht eine Zahl, sondern eine Richtung* -- und die Richtung haengt daran,
# wofuer die Population da ist. Wer hier dieselbe Ratsche wie nebenan haengt, meldet die gute
# Arbeit als Bruch. Beide Seiten sind trotzdem ein Befund: ein Anstieg heisst, dass eine Probe
# durchrutscht, ein Abstieg, dass die Marke nachzuziehen ist.
# **2 -> 8 am 2026-09-02, und alle sechs neuen sind `-- erwartet: cc`.** Der Erzeugerfuzzer
# (`instrumente/fuzze-erzeuger.py`) hat ueber 5889 Faellen 273 gefunden, die zu C absenken, das
# unter `cc -std=c11 -O0 -Wall -Wextra -Werror -c` nicht uebersetzt; zurueckgefuehrt sind sie
# auf sechs Erzeugerfehler, und jeder hat seither eine Probe: `641` (ein `walk` steigt durch
# ein `reserved`-Feld ab), `642` (`forever` als ganzer Rumpf einer antwortenden Funktion),
# `643` (ein Literal ohne `u`-Suffix), `644` (ein Massstab breiter als jeder C-Typ), `645`
# (eine Feldlaenge jenseits von C's groesstem Objekt), `646` (ein `section`-Name, den nichts
# maskiert).
#
# > **Die Decke steigt hier, weil die MESSFLAECHE gewachsen ist, und nicht, weil eine Probe
# > durchrutscht.** Das ist genau der Fall, fuer den die Meldung *„Nachsehen mit: head -1 auf
# > die neue Datei -- steht dort `-- erwartet: cc`, gehoert die Marke mit Grund nachgezogen"*
# > geschrieben wurde. Bei allen sechs steht es dort.
#
# **8 -> 2 on 2026-09-03, and the direction is the good one all six times.** All six emitter
# defects of 2026-09-02 were repaired in one run. `641`, `642`, `644`, `645` and `646` no
# longer reach the emitter's output -- each falls AT the emitter with `C001` and is headed
# `-- erwartet: C001`. `643` went the other way: its program was always correct Gabbro and
# the LOWERING was wrong, so it emits, compiles, and left the poison corpus altogether for
# `messung/proben/probe-literal-past-the-signed-end.gab`.
#
# That is the cap moving the way its own message says it should -- *a probe caught before it
# emits* -- and it is now back where it stood before 2026-09-02.
MARKE_EMIT_G=2      # `gift/286` (uebersetzt) und `gift/414` (`-- erwartet: cc`)
#
# **Und die umgekehrten Proben werden GEZAEHLT, weil eine Probe ohne Gegenstand nichts misst.**
# Faellt diese Zahl auf 0, laeuft der `-- erwartet: cc`-Zweig oben ueber keine einzige Datei
# mehr -- und ein Zweig, den nichts betritt, ist gruen, ohne etwas zu sagen. *Genau der Fall,
# an dem die Sprechprobe der Grammatiktafel am 2026-08-31 gestorben ist: die Arbeit, die den
# Baum verbessert, hat den Waechter abgeschaltet.* Hier faellt es auf.
# **1 -> 4 on 2026-09-01, and the three that came in had been RED across two lanes.** The
# `B001` poison probes went into the tree without the marker, so this stage read them as
# `UEBERSETZT NICHT` -- three files whose OWN HEADERS predict, word for word, the `cc`
# diagnostic they then got:
#
#     -parameter   "`main` takes only zero or two arguments"      [-Werror=main]
#     -privat      "`main` is normally a non-static function"     [-Werror=main]
#     -zwei        "static declaration of `main` follows non-static declaration"
#
# *What the marker buys is not a green line, it is a measurement.* The commit that built
# `B001` states in PROSE who refused each entry shape before the rule existed -- `cc` for
# the private one, `cc` for the parametrised one, nobody for a `pub` beside a private. From
# here on this stage CHECKS that table every run instead of quoting it, and the reverse
# direction bites too: if any of the three ever compiles, `B001` has stopped covering a
# shape a foreign tool used to catch. **A probe that cannot bite reads like one that never
# could.**
#
# **4 -> 10 am 2026-09-02.** Dieselben sechs Proben wie an `MARKE_EMIT_G` darueber, und die
# Zahl steht hier ein zweites Mal, weil sie zwei verschiedene Dinge misst: dort, wie viele
# Giftproben ueberhaupt bis zum Erzeuger kommen, hier, wie viele davon dem `cc`-Zweig einen
# Gegenstand geben. *Ein Zweig, den nichts betritt, ist gruen, ohne etwas zu sagen* -- mit
# zehn Dateien betritt ihn jetzt das Zweieinhalbfache.
# **10 -> 4 on 2026-09-03.** All six emitter defects of 2026-09-02 were repaired: `641`,
# `642`, `644`, `645` and `646` now fall at `C001` and are re-headed `-- erwartet: C001`;
# `643` lowers correctly and moved out of the poison corpus. None of the six gives the
# `-- erwartet: cc` branch an object any more. **The number falling IS the evidence the
# repairs landed** -- and four files still enter the branch, so it keeps saying something:
# `gift/414` and the three `B001` entry probes.
MARKE_UMGEKEHRT=4
ratsche() {
    local ist="$1" marke="$2" wo="$3"
    if [ "$ist" -lt "$marke" ]; then
        echo "  RATSCHE GEBROCHEN: $ist emittierende Dateien in $wo, gebucht sind $marke."
        echo "                     Eine Datei hat die Emission VERLASSEN -- das ist kein gruener"
        echo "                     Lauf, sondern ein kleinerer Nenner. Nachsehen mit:"
        echo "                     for f in $wo*.gab; do ./target/debug/gabbro emit \$f >/dev/null || echo \$f; done"
        schlecht=1
    elif [ "$ist" -gt "$marke" ]; then
        echo "  FUND: $ist statt $marke emittierende Dateien in $wo -- die Marke gehoert"
        echo "        nachgezogen (der gute Fall, und trotzdem ein Befund)."
        schlecht=1
    fi
}
decke() {
    local ist="$1" marke="$2" wo="$3"
    if [ "$ist" -gt "$marke" ]; then
        echo "  DECKE DURCHBROCHEN: $ist emittierende Giftproben in $wo, gebucht sind $marke."
        echo "                      Eine Probe RUTSCHT DURCH: sie sollte am Pruefer fallen und"
        echo "                      kommt bis zum Erzeuger. Das ist kein gruener Lauf."
        echo "                      Nachsehen mit: head -1 auf die neue Datei -- steht dort"
        echo "                      \`-- erwartet: cc\`, gehoert die Marke mit Grund nachgezogen."
        schlecht=1
    elif [ "$ist" -lt "$marke" ]; then
        echo "  FUND: $ist statt $marke emittierende Giftproben in $wo -- der Pruefer faengt"
        echo "        jetzt eine mehr, bevor sie emittiert. Die Marke gehoert nachgezogen"
        echo "        (der gute Fall, und trotzdem ein Befund)."
        schlecht=1
    fi
}
ratsche "$n_emit_b" "$MARKE_EMIT"   "beispiele/"
ratsche "$n_emit_m" "$MARKE_EMIT_M" "messung/*/"
ratsche "$n_emit_n" "$MARKE_EMIT_N" "messungen/"
ratsche "$n_emit_p" "$MARKE_EMIT_P" "programmlogik/"
decke   "$n_emit_g" "$MARKE_EMIT_G" "beispiele/gift/"
if [ "$n_emit_x" -ne "$MARKE_EMIT_X" ]; then
    echo "  NEUE WURZEL EMITTIERT: $n_emit_x Dateien ausserhalb der fuenf gebuchten Wurzeln"
    echo "                         emittieren, gebucht sind $MARKE_EMIT_X. Das ist die Stelle,"
    echo "                         an der die Reichweite frueher lautlos zurueckblieb:$rest_x"
    schlecht=1
fi
if [ "$n_umg" -ne "$MARKE_UMGEKEHRT" ]; then
    echo "  UMGEKEHRTE PROBEN: $n_umg statt $MARKE_UMGEKEHRT."
    if [ "$n_umg" -lt "$MARKE_UMGEKEHRT" ]; then
        echo "                     Faellt sie auf 0, misst der \`-- erwartet: cc\`-Zweig NICHTS"
        echo "                     mehr -- er ist dann gruen, ohne etwas gesagt zu haben."
    fi
    echo "                     Die Marke gehoert mit Grund nachgezogen (MARKE_UMGEKEHRT)."
    schlecht=1
fi
if [ "$schlecht" != "0" ]; then
    echo "== EMISSION: die REGEL haelt nicht -- eine neue Form ist am C-Uebersetzer vorbei =="
    exit 1
fi

# **Die Sprechprobe der Regel.** Ein Waechter, der nur gruen kann, misst nichts: hier faellt
# absichtlich erzeugtes C durch, damit „$n_ok von $n_nenner" eine Aussage ist und kein Ritual.
#
# **Und die UMKEHRUNG braucht keine eigene Sprechprobe, sondern zwei Marken -- gepruefte
# Ueberlegung, kein Weglassen** (2026-08-31). Zwei Wege koennte der `-- erwartet: cc`-Zweig
# falsch gehen, und beide sind schon zugehalten:
#
#   * **Die Marke trifft nie** (ein Leerzeichen zu viel, ein CRLF): dann faellt `gift/413` in
#     den gewoehnlichen Zweig und wird als `UEBERSETZT NICHT` gemeldet -- laut und rot.
#   * **Die Marke trifft zu viel**: dann steigt `n_umg` ueber `MARKE_UMGEKEHRT` und der Lauf
#     sagt es. Faellt sie auf 0, sagt er auch das -- *ein Zweig, den nichts betritt, ist
#     gruen, ohne etwas gesagt zu haben.*
#
# Damit sind BEIDE Zweige jeden Lauf betreten: `n_umg >= 1` erzwingt `MARKE_UMGEKEHRT`,
# `n_ok >= 1` die vier Ratschen daneben. *Das ist die Aussage, die eine Sprechprobe geben
# soll -- hier gibt sie der Korpus selbst, und sie kostet keinen zweiten Durchgang.*
printf 'int fehlt(void) { return nicht_da(); }\n' > "$ARB/sprech9.c"
if cc -std=c11 -Wall -Wextra -Werror -c -o /dev/null "$ARB/sprech9.c" 2>/dev/null; then
    echo "== EMISSION: Sprechprobe 9 haelt nicht -- cc -Werror laesst alles durch =="
    exit 1
fi
echo "  Sprechprobe:  ok (ein fehlender Prototyp faellt an cc -Werror)"

# **The speech test of the SECOND family, and it has TWO halves** (2026-09-02).
#
# The piece below is the shape for whose sake this question exists at all: the `update` body
# of an `exchange` that answers on one path and pushes a never-written value into a
# compare-exchange on the other (`0e328c7`). Both halves must hold, and the FIRST one is what
# separates this stage from a decoration:
#
#   (a) `cc -Wall -Wextra -Werror` ACCEPTS it. If it falls here, the second family only sees
#       what the first would long since have reported -- the extension would be a second
#       register over one thing (W7) and not the question it stands for.
#   (b) `clang` with the same flag word REJECTS it. If that stops holding, the new branch
#       measures nothing and the $n_clang_ok above is a number without a statement (R11).
if [ "$HAT_CLANG" = "1" ]; then
    cat > "$ARB/sprech9b.c" <<'PROBE_CAS'
#include <stdatomic.h>
#include <stdint.h>
#define GRENZE 100u
static _Atomic uint32_t ZAEHLER;
uint32_t schritt(void);
uint32_t schritt(void) {
    uint32_t _cx1 = atomic_load_explicit(&ZAEHLER, memory_order_relaxed);
    for (;;) {
        uint32_t _cn1;
        {
            const uint32_t v = _cx1;
            if (v < GRENZE) { _cn1 = v + 1; goto _cn1_fertig; }
            _cn1_fertig: ;
        }
        if (atomic_compare_exchange_weak_explicit(&ZAEHLER, &_cx1, _cn1,
                memory_order_seq_cst, memory_order_seq_cst)) break;
    }
    return _cx1;
}
PROBE_CAS
    if ! cc -std=c11 -Wall -Wextra -Werror -c -o /dev/null "$ARB/sprech9b.c" 2>/dev/null; then
        echo "== EMISSION: Sprechprobe 9b, Haelfte (a) haelt nicht -- cc faengt die CAS-Gestalt =="
        echo "   Dann sagt die zweite Familie nichts, was die erste nicht schon saegt, und der"
        echo "   Grund dieser Erweiterung steht nicht mehr. Der Kasten an Stufe 9 gehoert"
        echo "   nachgemessen -- ein Waechter, dessen Anlass entfallen ist, ist ein Befund."
        exit 1
    fi
    if clang -std=c11 -Wall -Wextra -Werror -c -o /dev/null "$ARB/sprech9b.c" 2>/dev/null; then
        echo "== EMISSION: Sprechprobe 9b, Haelfte (b) haelt nicht -- clang laesst die CAS-Gestalt durch =="
        echo "   Der neue Zweig kann dann nicht mehr beissen, und \`$n_clang_ok von $n_ok\` ist"
        echo "   eine Zahl ohne Aussage. Diese Fassung von clang taugt fuer diese Frage nicht."
        exit 1
    fi
    echo "  Sprechprobe 9b: ok (cc nimmt die CAS-Gestalt an, clang lehnt sie ab)"
fi

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
LETZTE_STUFE="Stufe 10 (die Bibliothekskette)"
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
grep -q ', 0 errors, 0 hints' "$BIB/pruef" || { echo "  2. pruefe: nicht sauber"; head -20 "$BIB/pruef"; exit 1; }
echo "  2. pruefe:     ok (0 errors, 0 hints ueber die Grenze)"

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
cmp -s "$BIB/mischen.c" "$BIB/mischen-gift.c" && { echo "  7. Sprechprobe A: das Gift greift nicht"; exit 2; }
cc -std=c11 -O0 -w -c -o "$BIB/mischen-gift.o" "$BIB/mischen-gift.c" || exit 1
cc -std=c11 -O0 -w -o "$BIB/probe-gift" "$BIB/treiber.c" "$BIB/fach.o" "$BIB/mischen-gift.o" "$BIB/nutzer.o" || exit 1
if [ "$("$BIB/probe-gift")" = "$BIBERWARTET" ]; then
    echo '  7. Sprechprobe A: GESCHEITERT -- verfaelschtes verdopple rechnet dasselbe'; exit 2
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
    echo "  8. Sprechprobe B: GESCHEITERT -- zwei gleiche oeffentliche Namen gehen durch"; exit 2
fi
grep -q 'N039' "$BIB/koll" || { echo "  8. Sprechprobe B: es faellt, aber nicht an N039:"; head -5 "$BIB/koll"; exit 2; }
# und die Gegenprobe der Gegenprobe: EINZELN erzeugt kollidiert es wirklich beim Binder.
G emit "$BIB/eins.gab" > "$BIB/e1.c" && G emit "$BIB/zwei.gab" > "$BIB/e2.c" || exit 1
cc -std=c11 -w -c -o "$BIB/e1.o" "$BIB/e1.c" && cc -std=c11 -w -c -o "$BIB/e2.o" "$BIB/e2.c" || exit 1
printf 'int main(void){return 0;}\n' > "$BIB/leer.c"
if cc -w -o "$BIB/zusammen" "$BIB/leer.c" "$BIB/e1.o" "$BIB/e2.o" 2> "$BIB/ld2"; then
    echo '  8. Sprechprobe B: GESCHEITERT -- der Binder nimmt zwei lesen an, N039 zeigt ins Leere'; exit 2
fi
grep -q 'multiple definition' "$BIB/ld2" || { echo "  8. Sprechprobe B: der Binder faellt aus anderem Grund:"; head -3 "$BIB/ld2"; exit 2; }
echo "  8. Sprechprobe B: ok (N039 sagt ab, und der Binder haette es sonst getan)"

GANZ_DURCH=1
echo "== EMISSION: ALL PASS -- $N_DURCHGESTOCHEN durchgestochen, $n_ok von $n_nenner uebersetzen, $n_umg umgekehrte Probe(n) =="
echo "  Und was das NICHT heisst: DURCHGESTOCHEN sind $N_DURCHGESTOCHEN -- erzeugt, uebersetzt,"
echo "  AUSGEFUEHRT und mit einer Handschrift verglichen. Die Regel darueber ist"
echo "  schwaecher: sie fragt nur, ob der C-Uebersetzer die Ausgabe annimmt. Ein"
echo "  Programm, das uebersetzt und falsch rechnet, faellt ihr nicht auf."

# **Und die ASan-Zahl steht daneben, weil sie ORTSGEBUNDEN ist** (2026-09-02). Sie ist die
# einzige Zeile dieses Waechters, deren Wert von der Maschine abhaengt und nicht vom Baum:
# auf `ki-pc-fisch-101` laeuft ASan, auf dem Arbeitsrechner nicht. *Wer sie nicht ausdruckt,
# liest denselben gruenen Waechter zweimal und weiss nicht, dass er zwei Dinge gemessen hat.*
n_as_ok=0;  [ -f "$ARB/asan-gefahren" ]   && n_as_ok=$(grep -c '' "$ARB/asan-gefahren")
n_as_nix=0; [ -f "$ARB/asan-ungefahren" ] && n_as_nix=$(grep -c '' "$ARB/asan-ungefahren")
if [ "$ASAN_LAEUFT" = "1" ]; then
    echo "  ASan (Stufe 6b): $n_as_ok Einheit(en) unter -fsanitize=address,undefined gefahren,"
    echo "  kein Fund. Diese Zahl ist ORTSGEBUNDEN: auf einem Rechner, dessen Kern ASans"
    echo "  Schattenspeicher nicht zulaesst, steht hier 0 und der Waechter bleibt gruen --"
    echo "  dann ist es eine NICHT GEFAHRENE Probe und keine bestandene."
else
    echo "  ASan (Stufe 6b): NICHT GEFAHREN auf dieser Maschine ($n_as_nix Einheit(en))."
    echo "  Das ist keine bestandene Probe. Der Ort, an dem sie laeuft, ist ki-pc-fisch-101."
fi
