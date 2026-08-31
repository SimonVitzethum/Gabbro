# FORM × ZUSTÄNDIGKEIT aus der GRAMMATIK — und `UNGEDECKT` fiel von 13 auf 4

*Bahn V, Schritte V-2 und V-5 des `dokumente/PLAN-VOLLSTAENDIGKEIT.md`. Gemessen und gebaut
am 2026-08-31. Werkzeug: `./instrumente/pruefe-grammatiktafel.py`.*

> **Der Unterschied zu `gabbro blindstellen` ist die Grundgesamtheit, und darin liegt alles.**
> Jenes rechnet FORM × POSITION über einem **Korpus** und sagt von sich selbst: *der Korpus
> ist von der Sprache nach außen geschrieben.* **Falle 80.** Hier ist die Grundgesamtheit die
> **Grammatik**: `dokumente/SYNTAX.md` führt 154 Regeln und **219 Terminale**, und das ist
> die Menge, die „beliebig" meint.

---

## 1. Die vier Zustände, und wie jeder gemessen wird

```
gesenkt       ein Programm mit diesem Wort emittiert C, das `cc -Werror` ANNIMMT
abgesagt      der Erzeuger sagt es benannt ab, und ein PRUEFERFEHLER nennt es auch
vom Pruefer   nur ein Prueferfehler nennt es; der Erzeuger sieht die Form nie
UNGEDECKT     keines davon
```

**`gesenkt` sind ZWEI LÄUFE und keine Lesung.** Ein Wort gilt genau dann als abgesenkt, wenn
es in einer `.gab`-Datei steht, die **vollständig emittiert** (null Prüferfehler *und* null
`C001`) **und deren Erzeugnis `cc -std=c11 -Wall -Wextra -Werror` bei `-O0` und `-O2`
annimmt**. Dann ist alles, was in dieser Datei steht, durch den Erzeuger gegangen — das Wort
eingeschlossen — *und was dabei herauskam, ist C.*

> **Die zweite Hälfte kam am 2026-08-31 dazu, und §7 sagt, was sie gekostet hat: nichts.**
> Bis dahin hieß `gesenkt` nur „die Datei emittiert"; ob das Erzeugnis überhaupt C ist,
> fragte niemand — §6.1 stand als Selbstauskunft da, und `F06` war der Beleg dafür. **Die
> `UNGEDECKT`-Marke bleibt bei 4 und steigt nicht**; die Grundgesamtheit ist nicht gewachsen,
> die Messung ist schärfer geworden. *Eine Marke, die bei einer Verschärfung stehen bleibt,
> ist eine Aussage über den Baum und nicht über die Ratsche.*

**Und das trägt, weil der Wortschatz geschlossen ist.** `kw.rs` führt 213 der 222 Wörter als
`res` — reserviert, nirgends ein Bezeichner. *Ein Vorkommen IST damit ein Schlüsselwort.* Die
sechs verbleibenden `ctx`-Wörter (`child`, `observed`, `occupied`, `parent`, `sibling`,
`tree`) können ein Bezeichner sein; sie stehen neben dem Urteil, statt still mitzulaufen.

### Drei Register, gelesen statt kopiert (W7)

| was | woher |
|---|---|
| die 219 Terminale | `pruefe-wortschatz.py` — es hält sie schon gegen die EBNF |
| die 130 Absageformen | `zaehle-absagen.py` — 139 Stellen in `emit.rs` |
| die Prüferfehler | `Absage::fehler(…)` in jeder `gabbro-check/src/*.rs` **außer** `emit.rs` |

*Ein zweites Register über derselben Sache läuft weg* — dieser Ordner hat das oft genug
bezahlt, dass es keine dritte Kopie der Terminalliste gibt. **`Absage::hinweis` zählt
ausdrücklich nicht:** ein Hinweis weist nichts ab. `beispiele/gift/166` trägt `S007` als
Hinweis, prüft mit null Fehlern und fällt erst am `C001` — *ein Wächter, der Hinweise als
Absagen zählt, liest seine eigene Nachsicht als Deckung.*

---

## 2. Der erste Lauf: 13 UNGEDECKT — und neun davon waren nur ungeschrieben

```
gesenkt       205
abgesagt        0
vom Pruefer     1
UNGEDECKT      13
```

| Wort | wo es in der Grammatik steht | Befund |
|---|---|---|
| `i8` `i16` `i32` `i64` | `intty` (`SYNTAX.md`:356) | **kein Programm des Baumes schrieb je einen vorzeichenbehafteten Typ** |
| `f32` | `floatty` (:357) | dito — `f64` steht in zwei Dateien, `f32` in keiner |
| `and` | `accdecl … merge` (:283) | die fünfte Faltung; `max`, `min`, `add` sind geschrieben, `or` und `and` nicht |
| `port` | `space` (:463) | ein Adressraum ohne einen einzigen Zeiger |
| `rc` | `regklasse` (:1288) | *read to clear* — nie an einem Register geschrieben |
| `seq` | Ordnung am `atomic` (:1375) | `acquire`, `release`, `relaxed` sind geschrieben, `seq` nicht |
| `chain` `queue` `state` `threads` | Domänen und ein Item | **der Erzeuger sagt sie benannt ab, und der Prüfer nimmt sie an** |

> **Neun der dreizehn waren keine Lücke im Erzeuger, sondern eine im KORPUS** — und genau das
> ist der Satz, den `blindstellen` über sich selbst schreibt: *was 0 Fundstellen hat, ist
> nicht geprüft, sondern unerreichbar.* Eine Absenkung, die nie gelaufen ist, ist eine
> Vermutung mit einem Namen.

---

## 3. Die Antwort darauf: zwei Programme, aus der Grammatik geschrieben

`messung/grammatik/` — **von der Grammatik nach innen, nicht von einer Absicht nach außen.**

| Datei | schließt |
|---|---|
| `zahlbreiten.gab` | `i8`, `i16`, `i32`, `i64`, `f32`, `merge and` |
| `geraeteworte.gab` | `port`, `rc`, `seq` |

Beide prüfen mit **0 Fehlern**, emittieren und übersetzen unter `cc -Werror` (`-O0` und
`-O2`, Stufe 9). Damit fällt die Tafel:

```
gesenkt       214        UNGEDECKT   4
abgesagt        0        vom Pruefer 1   (`masked`)
```

**Und die neun Absenkungen, die dabei zum ersten Mal gelaufen sind, haben ZWEI Befunde
abgeworfen.** Das ist der eigentliche Ertrag; die Zahl ist nur die Buchhaltung.

### Befund 1 — ein `f32`-Ausdruck rechnet in `double`

`gleitkommatext` (`emit.rs`) schreibt `f64::from_bits(bits)` ohne Suffix hin. In C ist ein
Literal ohne `f` ein **`double`**:

```c
static float zehntel(float x) {
    return x * 0.1;          /* float * double -> double, und erst die Rueckgabe rundet */
}
```

Gemessen in reinem C über 200 000 Werten:

```
(float)(v * 0.1)  !=  v * 0.1f     in 39 974 von 200 000 Faellen
```

**Der Prüfer nimmt das Programm mit 100 % Typdeckung an, und das erzeugte C rechnet etwas
anderes, als dasteht.** Die Probe steht als `messung/proben/probe-f32-literal.gab` im Baum;
der Posten ist in `TODO.md` gebucht. *Er wird hier nicht nebenbei entschieden* — welche
Breite ein Literal in einem `f32`-Ausdruck hat, ist eine Aussage über das Zahlmodell, und
`dokumente/MEMO-GLEITKOMMA.md` führt die Doppelrundung bereits als Landmine.

### Befund 2 — der Adressraum `port` verschwindet in der Absenkung

`ptr<port, r> Stand` wird `const Stand *restrict p`, und `p.bereit` wird ein gewöhnlicher
Ladebefehl. **`ctyp` liest `z.raum` überhaupt nicht** — für einen Zeiger ist der Raum eine
Prüfertatsache und im C nicht sichtbar. Bei `mmio` fängt das der Geräteweg auf (`volatile` an
`basis + Versatz`); bei `port` fängt es nichts auf.

> *Ob das ein Fehler ist, hängt daran, was `port` verspricht* — auf x86_64 ist Portraum kein
> Speicher, sondern `in`/`out`. Die Frage steht in `TODO.md`, mit der Messung daneben und
> ohne Antwort: **eine Entscheidung über einen Adressraum gehört nicht in einen Nebensatz.**

---

## 4. Was offen bleibt: vier Zellen, und alle vier dieselbe Bauart

```
! GRAMMATIKTAFEL ROT: 4 von 219 Terminalen sind UNGEDECKT.
    chain            der Erzeuger sagt ab, der Pruefer nicht
    queue            der Erzeuger sagt ab, der Pruefer nicht
    state            der Erzeuger sagt ab, der Pruefer nicht
    threads          der Erzeuger sagt ab, der Pruefer nicht
```

**Der Prüfer nimmt jede der vier Formen an, und erst der Erzeuger sagt ab.** Das ist genau
der Zustand, den der Plan verbietet — und der Ausgang steht dort auch: *im PRÜFER absagen,
dann wandert die Zelle nach `vom Pruefer`.* **Eine Sprache, die eine Form nicht hat, ist
vollständig, solange sie das sagt.**

### Und das ist NACHGEMESSEN, nicht aus dem Schweigen der Texte geschlossen

*Diese Tafel liest Prüferfehlertexte. Ein Schluss aus einem Text ist keine Messung* (W16) —
also wurde gefragt: `messung/proben/probe-vier-zellen.gab`.

```
mit Kostenzusage    K003 faellt -- „die Domaene `queue` der Traversierung hat keine
                    Schranke aus der Deklaration (fehlt der Tabelle ihr `count`?)"
ohne Kostenzusage   8 Items, 0 Fehler, 0 Hinweise -- und VIER C001
```

**Der Wächter hatte zur Hälfte unrecht und in die sichere Richtung.** Die `K003`-Meldung baut
den Domänennamen mit `format!` aus einer Variablen; `queue` und `chain in` stehen darum in
keinem Literal, und die Textlesung sah sie nicht. *Eine Lesung über einem `format!` ist eine
untere Schranke — sie meldet zu viel, nicht zu wenig, und das ist die Richtung, in der ein
Wächter verpflichtet statt freizusprechen* (W10).

**Und das Urteil steht:** in einem `divergent fn` — der keine Kostenzusage trägt, an der
`K003` hängen könnte — prüfen alle vier mit **0 Fehlern** und fallen an vier `C001`.

> **Damit hat die ganze offene Menge EINE Wurzel.** `messung/ABSAGEFORMEN.md` U10–U15 zeigen
> dasselbe Bild: `K003` ist die einzige Regel zwischen den Absagen des Erzeugers und dem
> Prüfer, und sie hängt an einer Zusage, die nicht jede Funktion macht. *Das ist eine
> Adresse und keine Liste.*
>
> **Die Adresse ist am 2026-08-31 ausgerechnet: [`K003-TOR.md`](K003-TOR.md).** Drei Formen
> einer torlosen Regel, ihr Preis über 418 Dateien gemessen — und der Befund, dass `state`
> von KEINER erreicht wird: der Kostenpass läuft nur über Funktionsrümpfe
> (`kosten.rs`:259–264), und ein `state`-Item ist keiner.

*Das ist eine Entscheidung über die SPRACHE und keine über den Erzeuger* — vier Formen fallen
damit aus Gabbro heraus. Sie gehört dem Ordner und der Bahn, die am Prüfer arbeitet, und
steht darum hier als Arbeitsmenge und nicht als erledigt.

---

## 5. Die Sprechprobe — in beide Richtungen, und beide waren gefordert

```
ok   entfernte Absenkung `acquire` faellt als UNGEDECKT
ok   und im sauberen Lauf ist `acquire` gesenkt
ok   erfundene Grammatikregel `zztafelprobe` faellt als UNGEDECKT
ok   und sie steht nicht schon in der echten Grammatik
```

**Seit dem 2026-08-31 sind es DREI Richtungen und elf Proben** — die dritte ist das
Übersetzungstor, und sie ist die Richtung, an der `F06` siebzehn Tage vorbeilief:

```
ok   kuenstliches `F06`-C faellt bei `cc -Werror` (beide Stufen)
ok   und die Meldung nennt den erzwungenen Bereich ('limited range')
ok   gueltiges C kommt durch -- das Tor sagt nicht zu allem nein
ok   `beispiele/03-format.gab` mit `F06`-C faellt aus der Deckung
ok   und aus dem richtigen Grund
ok   und das allein von ihr getragene `sizeof` faellt als UNGEDECKT
ok   im sauberen Lauf ist `sizeof` gesenkt
```

Das Gift ist **genau die Form, an der `F06` hing** — ein `uint8_t`-Index gegen eine Schranke,
die sein Bereich nicht überschreiten kann, also *„comparison is always true due to limited
range of data type"* (`-Wtype-limits`, in `-Wextra`). Und es geht **durch dasselbe Tor wie
der echte Lauf**: `uebersetzende(verfaelsche=(datei, GIFT_C))` schiebt einer echten Datei
das kaputte C unter, statt zu behaupten, was das Tor getan hätte. *Eine Probe, die das
Ergebnis setzt statt es zu messen, prüft ihre eigene Annahme.*

Die drei Zeilen davor sind so wichtig wie die drei danach: **ein Tor, das zu allem nein sagt,
misst auch nichts.** Ein Tippfehler im `cc`-Aufruf hätte 214 Zellen auf einmal rot gemacht,
und das hätte wie ein Befund ausgesehen. `LC_ALL=C` steht daneben, weil die Probe den
Meldungstext liest — *ein Wächter, dessen Urteil an der Spracheinstellung hängt, misst die
Umgebung.*

Die zweite Richtung läuft über eine **Kopie von `SYNTAX.md`** mit einer eingeschobenen Regel
— also durch dieselbe Extraktion, die auch die echten 219 liefert, und nicht durch eine
zweite. Die erste unterdrückt die Korpusbelege für ein Wort, das heute allein durch die
Absenkung gedeckt ist. *Ein Werkzeug, das über die Sprache urteilt und selbst ungeprüft ist,
ist die teuerste Sorte Wächter.*

**Und der Lauf bricht ab, bevor er urteilt, wenn die Probe fällt** — Rücklaufwert 2, nicht 1:
ein Wächter, der nichts gemessen hat, ist kein Befund.

---

## 6. Was diese Tafel NICHT sagt

1. ~~**Eine besetzte Zelle heißt, dass es eine Absenkung GIBT — nicht, dass sie richtig
   ist.**~~ **Diese Selbstauskunft ist seit dem 2026-08-31 zur Hälfte eingelöst** (§7): eine
   besetzte Zelle heißt jetzt, dass eine Absenkung LÄUFT *und ihr Erzeugnis C IST*. Was sie
   weiter nicht heißt: dass es das **richtige** C ist. `cc -Werror` prüft die Sprache, nicht
   die Bedeutung — *ein `f32`-Ausdruck, der in `double` rechnet, übersetzt tadellos* (§3,
   Befund 1). Die Gegenprobe über *Dateien* bleibt **Stufe 9** von `pruefe-emission.sh`; die
   Tafel stellt die Frage seit heute selbst, weil sie über *Wörter* urteilt und ihre
   Grundgesamtheit vier Dateien größer ist als die von Stufe 9.
2. **Ein Terminal ist nicht dasselbe wie eine Form.** `SYNTAX.md` führt 154 Regeln; diese
   Tafel steht über den 219 **Wörtern**. Eine Regel, die aus lauter gedeckten Wörtern eine
   ungedeckte Kombination baut, fällt hier nicht auf — *das ist genau die Klasse, für die
   `gabbro blindstellen` über dem Korpus gebaut wurde*, und die zwei Werkzeuge decken
   einander nicht ab, sondern ergänzen sich.
3. **Für die sechs `ctx`-Wörter ist `gesenkt` eine OBERE Schranke.** Ein Vorkommen kann ein
   Bezeichner sein. Sie werden bei jedem Lauf genannt.

---

## 7. Die Verschärfung, erst gemessen: **80 von 80 übersetzen — und `UNGEDECKT` bleibt bei 4**

*Gemessen am 2026-08-31, `ki-pc-fisch-101` (`gabbro-g`), vor jeder Änderung am Werkzeug.*

§6.1 sagt, was diese Tafel nicht weiß: eine besetzte Zelle heißt, dass es eine Absenkung
**gibt**. Der Auftrag war, `gesenkt` schärfer zu fassen — *das Wort steht in einer Datei, die
emittiert UND deren C `cc -Werror` annimmt*, bei `-O0` und `-O2`. Die Frage davor lautet:
**wie viele Wörter kostet das?**

```
418 `.gab` im Baum                    80 emittieren vollstaendig (0 Prueferfehler, 0 C001)
cc -std=c11 -Wall -Wextra -Werror     -O0: 80 von 80      -O2: 80 von 80
```

**Null.** Kein Wort verliert seine Deckung, `UNGEDECKT` bleibt bei 4, `gesenkt` bei 214.
*Die Tafel sagte nicht mehr, als sie wusste — sie wusste es nur nicht.*

> **Und die Zahl ist an ZWEI Übersetzern gemessen**, weil ein Wächter, dessen Urteil vom
> Rechner abhängt, keines ist: `gcc 13.3.0` (Ubuntu 24.04, `ki-pc-fisch-101`) und
> `gcc 16.2.1` (lokal, Arch) — **beide 80 von 80, beide Stufen.** Die 80 Erzeugnisse wurden
> auf dem Server erzeugt und lokal ein zweites Mal übersetzt; die Diagnostik dreier
> Hauptversionen Abstand fand nichts.

### Der Ertrag ist nicht die Null — es ist die REICHWEITE

Stufe 9 von `pruefe-emission.sh` fährt `beispiele/*.gab` und `messung/*/*.gab`: **76**. Die
Tafel urteilt über **80**. Die Differenz sind **vier Dateien, deren C noch nie ein Übersetzer
gesehen hat**, und sie standen nicht auf einer Liste, sondern fielen aus dem Abgleich:

```
beispiele/gift/45-pub-wo-es-nicht-steht.gab       `beispiele/*.gab` trifft `gift/` nicht
messungen/narrow.gab                              das Verzeichnis heisst `messungen`, nicht `messung`
messungen/tabelle.gab                             dito
programmlogik/beispiel/lager.gab                  eine dritte Wurzel, die keine Stufe kennt
```

**Alle vier übersetzen.** Aber bis heute hätte keiner es gemerkt, und `beispiele/gift/` ist
genau das Verzeichnis, in dem absichtlich schwierige Programme liegen. *Dieselbe Bauart wie
`F06`: eine Regel, deren Gegenstand die Sprache ist und deren Reichweite ein Verzeichnis,
misst das Verzeichnis.* Die Tafel braucht die Frage darum selbst und nicht als Verweis auf
eine andere Stufe.

### Wo die Verschärfung beißen WÜRDE: 25 Wörter an neun Dateien

Ein Wort, das mehrere Dateien schreiben, überlebt den Ausfall einer. Diese hier nicht —
*jedes hängt an genau einer Datei*, und fällt die aus der Übersetzung, fällt das Wort:

| Datei | trägt allein |
|---|---|
| `beispiele/07-eintritt-und-boot.gab` | `boot` `down` `exists` `leaf` `levels` `mappings` `node` `prim` `walk` |
| `messung/grammatik/zahlbreiten.gab` | `and` `i8` `i16` `i32` `i64` |
| `beispiele/47-ops-wortmenge.gab` | `insert` `relabel` `remove` |
| `messung/grammatik/geraeteworte.gab` | `port` `rc` `seq` |
| `beispiele/03-format.gab` | `sizeof` |
| `beispiele/09-ohne-zeiger.gab` | `allocs` |
| `beispiele/23-akkumulatoren.gab` | `min` |
| `beispiele/26-gleitkomma.gab` | `finite` |
| `beispiele/29-undurchsichtig.gab` | `use` |

125 der 219 Terminale sind **nur** durch Absenkung gedeckt — kein Prüferfehlertext nennt
sie. Für die ist die Übersetzungsprobe die einzige Gegenprobe, die es gibt. **Ein `F06` in
`beispiele/07` kostet neun Zellen auf einmal**; die zwei aus der Grammatik geschriebenen
Dateien tragen zusammen acht. *Das ist keine Empfehlung, sie zu vervielfachen — es ist die
Adresse, an der die Messung dünn ist.*

### Die Verschärfung steht im SCHNELLLAUF, und die Zahl steht daneben

| | vorher | nachher |
|---|---|---|
| `ki-pc-fisch-101` | 0,85 s | **5,0 s** |
| lokal (20 Kerne) | 1,0 s | **5,7 s** |
| davon der Übersetzerdurchgang | — | 1,8 s / 4,0 s (160 `cc`-Aufrufe) |

`abnahme.py` gibt jedem leichten Wächter **600 s** (`FRIST_ABNAHME`) — das sind knapp ein
Prozent. **Die erste Fassung brauchte 9,8 s**, weil die Sprechprobe den ganzen Durchgang ein
zweites Mal fuhr, um EINE vergiftete Datei zu prüfen; sie fährt jetzt nur diese eine
(`uebersetzende(nur=…)`) und zeigt dieselbe Kette.

> **Und der Grund gegen `--voll` ist nicht nur die Zahl.** `pruefe-waechter.SCHWER` sagt
> ausdrücklich, dass keiner seiner vier Einträge wegen der **Zeit** dort steht — es ist der
> *Ort* (Speicher, Rechenlast gehört auf den Server) oder die *Wirkung* (es schreibt in
> Quellen). `cc -c` auf eine Übersetzungseinheit tut weder das eine noch das andere. *Ein
> Wächter hinter `--voll`, den der Schnelllauf braucht, ist ein Wächter, den niemand fährt.*

### Und was hier NICHT entschieden wurde

* **Nichts über die Sprache.** Die vier Zellen `chain`, `queue`, `state`, `threads` stehen
  unverändert; sie sind eine Entscheidung des Ordners (§4) und keine Messfrage.
* **Nichts über `cc` als Maßstab.** Zwei Übersetzer, drei Hauptversionen Abstand, dieselbe
  Antwort — aber das ist eine *Messung* und keine Zusage, dass jeder C-Übersetzer dasselbe
  sagt. Fällt ein dritter anders aus, ist das ein Befund und kein Fehler dieses Wächters.
* **Nichts über die vier Dateien außerhalb von Stufe 9.** Sie übersetzen; ob Stufe 9 ihre
  Reichweite auf `messungen/` und `programmlogik/` ausdehnen soll, gehört zu
  `pruefe-emission.sh` — *und daran arbeitet in dieser Nacht eine andere Bahn.* Die Tafel
  misst sie ab heute selbst; das ersetzt die Frage nicht, es beantwortet sie nur für Wörter.

---

## 8. Was neu `UNGEDECKT` wurde: **nichts** — und was das Tor trotzdem gefunden hat

Schritt 3 des Auftrags lautete: *je Wort, das seine Deckung verliert — liegt es am Erzeuger
oder am Programm?* **Kein Wort verliert seine Deckung.** Das ist eine benannte Absage und
damit ein Ergebnis: das Tor steht, und es hat heute nichts zu tragen.

Also wurde die Gegenfrage gestellt — **wie viel Luft hat das Tor?** Die 80 Erzeugnisse noch
einmal, `-Wall -Wextra -Werror -O2` plus *je einen* schärferen Schalter (`gcc 16.2.1`):

```
-Wpedantic  -Wsign-conversion  -Wshadow  -Wcast-qual  -Wstrict-prototypes
-Wmissing-prototypes  -Wswitch-enum  -Wfloat-equal  -Wundef  -Wwrite-strings
-Wold-style-definition  -Wvla                       0 von 80 fallen

-Wconversion         3 von 80        -Wdouble-promotion   2 von 80
-Wredundant-decls    1 von 80        -Wpadded            42 von 80
```

`-Wpadded` ist Rauschen — Ausrichtungslücken sind kein Fehler, und ein Wächter, der sie
zählt, misst die Zielarchitektur. **Die anderen drei sind es nicht.**

### Fund A — dieselbe Familie wie `F06`, eine Datei weiter

`messung/treiber/virtio-net.gab`:236 schreibt

```
a.slots[i].kopf = i;        -- i : index into Deskring,  count QGROESSE = 8
                            -- AvailRing.slot.kopf : u16,  AVAIL_IDX : u16
```

Das Erzeugnis: `uint32_t i` im Kopf von `armieren`, und `a->slots[i].kopf = i;` **ohne
Umwandlung**. `cc -Wconversion` nennt es zweimal, `-Wall -Wextra` **nicht**.

> **Das ist genau `F06`s Kopie aus `slots of`, nur mit einer anderen Diagnose.** Dort
> erzwang der Bereich einen konstant wahren Vergleich (`-Wtype-limits`, in `-Wextra`); hier
> erzwingt er eine stillschweigende Verengung (`-Wconversion`, **nicht** in `-Wextra`). *Der
> Prüfer kennt die Schranke — drei Bit reichen —, und der Erzeuger senkt 32 Bit ab.*
>
> **Es liegt am ERZEUGER**, nicht am Programm: das Programm schreibt einen Index in ein Feld,
> dessen Breite die Deklaration trägt. **Was daraus folgt, wird hier nicht entschieden** —
> ob ein Indextyp auf die kleinste Breite seines `count` absenken soll oder ob der Erzeuger
> eine Umwandlung hinschreibt, ist eine Aussage über die Absenkung. In `TODO.md` gebucht.

### Fund B — zwei Deklarationen, zwei verschiedene Versprechen

`beispiele/29-undurchsichtig.gab` nennt `pa_aus_zahl` zweimal — als `pub impl fn … effects
{ pure }` (Z. 23) und als `extern fn … effects { pure }` in einem anderen Modul (Z. 46). Das
Erzeugnis trägt beide Prototypen:

```c
uint64_t pa_aus_zahl(uint64_t z) __attribute__((const));   /* aus dem `impl fn`   */
uint64_t pa_aus_zahl(uint64_t z);                          /* aus dem `extern fn` */
```

**Dieselbe `effects { pure }` senkt zweimal verschieden ab.** Gegengeprüft an
`beispiele/40-werte-und-griffe.gab`:96: `extern fn halde() effects { pure }` wird
`void halde(void);`, ohne Attribut. `-Wredundant-decls` nennt es, `-Wall -Wextra` nicht.

*Die Doppelung kommt vom PROGRAMM* — es nennt den Namen zweimal, und das ist der Zweck der
Datei. *Die auseinanderlaufenden Attribute kommen vom ERZEUGER.* Auch das ist gebucht und
nicht entschieden.

### Fund C — der `f32`-Posten hat jetzt einen maschinellen Zeugen

`-Wfloat-conversion` (in `-Wconversion`) nennt Befund 1 aus §3 beim Namen:
*„conversion from `double` to `float` may change value"* an `messung/grammatik/zahlbreiten.gab`
und `messung/proben/probe-f32-literal.gab`. **Der Posten stand schon in `TODO.md`, gefunden
durch Rechnen über 200 000 Werten** — er ist ab jetzt mit einem Schalter zu finden.

### Und warum der Schalter trotzdem NICHT dazukommt

`CC_SCHALTER` bleibt bei `-std=c11 -Wall -Wextra -Werror` — **dieselben Schalter wie Stufe 9
von `pruefe-emission.sh`.** Zwei Wächter, die dasselbe Erzeugnis mit verschiedenen Schaltern
übersetzen, geben zwei Antworten auf eine Frage; und `-Wconversion` dazuzunehmen würde
`UNGEDECKT` durch eine **Entscheidung** heben statt durch eine Messung. *Die Verschärfung
dieser Nacht ist eine Berichtigung; die nächste wäre eine Wahl, und die gehört dem Ordner.*
