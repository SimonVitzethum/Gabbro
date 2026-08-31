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
> `UNGEDECKT`-Marke bleibt bei 4 und steigt nicht**; **die 219 Terminale sind dieselben**, die
> Messung ist nur schärfer geworden. *Eine Marke, die bei einer Verschärfung stehen bleibt,
> ist eine Aussage über den Baum und nicht über die Ratsche.* (Der KORPUS ist in derselben
> Nacht gewachsen — 418 → 426 `.gab`, 80 → 83 vollständig emittierend —, aber das war eine
> andere Bahn und nicht diese Verschärfung; §7 misst beide Stände getrennt.)

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

## 7. Die Verschärfung, erst gemessen: **83 von 83 übersetzen — und `UNGEDECKT` bleibt bei 4**

*Gemessen am 2026-08-31, `ki-pc-fisch-101` (`gabbro-g`), vor jeder Änderung am Werkzeug —
und nach dem Einmischen von `master` (`652d117`) **noch einmal**, weil der Korpus in derselben
Nacht um acht Dateien gewachsen ist. Beide Läufe stehen unten; die zweite Zahl ist die gültige.*

§6.1 sagt, was diese Tafel nicht weiß: eine besetzte Zelle heißt, dass es eine Absenkung
**gibt**. Der Auftrag war, `gesenkt` schärfer zu fassen — *das Wort steht in einer Datei, die
emittiert UND deren C `cc -Werror` annimmt*, bei `-O0` und `-O2`. Die Frage davor lautet:
**wie viele Wörter kostet das?**

```
vor dem Merge     418 `.gab` im Baum    80 emittieren vollstaendig    -O0/-O2: 80 von 80
nach dem Merge    426 `.gab` im Baum    83 emittieren vollstaendig    -O0/-O2: 83 von 83
```

**Null.** Kein Wort verliert seine Deckung, `UNGEDECKT` bleibt bei 4, `gesenkt` bei 214 —
*in beiden Ständen.* Die Tafel sagte nicht mehr, als sie wusste — sie wusste es nur nicht.

> **Zweimal gemessen, weil `master` sich unter der Messung bewegt hat.** Zwischen dem ersten
> Lauf und dem Commit kamen sechs Commits einer anderen Bahn dazu: ein neuer Prüferpass
> (`N041`, `cnamen.rs`), fünf Giftproben und drei `messung/proben/`-Dateien. Damit fiel
> `beispiele/gift/45-pub-wo-es-nicht-steht.gab` aus der Emission (**`P041`**) und vier andere
> kamen hinein. *Ein Zweig, der drei Commits zurückliegt, misst gegen einen Stand, den es
> nicht mehr gibt* (`CLAUDE.md`) — also wurde nach dem Merge neu gemessen und nicht
> hochgerechnet.

> **Und die Zahl ist an ZWEI Übersetzern gemessen**, weil ein Wächter, dessen Urteil vom
> Rechner abhängt, keines ist: `gcc 13.3.0` (Ubuntu 24.04, `ki-pc-fisch-101`) und
> `gcc 16.2.1` (lokal, Arch) — **beide 83 von 83, beide Stufen.** Die 83 Erzeugnisse wurden
> auf dem Server erzeugt und lokal ein zweites Mal übersetzt; die Diagnostik dreier
> Hauptversionen Abstand fand nichts.

### Der Ertrag ist nicht die Null — es ist die REICHWEITE

Stufe 9 von `pruefe-emission.sh` fährt `beispiele/*.gab` und `messung/*/*.gab`: **79**
(`MARKE_EMIT=54` + `MARKE_EMIT_M=25`). Die Tafel urteilt über **83**. Die Differenz sind
**vier Dateien, deren C noch nie ein Übersetzer gesehen hat**, und sie standen nicht auf einer
Liste, sondern fielen aus dem Abgleich:

```
beispiele/gift/286-maintains-ohne-schreiben.gab   `beispiele/*.gab` trifft `gift/` nicht
messungen/narrow.gab                              das Verzeichnis heisst `messungen`, nicht `messung`
messungen/tabelle.gab                             dito
programmlogik/beispiel/lager.gab                  eine dritte Wurzel, die keine Stufe kennt
```

*Vor dem Merge stand an der ersten Stelle `beispiele/gift/45-pub-wo-es-nicht-steht.gab` —
**die Adresse wechselt, die Lücke bleibt.** Genau darum ist sie eine Regel und keine Liste.*

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

> ### Und am Abend desselben Tages sind es **null** — §9
>
> Die 25 wurden eingeteilt (`messung/EINSAME-WOERTER.md`) und dann verteilt: **fünf Programme
> aus der Grammatik**, und die Zahl fällt `25 → 0`. Jedes der 125 Wörter steht jetzt in
> mindestens zwei übersetzenden Dateien. Die Zahl steht seither **im Wächter** und nicht mehr
> nur in diesem Absatz — mit Marke, mit Adressen und mit einer Sprechprobe, die eine Datei
> wegnimmt. §9 misst es nach, und es ist dabei etwas herausgefallen.

### Die Verschärfung steht im SCHNELLLAUF, und die Zahl steht daneben

| | vorher | nachher |
|---|---|---|
| `ki-pc-fisch-101` | 0,85 s | **2,7 s** (2,73 · 2,66 · 2,72) |
| lokal (20 Kerne) | 1,0 s | **5,9 s** (5,87 · 5,83) |
| davon der Übersetzerdurchgang | — | 1,8 s / 4,0 s (166 `cc`-Aufrufe über 83 Erzeugnisse) |

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

Also wurde die Gegenfrage gestellt — **wie viel Luft hat das Tor?** Die 83 Erzeugnisse noch
einmal, `-Wall -Wextra -Werror -O2` plus *je einen* schärferen Schalter (`gcc 16.2.1`):

```
-Wpedantic  -Wsign-conversion  -Wshadow  -Wcast-qual  -Wstrict-prototypes
-Wmissing-prototypes  -Wswitch-enum  -Wfloat-equal  -Wundef  -Wwrite-strings
-Wold-style-definition  -Wvla                       0 von 83 fallen

-Wconversion         3 von 83        -Wdouble-promotion   2 von 83
-Wredundant-decls    1 von 83        -Wpadded            42 von 83
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

---

## 9. Die Empfindlichkeit: **25 → 0** — und der Wächter war der erste Befund

*Gemessen am Abend des 2026-08-31, lokal (`free -g`: 31 GB gesamt, 17 GB verfügbar,
20 Kerne). Fünf Programme, eine Giftprobe, eine vierte Sprechproberichtung.*

§7 nennt die Zahl als Satz: *25 Wörter hängen an je einer Datei.* Ein Satz in einem Dokument
steigt unbemerkt. Er steht jetzt als **Zahl im Wächter** (`MARKE_ALLEIN`), mit den Adressen
daneben und mit einer Probe, die ihn misst.

### 9.1 Erst einteilen, dann schreiben

`messung/EINSAME-WOERTER.md` nimmt die 25 einzeln und fragt je Wort: **warum nur diese
Datei?** Drei Klassen, und die Einteilung ist der Ertrag:

| Klasse | Wörter | Antwort |
|---|---:|---|
| **⟨G⟩ Bündel aus der GRAMMATIK** | 9 | `walkdecl` ist EINE Produktion; `opdecl` braucht `table`+`slot`+`occupied` |
| **⟨A⟩ Bündel aus der AUTORSCHAFT** | 8 | eine Datei gegen eine LISTE geschrieben — grammatisch unverwandt |
| ⟨Z⟩ Zufall | 8 | gewöhnliche Wörter, einmal geschrieben |
| ⟨E⟩ eng | 1 (Form) | `bootdecl` — siehe 9.5 |

> **⟨A⟩ ist der Befund über die eigene Methode.** Acht der 25 hingen an
> `messung/grammatik/zahlbreiten.gab` und `geraeteworte.gab` — den zwei Dateien, die in der
> Nacht davor gegen genau diese Lücke geschrieben wurden. *Eine Lücke mit EINER Datei zu
> schließen verschiebt sie.* Darum heißt die Antwort unten nicht „noch eine Datei".

### 9.2 Fünf Programme, jedes mit einem Gegenstand

| Datei | verteilt | Gegenstand |
|---|---|---|
| `messung/grammatik/blocklauf.gab` | `walk` `levels` `node` `down` `leaf` `mappings` | der Indirektionsbaum eines Inodes — **keine zweite Seitentabelle** |
| `messung/grammatik/tabellenworte.gab` | `insert` `remove` `relabel` `exists` | ein Gerätebaum: Gerät am Bus am Bus |
| `messung/grammatik/messreihe.gab` | `i8` `i16` `i32` `i64` `and` `min` `finite` `sizeof` | eine Messreihe — Abweichungen sind vorzeichenbehaftet |
| `messung/grammatik/raumworte.gab` | `port` `rc` `seq` `boot` `prim` `allocs` `use` | ein Zeitgeber am Altlastenbus |
| `beispiele/gift/413-…gueltig.gab` | — | die Giftprobe zu Befund A unten |

**Alle vier Messprogramme: 0 Prüferfehler, 0 Hinweise, 0 `C001`, `cc -Werror` grün bei `-O0`
und `-O2`.** Der Korpus wächst von 83 auf 88 vollständig emittierende Dateien; 87 übersetzen.

```
vorher   25 Woerter an je EINER Datei · 15 an zwei · Median 4
nachher   0 Woerter an je EINER Datei · 38 an zwei · Median 4
```

`gesenkt` bleibt bei 214, `UNGEDECKT` bei 4. **Kein Wort ist dazugekommen** — die Programme
decken nichts Neues ab, sie machen die vorhandene Deckung unempfindlich. *Das ist der ganze
Zweck, und es ist wichtig, dass es sich in keiner Deckungszahl zeigt.*

### 9.3 Befund A — ein Formatfeld, das `gueltig` heißt, und der Erzeuger schreibt den Namen zweimal

Gefunden **beim ersten Lauf von `blocklauf.gab`, ungesucht**: das Gültigkeitsbit eines
Blockzeigers hieß `gueltig`, das naheliegendste Wort seiner Domäne.

```c
static inline bool Blockzeiger_gueltig(const Blockzeiger *v)   /* der FELDLESER            */
static inline bool Blockzeiger_gueltig(const Blockzeiger *v)   /* die Pruefkoerperfunktion */
```

`cc`: *redefinition*. Der Prüfer: **0 Fehler, 0 Hinweise.** Der Erzeuger: **0 `C001`.**

Und es ist eine **Familie**, keine Einzelstelle — drei Namensmuster aus einem Präfix, zwei
davon kollidierbar:

```
{Format}_gueltig       die Pruefkoerperfunktion (emit.rs:3369)  <->  ein Feld `gueltig`
{Format}_setz_{feld}   der Schreiber                            <->  ein Feld `setz_<feld>`
{Format}_{feld}        der Leser                                --   die Quelle beider
```

> **`N041` (`cnamen.rs`) fängt es nicht, und das ist kein Versehen jenes Passes.** Er hält die
> Namen, die C schon **vergeben** hat — C11-Wort, Kopfdatei, eingebaut; `gueltig` ist keiner
> davon. Die Kollision entsteht zwischen zwei Namen, die der **Erzeuger selbst** bildet. *Ein
> Namenswächter, der nur die fremden Namen kennt, misst die fremden.*

Beide Formen stehen als `beispiele/gift/413-format-feld-heisst-gueltig.gab` im Baum. **Sie
liegt in `gift/` und nicht in `messung/proben/`, weil sie EMITTIERT** — unter
`messung/proben/` hätte Stufe 9 von `pruefe-emission.sh` rot gemeldet, und daran arbeitet in
dieser Nacht eine andere Bahn. Gehalten wird sie trotzdem: **vom Übersetzungstor dieser
Tafel, dessen Reichweite `beispiele/gift/` einschließt.** Genau die vier Dateien
Reichweitenunterschied aus §7 fangen hier zum ersten Mal etwas. *Dass Stufe 9 sie nicht
sieht, ist der zweite Befund und gehört der anderen Bahn; die zwei Wege — Reichweite
ausdehnen oder benannter Eintrag in `ausnahme_grund()` — stehen in der Datei und werden hier
nicht gegangen.*

### 9.4 Befund B — der WÄCHTER war der Befund, und zwar dieser hier

Richtung (c) der Sprechprobe nahm bis heute **ein Wort, das in genau EINER Datei steht**, und
prüfte, dass es `UNGEDECKT` wird, wenn deren C vergiftet ist. Sobald die 25 verteilt waren,
gab es kein solches Wort mehr — und der Wächter meldete

```
GESCHEITERT  keine Datei traegt ein Wort allein -- die Probe misst nichts
! Die Tafel misst nicht, was sie behauptet. ABBRUCH.       (Rücklaufwert 2)
```

**Die Arbeit, die den Baum verbessert, hat den Wächter abgeschaltet.** Nicht der Baum war
falsch, die Probe war es: *eine Probe, deren Gegenstand „kostet eine gefallene Übersetzung
eine Zelle?" ist, darf nicht daran hängen, dass der Korpus eine dünne Stelle HAT* — die dünne
Stelle ist das, woran gearbeitet wird.

Sie nimmt jetzt das Wort mit der **kleinsten Trägermenge** und vergiftet **jeden** Träger. Bei
einem Träger ist das die Probe von gestern, bei zweien ein `cc`-Lauf mehr, und sie misst auch
nach der nächsten Runde noch. `verfaelsche` nimmt dafür seit heute eine **Menge** von Dateien
statt einer.

### 9.5 Was NICHT geheilt wurde: die Form `bootdecl`

`boot` steht an **zwei** Grammatikstellen — `bootdecl` (:245) und `space` (:463).
`raumworte.gab` schreibt es als Adressraum (`ptr<boot, r>`), und damit ist das **Wort** an
zwei Dateien gedeckt. **Die Form `bootdecl` bleibt allein in `beispiele/07`, und das ist
richtig:**

> Ein `bootdecl` ist die Modusleiter EINER Maschine. `write_cr3` · `write_cr4(PAE)` ·
> `wrmsr_efer(LME)` · `write_cr0(PG)` ist *der* x86_64-Weg in den Langmodus, nicht *ein* Weg.
> Ein zweites `bootdecl` wäre eine **Abschrift** — Falle 80 im Kleinen, ein Programm nur damit
> ein Zähler steigt — oder `aarch64`, und das ist versiegelt.

*Die Einsamkeit ist benannt und nicht geheilt.* Und der Satz daneben gehört dazu: **das Wort
ist an zwei Dateien, die Form an einer.** Wer nur den Zähler nennt, hat den `bootdecl`
stillschweigend für gedeckt erklärt — §6.2 sagt seit jeher, dass ein Terminal keine Form ist,
und hier kostet dieser Satz etwas.

### 9.6 Die Zahl im Wächter — gedruckt, **nicht** geratscht

```
== EMPFINDLICHKEIT: 0 Woerter haengen an je EINER Datei (Marke 0) ==
   125 der 219 Terminale sind NUR durch Absenkung gedeckt …
   an je ZWEI Dateien: 38 (Marke 38, ohne Ratsche …)
```

Steigt sie, druckt der Lauf jedes Wort mit seiner Adresse. **Der Rücklaufwert ändert sich
nicht**, und der Grund steht an der Marke:

* Eine Marke, die auf dem Lauf gesetzt wird, der sie zum ersten Mal gemessen hat, ist eine
  **Vermutung** — diese Zahl ist in einer Nacht von 25 auf 0 gesprungen.
* Sie wächst aus **zwei** Richtungen: ein neues Terminal, das genau ein Programm schreibt,
  hebt sie, ohne dass etwas schlechter geworden wäre (*Ratschen: Steigen braucht seinen Grund
  an der Marke*).
* Und ein Anstieg wäre **unsichtbar** in einem Rot, das eine andere Ursache hat — die vier
  `UNGEDECKT`-Zellen.

> **Der Vorschlag steht daneben, damit der nächste Lauf ihn nicht erfinden muss:** sobald die
> vier Zellen entschieden sind und dieser Wächter grün werden kann, soll das Überschreiten von
> `MARKE_ALLEIN` den Rücklaufwert mitentscheiden. *Eine unsichtbare Ratsche ist schlechter als
> eine gedruckte Zahl.*

Die zweite Zahl (Wörter an genau **zwei** Dateien, heute 38) trägt **absichtlich keine
Ratsche**: sie steigt, wenn Wörter aus der Einserspalte herunterwandern — also wenn es besser
wird. *Eine Ratsche auf einer Zahl, die beim Verbessern wächst, bestraft die Heilung.*

### 9.7 Die Sprechprobe, in beide Richtungen

Die vierte Richtung nimmt eine Datei weg und verlangt, dass die Zahl **steigt** — und dass
jedes neu einsame Wort in genau dieser Datei stand. *Eine Zahl, die steigt, ist noch kein
Beleg dafür, dass das Wegnehmen sie hat steigen lassen.*

```
ok   ohne `beispiele/01-tabelle.gab` steigt die Einsamkeitszahl (0 -> 1)
ok   und jedes neu einsame Wort stand in der entfernten Datei
```

Und von Hand, mit einer ganzen Datei aus dem Baum genommen — `raumworte.gab` beiseite:

```
! EMPFINDLICHKEIT GESTIEGEN: 7 statt 0.
    allocs  beispiele/09 · boot beispiele/07 · port geraeteworte · prim beispiele/07
    rc geraeteworte · seq geraeteworte · use beispiele/29
```

### 9.8 Der Preis

| | vorher (83 Dateien) | jetzt (88 Dateien, 13 Proben) |
|---|---|---|
| lokal (20 Kerne) | 5,9 s | **6,2 s** (6,20 · 6,26 · 6,15) |

`abnahme.py` gibt jedem leichten Wächter **600 s**. Die Empfindlichkeitsprobe selbst kostet
nichts als Text — sie liest die Trägerkarte, die ohnehin gerechnet wird; die 0,3 s sind die
fünf neuen Dateien und der zweite vergiftete Träger.

### 9.9 Und was hier NICHT entschieden wurde

* **Nichts über die vier Zellen.** `chain`, `queue`, `state`, `threads` stehen unverändert;
  der Lauf bleibt rot, und das ist das gewollte Rot.
* **Nichts über den `Format_gueltig`-Zusammenstoß.** Der Befund hat eine Adresse, eine
  Giftprobe und zwei Formen; ob der Erzeuger die Namen entzerrt oder ein Prüferpass sie
  abweist, ist eine Entscheidung über die Absenkung.
* **Nichts über die Reichweite von Stufe 9.** Sie sieht `beispiele/gift/` nicht, und die
  Giftprobe liegt genau dort. Das gehört `pruefe-emission.sh`.
* **Nichts darüber, ob die Absenkungen RICHTIG sind.** Zwei Träger statt einem machen die
  Messung unempfindlich, nicht die Sprache richtig. `ptr<port, r>` senkt in `raumworte.gab`
  genauso zu einem gewöhnlichen Ladebefehl ab wie in `geraeteworte.gab` — §3 Befund 2, ein
  zweites Mal und unabhängig, und `ptr<boot, r>` ebenso: `ctyp` liest `z.raum` für **jeden**
  Raum außer `mmio` nicht. *Die Adresse dieses Befundes ist breiter, als der Satz von gestern
  sagte.*
