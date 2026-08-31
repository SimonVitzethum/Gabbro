# Die Rücklaufwerte der ~~28~~ ~~46~~ **50** Wächter — was jeder Wert BEDEUTET

*Gemessen 2026-08-31. Grundlage: der Quelltext jedes Wächters und ein Lauf jedes Wächters
über einem **leeren Baum** (`instrumente/` kopiert, sonst nichts) — die Messung, die
„leere Grundgesamtheit" von „nichts gefunden" trennt.*

> **Die Tafel unten führt 28, die Abnahme fährt ~~46~~ 50** *(2026-08-31)*. An diesem Tag
> sind die 18 `zaehle-*` dazugekommen; ihre eigene Tafel steht unter *Die achtzehn Zähler*.
> Am Abend kamen `pruefe-grammatiktafel.py`, `zaehle-absagen.py`, `zaehle-gifttreffer.py` und
> `pruefe-uebersetzerfamilie.py` hinzu — **die Zahl steigt, weil der GEGENSTAND wächst**, und
> das ist die eine erlaubte Richtung für eine Ratsche. Die Nummerierung der großen Tafel
> bleibt bei 28, weil sie den Stand beschreibt, an dem diese Messung angefangen hat.

> **Ein Werkzeug, das nichts gemessen hat, darf nicht so aussehen wie eines, das etwas
> gefunden hat.** In der Nacht auf den 2026-08-31 hat dieser Unterschied zweimal eine Stunde
> gekostet: `pruefe-grammatiktafel.py` brach ab (*„es wurde NICHTS gemessen"*) und
> `abnahme.py` zeigte die Absage in derselben Zeile und derselben Farbe wie vier offene
> Zellen. *Null Dateien ist eine Absage, kein Ergebnis* (W1, W17).

## Die drei Klassen

```
0   gruen     -- gemessen, kein Befund
1   BEFUND    -- gemessen, und es steht etwas offen
2   ABBRUCH   -- es wurde NICHTS gemessen (fehlende Vorbedingung, gefallene
                 Sprechprobe, leere Grundgesamtheit, Frist, Absturz)
```

**Die Trennlinie beantwortet EINE Frage: wer muss sich ändern?**

| | |
|---|---|
| **`1` — der BAUM** | eine Lücke, eine gebrochene Ratsche, eine veraltete Buchung, eine Theorie ohne `ROOT`-Eintrag. Jemand schreibt eine Zeile im Repository. |
| **`2` — die UMGEBUNG** | fehlendes Werkzeug, leere Grundgesamtheit, gefallene Sprechprobe, überschrittene Frist, unlesbarer Gegenstand. Am Baum ist damit **nichts** gesagt. |

Die Regel für die Sprechprobe stand schon geschrieben, nur nicht überall: `abnahme.py`
beendet eine gefallene Sprechprobe mit `2` und dem Satz *„misst nicht, was er behauptet.
ABBRUCH."* Ein Wächter, der seine eigene Logik nicht besteht, hat **nichts** gemessen — was
er danach über den Baum sagt, ist keine Aussage über den Baum.

**Zwei Rangstufen der Gefahr**, und sie stehen in dieser Reihenfolge:

1. **Leere Grundgesamtheit → `0`.** *Ein positives Urteil über nichts* (W17). Es sieht aus
   wie ein Ergebnis, wird nie nachgerechnet und deckt alles.
2. **Fehlende Vorbedingung → `1`.** Sieht aus wie ein Rückstand. Kostet eine Stunde
   Suche nach einem Befund, den es nicht gibt — und wenn er gefunden wird, ist der Wächter
   inzwischen als „bekannt rot" gebucht.

## Die Tafel

*Spalte „leer" ist gemessen: der Rücklaufwert über dem leeren Baum, **vorher → nachher**.*

| # | Wächter | 0 | 1 | 2 | leer | war vermischt |
|---|---|---|---|---|---|---|
| 1 | `mutiere-pruefer.py` | sauber | tote Anker, unbekannte Fläche | `crates/` schmutzig, **4 Sprechproben** | 1 → **2**¹ | Sprechprobe → 1 |
| 2 | `pruefe-abstieg.py` | sauber/gebucht | neue Lücke, veraltete Buchung | **6 Sprechproben, `lib.rs::unterbloecke` fehlt** | 1 → **2**¹ | **kein `2`** |
| 3 | `pruefe-aufloesung.py` | sauber | Ratsche | Sprechprobe | 1 → **2**¹ | — |
| 4 | `pruefe-beweise.sh` | ALL PASS | Fehler, **`ROOT`-Lücke** | **Isabelle fehlt · Sprechprobe · Wachhund · OHNE NACHWEIS · keine `.thy`** | 1 → **2** | **kein `2`** |
| 5 | `pruefe-emission.sh` | ALL PASS | ~50 Stufenbefunde | **kein `cargo`/`cc` · 10 Sprechproben** | 1 → **2** | **kein `2`** |
| 6 | `pruefe-englisch.py` | ALL PASS | Ratschen | drei Sprechproben, **leere Quellenmenge** | **0 → 2** | **leer → grün** |
| 7 | `pruefe-grammatiktafel.py` | 0 ungedeckt | ungedeckte Zellen | Sprechprobe, **„KEIN LAUF"** | 1 → **2**¹ | Abbruch → 1 |
| 8 | `pruefe-gruende.py` | sauber | — | **Sprechprobe · null Absagetexte** | **0 → 2** | **leer → grün**, Sprechprobe → 1 |
| 9 | `pruefe-kennungen.py` | ALL PASS | Doppelbelegung | **Sprechprobe · null Kennungen** | **0 → 2** | **leer → grün** |
| 10 | `pruefe-klauseln.py` | keine neue | neue Fundstelle | **Selbsttest** | 1 → **2** | Abbruch → 1 |
| 11 | `pruefe-konstrukte.py` | keine neue | neue ohne Probe | **Sprechprobe (enthält den Leertest)** | 1 → **2**¹ | Abbruch → 1 |
| 12 | `pruefe-lean-beweis.sh` | LEAN GREEN | rote Module | **5 Absagen + Frist je Modul** | 1 → **2** | **kein `2`** |
| 13 | `pruefe-lean-programm.sh` | LEAN GREEN | rote Ausfuhr | **5 Absagen** | 1 → **2** | **kein `2`** |
| 14 | `pruefe-luecken.py` | ALL PASS | offene/tote Anker | schmutzig · Nullauf rot · Rückgabe | 2 → 2 | **VORBILD** |
| 15 | `pruefe-notation.py` | alles zu | stumme Absage | **Prüfer baut nicht · Prüfer antwortet nicht** | 1 → **2** | Abbruch → 1; Bauausfall unerkannt |
| 16 | `pruefe-p6-beweis.sh` | ISABELLE GRUEN | rote Pflicht | **5 Absagen** | 1 → **2** | **kein `2`** |
| 17 | `pruefe-reichweite.py` | keine Lücke | ungelesen | **Sprechprobe** | 1 → **2** | Sprechprobe → 1 |
| 18 | `pruefe-saetze.py` | sauber | Ratsche, erfundene Kennung | Sprechprobe · Binär fehlt/veraltet · Frist | 2 → 2 | **VORBILD** |
| 19 | `pruefe-schablonen.py` | sauber | Ratsche, Prämisse ohne Adresse | **2 Sprechproben** + Binär/Frist/Format | 2 → 2 | Sprechprobe → 1 |
| 20 | `pruefe-sonden.sh` | keine widerlegt | widerlegt, ungebaut | **Sprechprobe · null Sonden** · Argument | **0 → 2** | **leer → grün** |
| 21 | `pruefe-syntax.sh` | ALL PASS | verbotene Form, Warnungen | **6 Sprechproben · Dokument fehlt · Bau bricht ab** | 1 → **2** | **kein `2`**; Bauausfall → grün |
| 22 | `pruefe-todo.py` | ALL PASS | Befunde | **Sprechprobe** | 1 → **2**¹ | Sprechprobe → 1 |
| 23 | `pruefe-vergabe.py` | Ratsche hält | Ratsche | **Sprechprobe** | 1 → **2** | Sprechprobe → 1 |
| 24 | `pruefe-waechter.py` | keine Verletzung | Verletzungen | **Sprechprobe** | 0 → 0² | Sprechprobe → 1 |
| 25 | `pruefe-widerruf.py` | ALL PASS | lebende Vorkommen | Eintrag · Sprechprobe · **Gegenstand fehlt** | 1 → **2** | **VORBILD**, bis auf den Absturz |
| 26 | `pruefe-wortschatz.py` | deckt | fehlt/tot/unerreichbar | **Sprechprobe · leere Tabelle/EBNF** | 1 → **2**¹ | **kein `2`**; leer → grün |
| 27 | `pruefe-zahlen.py` | keine Abweichung | Abweichung, Selbstbezug | **4 Sprechproben**, **„0 von 0"** | 1 → **2** | ~~GEBUCHT — fremde Bahn~~ **eingelöst 2026-08-31** |
| 28 | `pruefe-zitate.py` | Ratsche hält | Ratsche | Sprechprobe, **2 ABORT-Zweige** | 1 → **2** | Abbruch → 1 |

¹ ~~Der leere Baum trifft diese sieben in einem `FileNotFoundError`, bevor irgendein Riegel
greift: Python beendet mit `1`.~~ **Erledigt am 2026-08-31**: je Wächter ein
GEGENSTANDSRIEGEL („Zahn 0"), und alle sieben enden mit `2` und einer benannten Absage —
`lib.rs`, `umgebung.rs`, `SYNTAX.md` (im geladenen Modul!), `ast.rs`, `README.md`,
`sys.argv[1]` und `m1.rs`. *Ein Werkzeug, das seinen Gegenstand nicht findet, hat nichts
gemessen.*

² `pruefe-waechter.py` liest `instrumente/pruefe-*` und findet sich dabei immer selbst —
seine Grundgesamtheit kann nicht leer werden. Die `0` ist kein Fehlurteil.

**Über dem leeren Baum standen vorher 3 benannte Absagen mit `2`, dann 18 — und seit dem
2026-08-31 sind es 27 von 28.** Der eine Rest ist `pruefe-waechter.py`, und seine `0` ist
kein Fehlurteil (Fußnote 2). **Null Tracebacks.**

## Die achtzehn Zähler — gemessen am 2026-08-31, und danach in der Abnahme

`abnahme.py` sagte über sie: *„Sie messen, sie bewachen nicht — kein Rücklaufwert, der ein
Urteil trägt. Die Grenze steht hier, damit sie jemand verschieben KANN."* Der Satz war eine
Behauptung, und derselbe leere Baum hat sie widerlegt:

| leer, vorher | wie viele | leer, nachher |
|---|---:|---|
| `1` mit `FileNotFoundError` (Traceback) | 6 | `2` mit benanntem Gegenstand |
| `1` mit gedruckter Absage | 9 | `2` |
| `2`, sauber abgesagt | 3 | `2` |
| `0` über einem grünen Urteil über nichts | **0** | — |
| `0`, weil der Gegenstand ein FREMDER Baum ist (`zaehle-narrow.py`) | 1 | `0`, zu Recht |

**Kein einziger von 18 trug KEIN Urteil — sie hatten nur keins bekommen.** Und einer war
seit Tagen rot, ohne dass es jemand sah: `zaehle-karten.py` maß 40 direkte Kartenblicke
(36 unqualifiziert) gegen die Ratsche 36 / 32. *Ein Wächter, den niemand fährt, ist von
einem, den es nicht gibt, nicht zu unterscheiden* — der Satz, auf dem `abnahme.py` steht,
gegen die Grenze, die `abnahme.py` selbst gezogen hat.

**41 Ausgänge gingen von `1` auf `2`**, in zwölf Zählern. Was draußen bleibt, steht in
`pruefe-waechter.py:OHNE_URTEIL` — **leer**, und die Abnahme druckt die Zahl.

## Die Form, die alle Vorbilder teilen

```python
    if not BIN.is_file():
        print(f"ABBRUCH: {BIN} fehlt -- gebaut wird auf ki-pc-fisch-101 (CLAUDE.md).",
              file=sys.stderr)
        sys.exit(2)
```

Drei Bestandteile, und keiner ist Schmuck: das **Wort** `ABBRUCH`, der **Grund** samt Heilung,
und der **Rücklaufwert 2**. Wer nur zwei davon schreibt, hat einen Wächter, dessen Absage
sich als Befund liest.

## Der Riegel gegen den Rückfall — Forderung 6 in `pruefe-waechter.py`

Forderung 3 verlangt *„ein Abbruch verlässt mit einem Rücklaufwert ungleich null"* — und `1`
ist ungleich null. Die sechste ist die fehlende Hälfte: **eine gedruckte Absage endet mit 2.**
Erkannt wird die AUFRUFSTELLE (`print(` am Anweisungsanfang, `echo` in der Shell) und der
nächste Ausgang innerhalb von sechs Zeilen.

Ihre Reichweite ist gemessen statt behauptet:

Und seit dem 2026-08-31 hat sie eine **zweite Hälfte**, weil die erste ein Absagewort auf
einer druckenden Zeile braucht — und eine gefallene Sprechprobe druckt nichts:

```python
    if not sprechprobe():
        return 1
```

| | gedruckte Absage → 1 | stumme Probe → 1 |
|---|---|---|
| über dem Stand vor Posten 3 (`99e2145`) | **44 Stellen in 15 Dateien** | **9 Stellen in 9 Dateien** |
| davon in Dateien, die die gedruckte Hälfte GAR NICHT sah | — | **2** (`pruefe-todo.py`, `pruefe-vergabe.py`, ganz) |
| heute | **0** | **0** |
| über den 18 `zaehle-*` am 2026-08-30 | 40 | 6 |
| über den 18 `zaehle-*` heute | **0** | **0** |

**Das weitere Muster wurde gemessen und verworfen**: ein bloßes `\bproben?\b` meldet
`$name-probe` und `abi-proben/` in `pruefe-emission.sh` — vier Stufenbefunde, die RICHTIG
eine `1` sind. *Eine Regel mit Fehlalarmen wird ignoriert, und dann schützt sie nichts.*

Sie gilt seit dem 2026-08-31 für **alle ~~47~~ 50**: die `zaehle-*` sind in die Abnahme
aufgenommen, und `ABBRUCH_GEBUCHT` steht leer.

**Und am selben Abend hat ihre Wortliste eine Lücke gezeigt**, gefunden nicht von ihr,
sondern vom Sieb darunter: sie führte `SPRECHPROBE GESCHEITERT` beim Namen und sah eine
**RÜCKWÄRTSPROBE**, die fällt, nicht — zwei Stellen in `zaehle-pflichten.py`, beide mit `1`.
Das Muster heißt jetzt `PROBE\b[^\n]*(GESCHEITERT|UNTAUGLICH)` und trifft im ganzen Ordner
genau diese zwei; beide sind auf `2` geheilt. *Eine Regel, die die Wörter aufzählt, die sie
schon gesehen hat, misst die Wörter, die sie schon gesehen hat.*

## Gebucht statt geheilt — mit Grund

| Stelle | Warum sie bleibt |
|---|---|
| `pruefe-zahlen.py`, drei Stellen | **Fremde Bahn.** Sie übersetzt diese Datei in derselben Nacht; zwei Läufe auf einer Datei zerstören einander (`CLAUDE.md`). Steht als einziger Eintrag in `ABBRUCH_GEBUCHT`. |
| tote Anker in `mutiere-pruefer.py` → 1 | Ein toter Anker ist ein Befund ÜBER DEN KATALOG. Er verkleinert die Bezugsgröße, und genau das ist die Klage — der BAUM muss sich ändern. |
| `ROOT`-Lücke in `pruefe-beweise.sh` → 1 | Eine Theorie ohne Sitzungseintrag ist ein Loch IM BAUM. Ihr Text sagte „es wurde NICHTS an ihnen geprüft" und las sich wie ein Abbruch; er sagt jetzt, was er meint. |
| `UNGEBAUT` in `pruefe-sonden.sh` → 1 | Teilmessung: die anderen Sonden sind gelaufen, und das Loch steht mit einer Zahl in der Ausgabe. |
| „ergibt keine Theorie" / „zwei Einheiten heißen gleich" (p6, lean) → 1 | Aussagen über das ERZEUGNIS: der Erzeuger liefert etwas, das die vereinbarte Form nicht hat. |
| ~50 weitere `exit 1` in `pruefe-emission.sh` | Echte Befunde je Stufe. Nur der Kopf und die zehn Sprechproben sind Abbruch. |
| `pruefe-waechter.py`, leere Besetzung | Nicht erreichbar — er liest sich selbst mit. |
| `pruefe-aufloesung.py`, leere Quellenmenge | Nicht erreichbar — dieselbe Menge trägt `umgebung.rs`; ist sie leer, stürzt der Wächter vorher ab. |

## Die fünf Posten von damals — alle fünf eingelöst am 2026-08-31

| Posten | was gemessen wurde | was sich geändert hat |
|---|---|---|
| 1 — sieben `FileNotFoundError` | leerer Baum: 7 × Wert `1` mit Traceback | je ein GEGENSTANDSRIEGEL; 7 × `2` mit benannter Absage, 0 Tracebacks |
| 2 — Forderung 6 sieht die stumme Probe nicht | über `99e2145`: 44 gedruckte, **9 stumme**, davon 2 ganze Dateien, die die gedruckte Hälfte nie sah | zweite Hälfte in `pruefe-waechter.py`, mit drei Richtungen in der Sprechprobe |
| 3 — Probe nur auf Bestellung | `grep` über zehn Flaggen in acht Dateien: **genau eine** schaltete eine Probe ein | `pruefe-kennungen.py` fährt sie immer; und ihre Gegenrichtung nimmt ihren Maßstab nicht mehr vom Gegenstand |
| 4 — 18 `zaehle-*` außerhalb | leerer Baum: **kein einziger** gab ein grünes Urteil; 6 Tracebacks, 9 Absagen mit `1` | alle 18 in der Abnahme, `OHNE_URTEIL` leer, 41 Ausgänge von `1` auf `2` |
| 5 — Reichweite zählt je WERT | 145 unbewachte Zellen, davon **35 hinter einer Kollision** | Schlüssel trägt den ORT; 145 → **180**, und 9 von 76 Einträgen zeigen wirklich auf eine Zelle |

## Was offen bleibt

* **`zaehle-karten.py`s Ratsche ist auf den gemessenen Stand GEZOGEN, nicht geheilt**:
  36 / 32 → **40 / 36**. Die vier neuen direkten Kartenblicke liegen in `emit.rs` und
  `m1.rs` und gehören dem, der `crates/` führt. *Sie sind Schuld, kein Erfolg* — und sie
  sind der Beleg für Posten 4: der Zähler kam **rot bei `master` an** und wurde von keinem
  Sammellauf gelesen.
* **`pruefe-grammatiktafel.py` bleibt rot**, an seinen vier `UNGEDECKT`-Zellen. Eine
  Sprachentscheidung des Ordners, kein Werkzeugfehler.
* ~~**`pruefe-emission.sh` ist seit dem 2026-08-31 abends eine `TEILMESSUNG`, keine
  `ROT`.**~~ Er starb in **Stufe 9 von 10** an den sechs `messung/tor-proben/`, deren
  erzeugtes C nicht übersetzte — **Stufe 10 (die Bibliothekskette) lief nicht.**
  **NACHGESEHEN am 2026-08-31 über `f08e5ad`, lokal, `rc=0`: Stufe 10 läuft, und sie ist
  nicht nur angetreten.** Alle acht ihrer Teilproben stehen mit Text da — zwei `.gabi` je
  mit Marke, die Ausfuhr ohne die beiden privaten Helfer, `pruefe` mit 0 errors über die
  Grenze, drei getrennt übersetzte Einheiten unter `-Werror`, drei `pub`-Namen außen, ein
  Programm aus drei Objekten unter `-O0` **und** `-O2`, das Ergebnis `2007 65535` (der
  private Helfer hat gedeckelt) und **zwei Sprechproben, die beide beißen**: ein
  verfälschter privater Helfer ändert das Ergebnis, und `N039` sagt ab, wo sonst der Binder
  es getan hätte. Stufe 9 meldet **101 von 101** und eine umgekehrte Probe. *Der Posten ist
  eingelöst, und er war eine Aussage über den `crates/`-Baum, nicht über den Wächter.*

  > **Das ist der Beleg dafür, wozu die Marke da ist**, und er ist an einem Tag entstanden.
  > Zwei Wochen lang sah derselbe Wächter aus wie einer, der zu Ende gemessen hat; seit
  > gestern abend sagte er, wo er aufhörte; heute hört er nicht mehr dort auf. **Die Marke
  > hat den Befund nicht geheilt — sie hat ihn SICHTBAR gemacht**, und geheilt hat ihn, wer
  > `crates/` führt.
* **18 von 99 emittierenden Dateien fallen bei `clang`, nicht bei `gcc`** — alle an
  `-Wunused-function` über emittierten `static inline`-Zugriffen. `MARKE_FAMILIENUNTERSCHIED`
  steht auf 18, gezogen und nicht geheilt; die Heilung gehört `emit.rs`.
* **Die 180 unbewachten Zellen sind jetzt ehrlich gezählt und damit größer geworden.** 41
  davon tragend, 37 mit geschriebenem Grund, **4 offen** — das ist die Arbeitsliste.
* ~~**Der leere Baum ist die billigste Absage, nicht die einzige.** Ein Wächter, dessen
  Vorbedingung erst MITTEN im Lauf wegbricht, ist hier weiter nicht erfasst.~~
  **GEMESSEN am 2026-08-31, und zwar an einem Fall mit Datum.** Siehe den eigenen Abschnitt
  *Der Schnitt mitten im Lauf* darunter: **44 von 50** Wächtern können mitten im Lauf
  abbrechen, **251 Ausgangsstellen** liegen hinter dem jeweils ersten. Abgelesen mit
  `./instrumente/pruefe-waechter.py`, nachgerechnet von `pruefe-zahlen.py`.
  **Und am selben Abend GEHEILT**, soweit eine Form das kann: 92 gefährliche Stellen, alle
  gedeckt, `MARKE_TEILMESSUNG = 0`, und die Abnahme trennt eine `TEILMESSUNG` vom Befund.
  *Was bleibt, ist die Ansage — nicht das Ausbleiben des Schnitts.*
  **Und die Deckung wird seit dem 2026-08-31 je STELLE gezählt und nicht je Datei** —
  92 von 92, Differenz null. Die Marke ist nicht gestiegen, und das ist gemessen.
* **Die Klasse „nur eine Stelle der Datei ist gedeckt" ist gemessen und leer** — aber zwei
  Wächter gelten als gedeckt, **weil sie das Wort in ihrer eigenen Beschreibung tragen**:
  `pruefe-waechter.py` und `abnahme.py`. Beide haben heute null gefährliche Stellen, also
  kostet es nichts; der Zähler je Stelle nimmt ihnen die Ausnahme, weil er nach der
  VERDRAHTUNG fragt. *Es war eine gelegte Falle und kein Schaden.*
* **Ein Wächter ist für die Frage „wird heute abgeschnitten?" NICHT gemessen**, und er
  steht mit Grund da: `zaehle-b3.py` (`NICHT FAHRBAR` — die Caprock-Messbasis fehlt im
  Arbeitsbaum). **48 von 49 sind gemessen, null davon abgeschnitten** — die drei, die die
  schlichte Abnahme auslässt, sind einzeln nachgefahren. *Nachgemessen am selben Abend:
  die 48 gelten nur im ARBEITSBAUM* — `/home/simon/Dokumente/caprock-messbasis` existiert,
  und gegen diesen Pfad läuft `zaehle-b3.py` grün (105 Dateien, 2536 Rümpfe, 0 Abbrüche).
  Der relative Pfad zeigt aus einem `git worktree` heraus daneben. Siehe unten.
* **Die Schalenregel ist großzügig, und das ist geprüft und nicht gehofft**: ein `exit` in
  einem Funktionsrumpf gilt als gedeckt, weil der Rumpf aus dem Hauptlauf gerufen wird.
  Nachgesehen wurde, ob eine solche Funktion **vor** der Falle gerufen wird — in keinem der
  sieben Schalenwächter. *Wer die Reihenfolge ändert, muss diese Zeile neu messen.*
* **`OHNE_URTEIL` steht leer, und das ist eine Zusage an die Zukunft, keine Messung über
  sie.** Wer einen Zähler wieder herausnimmt, schreibt den Grund dazu — die Zahl der
  Ausgenommenen druckt die Abnahme.

## Der Schnitt mitten im Lauf — der Posten, den der leere Baum offen lässt

*Gemessen 2026-08-31 mit `./instrumente/pruefe-waechter.py` (Abschnitt „Ein Abbruch MITTEN
im Lauf"), Sprechprobe in beide Richtungen im selben Lauf.*

```
44 von 50 Wächtern können mitten im Lauf abbrechen
251 Ausgangsstellen liegen hinter dem jeweils ersten
  pruefe-emission.sh   62 Ausgänge, 156 Druckstellen dahinter
  mutiere-pruefer.py   12 Ausgänge,  50
  pruefe-syntax.sh     11 Ausgänge,  14
  zaehle-pflichten.py  10 Ausgänge,  67
  pruefe-lean-beweis.sh 8 Ausgänge,  32
```

**Der Fall, an dem die Klasse ihren Namen bekommen hat.** `pruefe-emission.sh` starb am
2026-08-31 an `F06`s `N043` in der vierten von zehn Stufen, mit `exit 1`. **Die Stufen 9 und
10 liefen nie, und keine Zeile sagte das.** Hinter dem Schnitt standen zwei Befunde, die
zwei Wochen niemand gesehen hat:

* sechs Dateien in `messung/tor-proben/`, deren erzeugtes C nicht übersetzt
  (`'return' with no value, in function returning non-void` — ein leeres `return` in einem
  `can_fail`-Block, den kein Pass liest);
* `MARKE_EMIT_M` stand auf 31, gemessen waren 38 — und `CLAUDE.md` führte den Posten
  ausdrücklich als *„der nächste volle Lauf nennt die richtige als FUND"*.

> *Eine leere Grundgesamtheit ist ein grünes Urteil über nichts (W17). Eine ABGESCHNITTENE
> ist schlimmer: sie sieht aus wie ein Urteil über alles.* Und der Rücklaufwert half nicht —
> `1` las sich als Stufenbefund und war zugleich ein Abbruch für alles dahinter. **Die dritte
> Klasse der Tafel oben kennt „nichts gemessen"; sie kennt „die Hälfte gemessen" nicht.**

**Was die Zahl misst, und was nicht.** Gezählt wird die FLÄCHE: alles hinter dem ersten
Ausgang mit einem Rücklaufwert ungleich null, sofern dahinter noch mindestens einmal
gedruckt wird. Sie sagt **nicht**, dass einer dieser Ausgänge falsch ist — eine Sprechprobe
am Dateianfang SOLL alles dahinter beenden, und das ist ihr Zweck. Sie sagt, wo man
nachsehen muss, und sie ist eine OBERE Schranke. *Sie verpflichtet, sie spricht nicht frei*
(W10).

**Und was daraus folgt, steht als Form und nicht als Zahl da:** wer mitten im Lauf abbricht,
schreibt dazu, was er nicht mehr gemessen hat. `pruefe-emission.sh` hat es an diesem Tag
nicht getan, und der Preis waren zwei Wochen.

### Das Sieb unter der Fläche — 251 sind die Fläche, **92** sind die Gefahr

*Gemessen 2026-08-31 über `283cb26`, abgelesen mit `./instrumente/pruefe-waechter.py`
(Abschnitt „Davon eine TEILMESSUNG"), Sprechprobe in vier Richtungen im selben Lauf.*

Die 251 sind eine **obere Schranke** und sagen das auch. Eine Fläche, die niemand
verkleinern kann, hört auf, gelesen zu werden — also steht darunter ein Sieb mit drei
Schnitten, und jeder nimmt Stellen heraus, die **nicht** die Gefahr sind:

| Schnitt | wie viele fallen | warum sie nicht die Gefahr sind |
|---|---:|---|
| **beendet den Lauf gar nicht** | 3 | ein `return 1` in einem HELFER ist ein *Wert*, den der Aufrufer liest. Kein Ausgang. |
| **endet mit `2`** | 144 | das ist ein ABBRUCH. Der Wächter sagt „nichts gemessen", die Abnahme druckt ihn mit eigenem Wort und eigener Farbe. **Dorthin kommt nur, wer etwas kaputt hat.** |
| **keine Ausgabe auf beiden Seiten** | 12 | ohne Ausgabe davor gibt es keine halbe Messung zu verwechseln; ohne Ausgabe dahinter wurde nichts übersprungen. |

Was übrigbleibt:

```
251  Ausgangsstellen hinter dem jeweils ersten          (die FLAECHE)
248  beenden den Lauf wirklich
104  enden mit 1 -- ERREICHBAR, OHNE DASS ETWAS KAPUTT IST
 92  tragen Ausgabe auf BEIDEN Seiten                   (die GEFAHR)
```

Beim ersten Ablesen waren es **106** und **94**; zwei Stellen sind seither von „Befund" auf
„Abbruch" gewandert (siehe unten), und das ist die richtige Richtung. Gedeckt waren damals
**45** — alle in `pruefe-emission.sh` —, **49 standen offen, in 25 Dateien.**

**Und am Abend desselben Tages: 49 → 19 → 0.**

| Schritt | offen | wodurch |
|---|---:|---|
| gemessen | 49 | — |
| `instrumente/abschnitt.py` | 19 | 19 Python-Wächter, 30 Stellen |
| `instrumente/abschnitt.sh` | 2 | 5 Shell-Wächter, 17 Stellen |
| `zaehle-pflichten.py` **geheilt** | **0** | die zwei brauchten die Form gar nicht |

Die letzten zwei sind der interessante Fall: **zwei gefallene RÜCKWÄRTSPROBEN, die mit `1`
endeten.** Eine gefallene Probe hat *nichts* gemessen — ihr Ausgang ist ein `2`, und dann
fällt sie aus der gefährlichen Menge heraus, ohne dass sie irgendetwas ansagen müsste. Die
sechste Forderung hatte die Vorwärtsrichtung **beim Namen** in ihrer Wortliste
(`SPRECHPROBE GESCHEITERT`) und die Rückwärtsrichtung nie gesehen. *Eine Regel, die die
Wörter aufzählt, die sie schon gesehen hat, misst die Wörter, die sie schon gesehen hat* —
gefunden hat es dieses Sieb, nicht jenes Muster.

Damit stehen **104** erreichbare Ausgänge und **92** gefährliche (zwei sind von „Befund" auf
„Abbruch" gewandert, und das ist die richtige Richtung). `MARKE_TEILMESSUNG` steht auf **0**.

> **Und 0 ist keine Ziellinie.** Eine gedeckte Stelle schneidet den Lauf genauso — *sie sagt
> es nur*, und die Abnahme druckt sie als `TEILMESSUNG` statt als Befund. Gemessen ist, ob
> der Schnitt ANGESAGT wird, nie, ob er richtig ist (W10).

### Die Form: das WO kommt aus der eigenen Ausgabe

    import abschnitt

    def main():
        ...
        abschnitt.fertig()             # ab hier wird nichts mehr gemessen
        return 1 if befunde else 0

    if __name__ == "__main__":
        sys.exit(abschnitt.fahre(main))

`fahre()` legt sich um `sys.stdout` und merkt sich die letzte `== … ==`-Zeile. **Eine Marke
je Stufe wäre ein zweites Register über derselben Sache** (W7) — und sie veraltet lautlos,
genau wie die Liste, die Stufe 9 einmal war. *Jeder Wächter dieses Ordners druckt seine
Abschnitte ohnehin.*

**Die Schale kann das nicht, und darum sagt sie es ausdrücklich.** `abschnitt.sh` bietet
`stufe "…"` statt `echo "== … =="`: eine Schale kann ihre eigene Ausgabe nicht durch ein
`tee` schicken und dabei sicher sein, dass es geleert ist, wenn die `EXIT`-Falle läuft. *Ein
Mechanismus, der manchmal die falsche Stufe meldet, wäre dieselbe Klasse wie das, wogegen er
gebaut ist.* Drei Änderungen je Wächter, keine davon je Stufenrumpf: die Quelle, die Falle
(`trap 'abschnitt_ende; …' EXIT` — und `abschnitt_ende` **zuerst**, weil es `$?` liest), und
`abschnitt_fertig` vor dem letzten, vollständigen Ausgang.

**Gedeckt heißt VERDRAHTET, nicht geladen.** `SAGT_WO` verlangt `abschnitt.fahre(` oder eine
`EXIT`-Falle auf `abschnitt_ende`; ein bloßes `import abschnitt` oder `. abschnitt.sh` zählt
nicht. *Eine Regel, die die Einfuhr zählt, zählt die Absicht.*

> ~~**Und was die Deckungszahl NICHT sagt: sie ist je DATEI gemessen, nicht je Stelle.**~~
> Eine Falle, die auf halber Höhe der Datei scharf wird, deckt die Ausgänge darüber nicht —
> und das Sieb sah es nicht. Nachgesehen wurde deshalb von Hand: `pruefe-syntax.sh` und
> `pruefe-sonden.sh` hatten je einen Ausgang **über** ihrer Falle, und beide sind
> nachgezogen (die Falle steht jetzt unmittelbar hinter der Quelle). ~~*Das ist eine
> gefundene Stelle und keine gemessene Menge — die Klasse bleibt offen.*~~
> **GEMESSEN am 2026-08-31 — siehe den nächsten Abschnitt. Es ist ein Nullbefund, und der
> Suchweg steht daneben.**

#### Die Klasse, gemessen statt gesucht — je STELLE, nicht je Datei

*Gemessen 2026-08-31 über `f08e5ad`, lokal (`free -g`: 31 GB gesamt, 13 GB verfügbar,
20 Kerne). **Kein Bau** — es wird Quelltext gelesen, sonst nichts.*

Die Vorgängerbahn hat zwei Fälle **von Hand** gefunden und ihren eigenen Schlusssatz offen
gelassen. Die Frage dahinter ist schärfer als die zwei Fälle: *wie viele Dateien gelten
heute als gedeckt, obwohl nur EINE ihrer Stellen es ist?* Eine Datei, die als gedeckt gilt,
weil irgendwo in ihr das richtige Wort steht, ist genau die Bauart, gegen die dieser
Abschnitt gebaut wurde — nur eine Ebene höher.

**Was „je Stelle" heißt, und es ist nicht dasselbe in beiden Sprachen:**

| | wann eine Stelle gedeckt ist | warum |
|---|---|---|
| **Schale** | ihre Zeile steht **hinter** der `EXIT`-Falle — oder sie steht in einem Funktionsrumpf | eine Falle wird an ihrer Zeile scharf. Ein `exit` darüber läuft an ihr vorbei. |
| **Python** | sie liegt **lexikalisch in einem `def`** | `fahre()` umschließt den Aufruf von `main`. Was auf Modulebene ausgeführt wird, läuft **vor** `fahre` — der Gegenstandsriegel etwa. |

```
92  gefaehrliche Stellen, in 25 Dateien
92  gedeckt je DATEI    (der Zaehler von gestern abend)
92  gedeckt je STELLE   (die Messung von heute)
 0  Differenz -- und 0 Dateien mit Scheindeckung
```

**Der Nullbefund ist belegt und nicht behauptet** (W25): die Verdrahtungszeile und die
kleinste Ausgangsstelle stehen je Datei nebeneinander, und in **keiner** liegt ein Ausgang
über seiner Falle. Die engsten Abstände sind `pruefe-beweise.sh` (Falle Zeile 21, erster
Ausgang 72) und `pruefe-syntax.sh` (11 / 70) — beide erst am Vorabend nachgezogen, und
genau darum liegt hier eine Null und keine Zwei. *Die Klasse ist nicht leer gewesen; sie ist
geleert worden.*

**Und die schärfere Nachfrage in derselben Messung**: erreicht ein Python-Wächter eine
gefährliche Stelle **außerhalb** von `fahre` — durch einen Aufruf auf Modulebene? Gesucht
wurde über alle Wächter, deren gefährliche Stellen und deren Modulebene vor der
Verdrahtungszeile. **Kein einziger Treffer.**

##### Der Fund, den die Nullzahl nicht zeigt: zwei Dateien sind aus Versehen gedeckt

`SAGT_WO` liest den Dateitext. Zwei Wächter tragen das Wort `ABGESCHNITTEN` in ihrer
**eigenen Beschreibung** und gelten damit als gedeckt, **ohne dass eine Zeile verdrahtet
ist**:

| Datei | warum sie trifft | gefährliche Stellen heute |
|---|---|---|
| `pruefe-waechter.py` | `SAGT_WO` selbst steht in ihr, dazu die Kommentare darüber | **0** |
| `abnahme.py` | druckt die Marke `TEILMESSUNG` und den Text dazu | **0** |

Beide haben heute **keine** gefährliche Stelle, also kostet es heute nichts. *Es ist eine
gelegte Falle und kein Schaden* — und sie liegt ausgerechnet unter den zwei Werkzeugen, die
diese Zahl drucken. **Ein Maßstab, der sich selbst freispricht, tut es lautlos**, und er tut
es an dem Tag, an dem jemand dem einen eine `1` mitten im Lauf hinzufügt. Der Zähler je
Stelle nimmt ihnen die Ausnahme, weil er nach der VERDRAHTUNG fragt und nicht nach dem Wort.

**`fertig()` ist die einzige Zeile, die Urteilskraft braucht**, und sie ist unentbehrlich:
ein Wächter, der an seinem LETZTEN Ausgang mit `1` endet, hat alles gemessen; einer, der am
vorletzten mit `1` endet, nicht. **Von außen sieht beides gleich aus.** `mutiere-pruefer.py`
trägt sie deshalb dreimal — einmal je Betriebsart (`--anker`, `--schnell`, der volle Lauf),
weil jede für sich ein ganzer Lauf ist.

Sprechprobe in fünf Richtungen (`python3 instrumente/abschnitt.py`, und `pruefe-waechter.py`
fährt sie mit, weil kein Sammellauf ein Modul ohne `pruefe-`-Namen erreicht): ein Ausstieg
vor dem Ende **wird** angesagt, ein vollständiger Lauf mit `1` **nicht**, ein grüner ohne
`fertig()` auch nicht, ein Absturz **doch** — und die eigene Ausgabe geht unverändert durch.
Die Schale bekommt zwei eigene Richtungen im selben Lauf, an einem erfundenen Skript.

### Und die Abnahme trennt es vom Befund — die vierte Marke

`abnahme.py` kannte `gruen · ROT · ABBRUCH · NICHT FAHRBAR · ausgelassen`. Am 2026-08-31 kam
**`TEILMESSUNG`** dazu, und sie ist eine eigene MARKE, keine eigene Farbe:

| | |
|---|---|
| `ABBRUCH` | er hat **nichts** gemessen. Er zählt nicht zur Arbeitsmenge. |
| **`TEILMESSUNG`** | er hat **etwas** gemessen, aber nicht alles. Er zählt zur Arbeitsmenge und macht den Lauf rot — **und die Zahl der Befunde daneben ist eine untere Schranke.** |
| `ROT` | er hat **alles** gemessen und etwas gefunden. |

Ohne sie hätte die Abnahme `pruefe-emission.sh`s Tod in Stufe 4 als `ROT` mit der
Zusammenfassung der vierten Stufe gezeigt — *dieselbe Zeile, dieselbe Farbe und dieselbe
Form wie ein Wächter, der zu Ende gemessen hat.* Die Sprechprobe fährt beide Richtungen: ein
abgeschnittener Lauf **muss** als `TEILMESSUNG` erscheinen, **und ein voller Befund muss ein
Befund bleiben** — sonst wäre die Marke eine, die jedes Rot einfärbt.

**Die beiden Zahlen beantworten zwei verschiedene Fragen, und die zweite ist die, die zählt.**
*Erreichbar, ohne dass etwas kaputt ist* sind **104** — ein Befund ist eine Aussage über den
BAUM, und der Baum darf einen Fehler haben; es braucht kein fehlendes Werkzeug und keine
gefallene Probe, um dort hinzukommen. *Eine Teilmessung, die wie eine ganze aussieht*, sind
**92** — und das ist die gefährliche Menge, weil vor der Stelle eine halbe Messung auf dem
Schirm steht und dahinter das, was nie lief.

> **Der Rücklaufwert kann es nicht sagen, und das ist der ganze Punkt.** `2` heißt „nichts
> gemessen" und wird gedruckt. `1` heißt „gemessen, es steht etwas offen" — und ein `1`
> mitten im Lauf heißt beides zugleich: *ein Befund hier, ein Abbruch für alles dahinter.*
> **Die drei Klassen der Tafel oben kennen „die Hälfte gemessen" nicht.**

Und die Deckung ist keine Heilung: eine gedeckte Stelle bricht genauso mitten im Lauf ab —
sie **sagt es nur**. `MARKE_TEILMESSUNG` in `pruefe-waechter.py` steht auf 0 und darf nur
fallen.

### Die Gegenzahl: wie oft wird heute WIRKLICH abgeschnitten?

*Gemessen 2026-08-31 mit `./instrumente/abnahme.py`, lokal (`free -g`: 31 GB gesamt, 13 GB
verfügbar, 20 Kerne).*

`MARKE_TEILMESSUNG = 0` zählt **Stellen, die es nicht ansagen würden**. Sie sagt nichts
darüber, wie oft ein Lauf tatsächlich mitten drin endet — das ist die andere Zahl, und die
Abnahme trägt sie in ihrer Kopfzeile:

```
== Arbeitsmenge: 45 von 49 Waechtern haben GEMESSEN -- 44 gruen, 1 ROT, 0 TEILMESSUNG ==
   0 ABBRUCH, 1 nicht fahrbar, 3 ausgelassen
```

**Null — und der Nenner ist 45 und nicht 49** (W25). Der schlichte Lauf lässt drei teure aus,
und **darunter ist ausgerechnet `pruefe-emission.sh`, der allein 45 der 92 gefährlichen
Stellen trägt.** Eine Null, die den halben Gegenstand nicht angesehen hat, ist genau die
Bauart, gegen die dieser Abschnitt steht — also ist sie hier nicht stehen geblieben:

| Wächter | wie gemessen | abgeschnitten? |
|---|---|---|
| 45 aus der Abnahme | `abnahme.py`, ein Lauf | **0** |
| `pruefe-emission.sh` | einzeln gefahren, `rc=0`, kein `ABGESCHNITTEN` in 282 Zeilen | **nein** |
| `pruefe-beweise.sh` | einzeln nachgefahren | **nein** |
| `pruefe-luecken.py` | einzeln nachgefahren: `ALL PASS`, *alle Quellen byteidentisch zurück* | **nein** |
| `zaehle-b3.py` | `NICHT FAHRBAR` im Arbeitsbaum; gegen `/home/simon/Dokumente/caprock-messbasis` **gefahren, `rc=0`** | **nein** |

**Also: 49 von 49 gemessen, null davon abgeschnitten** — ~~48 von 49~~, denn der eine
Rest ist am selben Abend gegen den Pfad nachgefahren worden, an dem seine Messbasis
wirklich liegt. Im Arbeitsbaum bleibt er `NICHT FAHRBAR`, und das ist eine Aussage über
den Arbeitsbaum. Das ist keine Zusage für morgen — es ist der Stand von heute abend.

**Die Zahl steht in der Kopfzeile, auch wenn sie null ist.** Das ist kein Schmuck: eine
gedruckte Null sagt, dass gemessen wurde; eine fehlende Zahl sagt gar nichts (W17). Ist sie
nicht null, kommt ein eigener Block dazu, der jeden abgeschnittenen Wächter mit seinem
Rücklaufwert und seiner STELLE nennt.

**Und dass sie erscheint, ist selbst unter einer Sprechprobe**, die bei jeder Abnahme
mitläuft: `abnahme.py:sprechprobe()` legt fünf erfundene Wächter an, darunter `pruefe-halb.sh`
(zwei Zeilen Ausgabe, dann `ABGESCHNITTEN in: Stufe 4`, dann `exit 1`) und `pruefe-rot.sh`
(ein voller Befund). Geprüft wird in **beide** Richtungen: der abgeschnittene **muss**
`TEILMESSUNG` heißen und seine STELLE nennen, der volle Befund **muss** `ROT` bleiben — und
die Arbeitsmenge muss `3` sein, was die Teilmessung mitzählt. *Eine Marke, die jedes Rot
einfärbt, bestünde die erste Richtung und fiele an der zweiten.*

> **Die zwei Zahlen messen Verschiedenes, und beide werden gebraucht.** Die Ratsche zählt
> Stellen, die schweigen *würden*; die Kopfzeile zählt Läufe, die heute schweigen *müssten*
> und es nicht tun. *Die erste darf nur fallen. Die zweite darf steigen* — sie ist eine
> Aussage über den BAUM und keine über die Messapparatur.

#### Und die zwei, die die Zahl drucken, standen selbst außerhalb der Form

`pruefe-waechter.py` und `abnahme.py` liefen bis zum 2026-08-31 abends mit
`sys.exit(main())`. Beide haben null gefährliche Stellen, also fielen sie aus der Ratsche
heraus — *und das ist ein Grund, vom BEFUND ausgenommen zu sein, nie von der FORM.* Ein
Absturz auf halber Höhe hätte bei `abnahme.py` zwanzig Zeilen auf dem Schirm gelassen und
keine Zeile darüber, dass neunundzwanzig Wächter nie gefragt wurden: **eine halbe Abnahme,
die wie eine ganze aussieht** — genau die Gestalt, für die die Marke da ist. Beide sind
jetzt verdrahtet, mit `fertig()` vor der Urteilskette; die rote Abnahme von heute bleibt ein
Befund und wird **nicht** als abgeschnitten gemeldet.

##### Der Fund dabei: die Sprechprobe war nicht wiedereintrittsfest

Kaum war `pruefe-waechter.py` verdrahtet, **fiel `abschnitt.py`s erste Richtung** — die,
die es überhaupt gibt. Nicht weil die Meldung kaputt war: `pruefe-waechter.py` fährt
`abschnitt.sprechprobe()` mit, und die läuft nun *innerhalb* eines `fahre()`. Damit stand
`_AN` schon auf `True`, das geschachtelte `fahre` legte sich nicht um seinen Puffer, und
`_MARKE` wurde nie gelernt. Der Lauf endete mit `2` und dieser Zeile:

```
== ABGESCHNITTEN in: ABGESCHNITTEN in: Stufe 2: der Kopf -- Ruecklaufwert 1 -- Ruecklaufwert 2 ==
```

*Eine Probe, die von dem Lauf zerstört wird, in dem sie steckt, misst diesen Lauf und nicht
ihren Gegenstand* — dieselbe Klasse wie das `pgrep -f`, das sich selbst findet. Geheilt,
indem `sprechprobe()` die drei Modulgrößen sichert, `_AN` zurücksetzt und alles hinterher
zurücklegt. **Und sie ist nicht durch Nachdenken gefunden worden, sondern dadurch, dass
jemand die Form auf ihren eigenen Träger angewandt hat.**


## Was die Auslassung KOSTET — der Schnelllauf sieht 45 von 92, nicht 45 von 49

*Gemessen 2026-08-31 abends, lokal (`free -g`: 31 GB gesamt, 13 GB verfügbar, 20 Kerne).
Kein Bau: die vier teuren wurden **nicht** gefahren, ihr Gegenstand ist aus ihrem eigenen
Quelltext und aus dem letzten protokollierten Auslauf gezählt.*

Die Kopfzeile des Schnelllaufs sagt heute:

```
== Arbeitsmenge: 45 von 49 Waechtern haben GEMESSEN -- 44 gruen, 1 ROT, 0 TEILMESSUNG ==
   0 ABBRUCH, 1 nicht fahrbar, 3 ausgelassen
```

**45 von 49 ist eine richtige Zahl über dem falschen Gegenstand.** Sie zählt Wächter. Wer sie
liest, liest ein Urteil über den Baum — und der Baum ist nicht in Wächtern gemessen, sondern
in dem, was sie ansehen. Also ist das nachgezählt worden, in zwei Einheiten.

### Erstens: in der Einheit, die dieser Ordner ohnehin führt — die gefährlichen Stellen

`pruefe-waechter.py:teilmessungen()` zählt sie schon, je Datei: **92 Stellen, an denen ein
Lauf mit `1` aussteigt und dahinter noch Ausgabe stünde.** Dieselbe Zahl, dieselbe Messung,
nur je Wächter aufgeteilt statt aufsummiert:

| | gefährliche Stellen | im Schnelllauf besucht? |
|---|---:|---|
| `pruefe-emission.sh` | **45** | nein — ausgelassen |
| `mutiere-pruefer.py` | 5 | nur die `--anker`-Hälfte |
| `pruefe-beweise.sh` | 2 | nein — ausgelassen |
| `pruefe-luecken.py` | 0 | nein — ausgelassen |
| die übrigen 45 Wächter | 40 | ja |
| **zusammen** | **92** | |

**47 der 92 stehen in Wächtern, die der Schnelllauf gar nicht erst startet** — mehr als die
Hälfte, und 45 davon in einem einzigen. Großzügig gerechnet (die fünf Stellen des
Ankerlaufs mitgezählt, obwohl der Mutationslauf selbst nicht läuft) sieht der Schnelllauf
**45 von 92**.

> *Zwei Zahlen, beide 45, und sie messen Verschiedenes:* **45 von 49 Wächtern — 49 %** *von
> 92 gefährlichen Stellen. Die erste steht in der Kopfzeile, die zweite stand nirgends* (W25:
> eine Zahl belegt ihren Nenner, nicht ihre Beschriftung).

### Zweitens: in der Einheit jedes einzelnen Wächters

| ausgelassen | sein Gegenstand | der Schnelllauf sieht davon |
|---|---|---|
| `pruefe-emission.sh` | zehn Stufen, 25 Durchstiche, **101 von 101** Übersetzungseinheiten in Stufe 9, dazu Stufe 10 (Bibliothekskette) | **nichts** |
| `mutiere-pruefer.py` | **372** Mutationen, je ein `cargo build` und ein `cargo test` | **372 Anker textlich**, null Mutationen gefahren |
| `pruefe-luecken.py` | **15** Verdrehungen (13 mit eigenem Bau, 2 bewiesene Nullmutationen) und ein Nullauf | **nichts** |
| `pruefe-beweise.sh` | **15** Isabelle-Theorien (`beweise/ROOT`) | **nichts** |

**503 Messposten stehen hinter der Auslassung** — 101 Übersetzungseinheiten, 372 Mutationen,
15 Verdrehungen, 15 Theorien. *Die Summe hat keinen eigenen Nenner:* es gibt keine gezählte
Gesamtmenge, gegen die sich „503" als Anteil lesen ließe, und darum steht sie hier mit ihren
vier Summanden daneben und nie allein. Die Zahl mit einem Nenner ist die andere: **45 von
92.**

### Und die Gegenprobe: wie oft war der VOLLE Lauf heute überhaupt grün?

Nicht geschätzt, sondern in `git log` gesucht (2026-08-31, 00:00 bis 18:51; einige Belege
können denselben Lauf meinen):

| Zeit | Besetzung | Ergebnis |
|---|---:|---|
| 01:10 (`bc3812d`) | 27 | **grün** (auf `fisch`) |
| 01:33 (`23bee0e`) | 27 | rot — `pruefe-beweise.sh [1]` |
| 01:55 (`e33eedd`) | 28 | rot — 27 grün, 1 ROT |
| 02:03 (`2755721`) | 27 | Fund über die **Messapparatur**, nicht über den Baum |
| 02:20 (`531b2e6`) | 27 | **grün** (`EXIT=0`) |
| 02:52 (`cd2c8db`) | 27 | **grün** — mit allen vier teuren |
| 06:11 (`22d56a1`) | 28 | rot — 25 gemessen, 24 grün, 1 ROT |
| 07:14 (`0ae9bea`) | 46 | **ungefahren** — der Mutationslauf hätte kollidiert |
| 17:34 (`1264dad`) | 49 | rot — `TEILMESSUNG pruefe-emission.sh`, Stufe 9 |

**Der letzte grüne volle Lauf war um 02:52 und ging über 27 Wächter.** Seither ist die
Besetzung auf 49 gewachsen, und **über der heutigen Besetzung war der volle Lauf noch nie
grün** — genau einmal gefahren (17:34), und da endete er in einer Teilmessung.

> *Die Auslassung ist also keine Abkürzung eines Laufs, den man sonst hätte:* der volle Lauf
> über die heutige Besetzung existiert als **ein** Datenpunkt. Was der Schnelllauf nicht
> sieht, sieht heute niemand — und die Kopfzeile sagte es nicht.


### Die Heilung: die Schlusszeile nennt jetzt ihren Gegenstand

*2026-08-31 abends. `pruefe-waechter.py:GEGENSTAND` (neu) und `abnahme.py:gegenstand()`.*

Die Kopfzeile hat eine zweite bekommen, und die zweite hat den anderen Nenner:

```
== Arbeitsmenge: 45 von 49 Waechtern haben GEMESSEN -- 44 gruen, 1 ROT, 0 TEILMESSUNG ==
   0 ABBRUCH, 1 nicht fahrbar, 3 ausgelassen
== Und ihr GEGENSTAND: hoechstens 45 von 92 gefaehrlichen Stellen besucht -- 49 % ==
   47 davon stehen in Waechtern, die dieser Lauf nicht gefahren hat -- und was
   mit ihnen ungemessen bleibt:
     pruefe-emission.sh    45 Stellen   101 von 101 Uebersetzungseinheiten in Stufe 9, …
     pruefe-beweise.sh      2 Stellen   15 Isabelle-Theorien (`beweise/ROOT`)
     pruefe-luecken.py      0 Stellen   15 Verdrehungen, 13 davon mit eigenem Bau
     zaehle-b3.py           0 Stellen   105 Dateien / 2536 Ruempfe der Caprock-Messbasis
```

**Drei Entscheidungen darin, und jede hat einen Grund:**

1. **Die Einheit ist die, die dieser Ordner ohnehin führt.** `gegenstand()` ruft
   `pruefe-waechter.teilmessungen()` — dieselbe Funktion, derselbe Code, nur je Wächter
   statt aufsummiert. *Kein zweites Register über derselben Sache* (W7): ein Wächter, der
   eine gefährliche Stelle dazubekommt, bekommt sie in beiden Zahlen zugleich.
2. **`höchstens`, und das Wort steht in der Zeile.** Ein halb gefahrener Wächter
   (`mutiere-pruefer.py --anker`) und eine `TEILMESSUNG` zählen hier als *gesehen*, obwohl
   beide nur einen Teil ihrer Stellen erreicht haben. Die Schranke irrt damit **nach oben** —
   die Richtung, in der eine Schranke irren darf.
3. **Was keine Stellen trägt, wird trotzdem genannt.** `zaehle-b3.py` hat **null**
   gefährliche Stellen und 105 fremde Dateien als Gegenstand: in der Einheit, in der der
   Bruch gerechnet wird, kostet sein Fehlen *nichts*. Er stünde nirgends. Also läuft neben
   dem Bruch eine zweite Liste — jeder nicht gemessene Wächter mit einem Eintrag in
   `GEGENSTAND` wird gedruckt, mit `0 Stellen` und seinem Gegenstand daneben. *Wer nur den
   Bruch druckt, verliert genau den Wächter, dessen Ausfall im Bruch keinen Ort hat.*

**Und die Gegenrichtung, weil ein Schnelllauf, der nie mehr grün aussieht, keine Hilfe ist:**
das Wort bleibt `GRUEN` und der Rücklaufwert bleibt `0`. Was sich ändert, ist die Zeile:

```
  ABNAHME GRUEN MIT BENANNTER LUECKE: 45 von 49 Waechtern,
  und hoechstens 45 von 92 gefaehrlichen Stellen -- 49 %. **Gruen heisst hier:
  was gefahren wurde, ist sauber** -- nicht, dass der Baum es ist.
```

Ein voller Lauf ohne Lücke bekommt die andere Hälfte: *„und 92 von 92 gefährlichen Stellen.
**Kein Wort davon ist ausgelassen.**"* — **Grün mit benannter Lücke und Grün sind zwei
Sätze, und man sieht ihnen den Unterschied an.**

#### Die Sprechprobe dazu — drei Richtungen, und auf ihrem EIGENEN Träger

`abnahme.py:sprechprobe()` legt für den Gegenstandszähler ein **eigenes** Wegwerfverzeichnis
an, nicht das der anderen zwölf Proben. Der Grund ist der Fund vom selben Abend: die
bestehenden Proben behaupten `len(erg) == 5`, und ein sechster erfundener Wächter hätte sie
umgeworfen. *Eine Probe, die den Lauf verändert, in dem sie steckt, misst diesen Lauf und
nicht ihren Gegenstand.*

| Richtung | erfundener Fall | verlangt |
|---|---|---|
| gezählt wird der Gegenstand | `pruefe-tief.sh` (2 gefährliche Stellen), `pruefe-flach.sh` (0), beide gefahren | `2 von 2`, keine Lücke |
| eine Auslassung nimmt ihren Gegenstand MIT | `pruefe-tief.sh` ausgelassen | `0 von 2`, und er wird benannt |
| eine Auslassung OHNE Gegenstand öffnet KEINE | `pruefe-flach.sh` ausgelassen | `2 von 2`, keine Lücke |

Die dritte ist die, die die Zahl ehrlich hält: *eine Lückenmeldung, die bei jeder Auslassung
anschlägt, misst die Auslassung und nicht den Gegenstand* — und dann liest sich jeder
Schnelllauf als blind, was so falsch ist wie die alte Null. **Sechzehn Proben laufen jetzt
vor jeder Abnahme, dreizehn alte und drei neue.**

### `zaehle-b3.py`: richtig eingeordnet — und „48 von 49" gilt nur im ARBEITSBAUM

*Gemessen 2026-08-31 abends.* Drei Fragen, drei Antworten:

* **Steht er sauber in `FREMDER_KORPUS`?** Ja. Der Eintrag nennt Pfad und Gegenstand, sein
  Kommentar nennt sogar den Sonderfall: *„`../caprock-messbasis` ist zusätzlich relativ: in
  einem `git worktree` zeigt der Pfad neben den Arbeitsbaum statt neben die
  Hauptauscheckung."* Er wird **nicht grün gebucht**, sondern als nicht gemessen gezählt.
* **Erscheint seine Zahl in der Schlusszeile?** Jetzt ja — vorher nur als `1 nicht fahrbar`,
  ohne dass irgendwo stand, was damit ungemessen bleibt. Er ist der Grund für die zweite
  Liste oben.
* **Und stimmt der Grund?** *Nur zur Hälfte.* Die Messbasis liegt da:
  `/home/simon/Dokumente/caprock-messbasis` **existiert**. Gefahren gegen genau diesen Pfad,
  aus diesem Arbeitsbaum heraus:

```
  ./instrumente/zaehle-b3.py /home/simon/Dokumente/caprock-messbasis   ->  rc=0
  Dateien 105 | Ruempfe 2536 | mit Schleife 462 | Abbrueche 0
  BUCHSTABE (Na+Nb1) 12 Ruempfe · BERICHTET (+Nb2) 26 Ruempfe · 0,953 %
```

> **`48 von 49` ist damit eine Aussage über den ARBEITSBAUM, nicht über den Baum.** Auf der
> Hauptauscheckung löst `../caprock-messbasis` richtig auf, und die Abnahme fährt **49 von
> 49**. Ein Wächter, dessen Urteil davon abhängt, aus welcher Auscheckung er läuft, ist
> dieselbe Klasse wie einer, dessen Urteil am Rechner hängt — nur eine Ebene kleiner.

**Gebucht, nicht geheilt**, und mit dem Grund: die Heilung heißt, den Pfad gegen die
*Hauptauscheckung* aufzulösen (`git rev-parse --git-common-dir`), und damit läse `korpus_fehlt`
`git` — was den Riegel aus derselben Datei verlangt (*„wer `git` liest, liest den
Rücklaufwert"*). Das ist ein eigener Posten und keine Nebenbei-Zeile.


## Der Wächter, dessen Urteil am RECHNER hing — und seine zwei Geschwister

*Gemessen und geheilt 2026-08-31. Der Fall stand seit heute früh gefunden, aber ungeheilt da.*

`mutiere-pruefer.py --anker` war **hier grün und auf `ki-pc-fisch-101` rot**, bei
byteidentischen Quellen. Nicht der Baum war verschieden, sondern sein Zustand als
*Gegenstand*: der übertragene Baum ist **kein git-Repository**, `git status` endet dort mit
**128 und leerer Ausgabe**, `baumstand()` meldet zu Recht `unbekannt` — und die Sprechprobe
verlangte vom eigenen Baum `sauber` oder `schmutzig`. Sie fiel:

```
SPRECHPROBE GESCHEITERT: der eigene Baum meldet `unbekannt`
```

**Der Satz war falsch.** Das Werkzeug war in Ordnung; der Gegenstand fehlte. Und
„Sprechprobe gescheitert" heißt in diesem Ordner *dieses Werkzeug misst nicht, was es
behauptet* — die schärfste Aussage, die ein Lauf über sich selbst machen kann.

> *Ein Wächter, dessen Urteil davon abhängt, auf welchem Rechner er läuft, ohne es zu sagen,
> misst den Rechner.* Der Ordner hat diese Klasse einmal bezahlt (`pruefe-waechter.py --lauf`,
> grün hier und rot dort, weil zwei Zähler fremde Bäume lasen — sie stehen seither in
> `FREMDER_KORPUS`).

**Die Form ist dieselbe, eine Ebene tiefer — nur trägt sie diesmal ihren Gegenstand mit.**
Ein fremder Baum ließ sich nicht mitbringen, ein git-Repository schon: `git init`, eine
Datei, ein Commit. Damit sind **alle drei Zustände in der eigenen Wegwerf-Ablage erreichbar**,
auf jedem Rechner, und der umgebende Baum trägt nichts mehr zum Urteil bei — er steht als
Angabe daneben.

| Richtung | vorher | jetzt |
|---|---|---|
| echtes Repository | ok | ok |
| `rsync`-Kopie ohne `.git` | **SPRECHPROBE GESCHEITERT**, `2` | ok; `Baum HIER: unbekannt` als Angabe |
| gar kein `git` | Traceback aus `FileNotFoundError`, `1` *(am Quelltext abgelesen, nicht gefahren)* | `ABBRUCH: der Baumstand ist NICHT GEMESSEN`, `2` *(gefahren mit leerem `PATH`)* |

Die dritte Zeile ist die, auf die es ankommt: **ohne `git` fallen alle drei Zustände auf
`unbekannt` zusammen**, und eine Probe mit einem einzigen erreichbaren Ausgang misst nichts.
Das ist keine gefallene Probe, sondern eine fehlende Vorbedingung — *„nicht gemessen" statt
„gefallen", `2` und nicht `1`.*

### Die Familie — `grep` über `instrumente/`, und die zweite war die schlimmere

Drei Werkzeuge stellten dieselbe Frage, jedes in seiner eigenen Kopie:

| Werkzeug | ohne Repository | was das heißt |
|---|---|---|
| `mutiere-pruefer.py` | Sprechprobe fiel | ein funktionierendes Werkzeug nennt sich kaputt |
| **`pruefe-luecken.py`** | las **nur `stdout`** — leer heißt *sauber* — und **schrieb dann in Quellen** | *nachgemessen: `returncode 128`, `stdout ''`, der Riegel griff NICHT* |
| `erzeuge-mutationen.py` | `git diff --quiet` gibt 128, gelesen als *„crates/ ist nicht sauber"* | ein falscher Grund schickt den Leser einen sauberen Baum reparieren |

**`pruefe-luecken.py` ist der teure Fund.** Er steht in `pruefe-waechter.py:SCHWER` mit dem
Grund *„baut dreizehnmal neu — gehört auf den Server"* — also lief der eine Riegel, der ihn
davon abhält, eine Mischung zu messen, **genau auf dem Rechner leer, für den er geschrieben
wurde.** Ein Lauf, der auf halbem Weg stirbt, lässt eine verdrehte Quelle stehen. Dieselbe
Klasse wie `W16`, und dieselbe wie die `rsync -a`-Falle in `CLAUDE.md`.

`erzeuge-mutationen.py` steht **in keinem Sammellauf** — die Besetzung von `abnahme.py` liest
`pruefe-*`, `mutiere-*` und `zaehle-*`. Ein Werkzeug, das in Quellen schreibt und das niemand
fährt. *Genannt, nicht verschoben* — die Grenze gehört dem Ordner.

**Geheilt mit einem Register statt mit drei Kopien** (W7): die drei Zustände stehen in
`mutiere-pruefer.py:baumstand()` und werden von dort **gelesen**, wie `abnahme.py` die
Register aus `pruefe-waechter.py` liest. Gegen die vierte Kopie steht eine statische Prüfung
in `pruefe-waechter.py` mit Sprechprobe in drei Richtungen: **wer `git` selbst aufruft, sieht
auf den Rücklaufwert** — *eine leere Ausgabe aus einem Befehl, der GESCHEITERT ist, ist keine
Antwort.* Heute: 1 von 50 Werkzeugen ruft `git`, 0 ohne Riegel.

## Was diese Tafel NICHT sagt

Sie liest den **Quelltext** und einen Lauf über einem leeren Baum. Ein Wächter, dessen
Vorbedingung erst mitten im Lauf wegbricht — ein Werkzeug, das nach der Sprechprobe stirbt,
eine Datei, die zwischen zwei Schritten verschwindet —, ist hier nicht erfasst. **Der leere
Baum ist die billigste Absage, nicht die einzige.** Und ein `2` an der richtigen Stelle sagt
nur, dass der Wächter seine Absage BENENNT; ob er sie an der richtigen Stelle bemerkt,
sagt es nicht (W10).
