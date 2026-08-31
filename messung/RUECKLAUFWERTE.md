# Die Rücklaufwerte der ~~28~~ **46** Wächter — was jeder Wert BEDEUTET

*Gemessen 2026-08-31. Grundlage: der Quelltext jedes Wächters und ein Lauf jedes Wächters
über einem **leeren Baum** (`instrumente/` kopiert, sonst nichts) — die Messung, die
„leere Grundgesamtheit" von „nichts gefunden" trennt.*

> **Die Tafel unten führt 28, die Abnahme fährt 46** *(2026-08-31)*. An diesem Tag sind die
> 18 `zaehle-*` dazugekommen; ihre eigene Tafel steht unter *Die achtzehn Zähler*. Die
> Nummerierung der großen Tafel bleibt bei 28, weil sie den Stand beschreibt, an dem diese
> Messung angefangen hat.

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

Sie gilt seit dem 2026-08-31 für **alle 47**: die `zaehle-*` sind in die Abnahme
aufgenommen, und `ABBRUCH_GEBUCHT` steht leer.

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
* **Die 180 unbewachten Zellen sind jetzt ehrlich gezählt und damit größer geworden.** 41
  davon tragend, 37 mit geschriebenem Grund, **4 offen** — das ist die Arbeitsliste.
* ~~**Der leere Baum ist die billigste Absage, nicht die einzige.** Ein Wächter, dessen
  Vorbedingung erst MITTEN im Lauf wegbricht, ist hier weiter nicht erfasst.~~
  **GEMESSEN am 2026-08-31, und zwar an einem Fall mit Datum.** Siehe den eigenen Abschnitt
  *Der Schnitt mitten im Lauf* darunter: **43 von 49** Wächtern können mitten im Lauf
  abbrechen, **249 Ausgangsstellen** liegen hinter dem jeweils ersten. Abgelesen mit
  `./instrumente/pruefe-waechter.py`, nachgerechnet von `pruefe-zahlen.py`.
* **`OHNE_URTEIL` steht leer, und das ist eine Zusage an die Zukunft, keine Messung über
  sie.** Wer einen Zähler wieder herausnimmt, schreibt den Grund dazu — die Zahl der
  Ausgenommenen druckt die Abnahme.

## Der Schnitt mitten im Lauf — der Posten, den der leere Baum offen lässt

*Gemessen 2026-08-31 mit `./instrumente/pruefe-waechter.py` (Abschnitt „Ein Abbruch MITTEN
im Lauf"), Sprechprobe in beide Richtungen im selben Lauf.*

```
43 von 49 Wächtern können mitten im Lauf abbrechen
249 Ausgangsstellen liegen hinter dem jeweils ersten
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

### Das Sieb unter der Fläche — 249 sind die Fläche, **94** sind die Gefahr

*Gemessen 2026-08-31 über `283cb26`, abgelesen mit `./instrumente/pruefe-waechter.py`
(Abschnitt „Davon eine TEILMESSUNG"), Sprechprobe in vier Richtungen im selben Lauf.*

Die 249 sind eine **obere Schranke** und sagen das auch. Eine Fläche, die niemand
verkleinern kann, hört auf, gelesen zu werden — also steht darunter ein Sieb mit drei
Schnitten, und jeder nimmt Stellen heraus, die **nicht** die Gefahr sind:

| Schnitt | wie viele fallen | warum sie nicht die Gefahr sind |
|---|---:|---|
| **beendet den Lauf gar nicht** | 3 | ein `return 1` in einem HELFER ist ein *Wert*, den der Aufrufer liest. Kein Ausgang. |
| **endet mit `2`** | 140 | das ist ein ABBRUCH. Der Wächter sagt „nichts gemessen", die Abnahme druckt ihn mit eigenem Wort und eigener Farbe. **Dorthin kommt nur, wer etwas kaputt hat.** |
| **keine Ausgabe auf beiden Seiten** | 12 | ohne Ausgabe davor gibt es keine halbe Messung zu verwechseln; ohne Ausgabe dahinter wurde nichts übersprungen. |

Was übrigbleibt:

```
249  Ausgangsstellen hinter dem jeweils ersten          (die FLAECHE)
246  beenden den Lauf wirklich
106  enden mit 1 -- ERREICHBAR, OHNE DASS ETWAS KAPUTT IST
 94  tragen Ausgabe auf BEIDEN Seiten                   (die GEFAHR)
 45  davon in `pruefe-emission.sh`, das seit heute `ABGESCHNITTEN in:` druckt
 49  bleiben offen, in 25 Dateien                       (die ARBEITSLISTE)
```

**Die beiden Zahlen beantworten zwei verschiedene Fragen, und die zweite ist die, die zählt.**
*Erreichbar, ohne dass etwas kaputt ist* sind **106** — ein Befund ist eine Aussage über den
BAUM, und der Baum darf einen Fehler haben; es braucht kein fehlendes Werkzeug und keine
gefallene Probe, um dort hinzukommen. *Eine Teilmessung, die wie eine ganze aussieht*, sind
**94** — und das ist die gefährliche Menge, weil vor der Stelle eine halbe Messung auf dem
Schirm steht und dahinter das, was nie lief.

> **Der Rücklaufwert kann es nicht sagen, und das ist der ganze Punkt.** `2` heißt „nichts
> gemessen" und wird gedruckt. `1` heißt „gemessen, es steht etwas offen" — und ein `1`
> mitten im Lauf heißt beides zugleich: *ein Befund hier, ein Abbruch für alles dahinter.*
> **Die drei Klassen der Tafel oben kennen „die Hälfte gemessen" nicht.**

Und die Deckung ist keine Heilung: eine gedeckte Stelle bricht genauso mitten im Lauf ab —
sie **sagt es nur**. `MARKE_TEILMESSUNG` in `pruefe-waechter.py` steht auf 49 und darf nur
fallen.

## Was diese Tafel NICHT sagt

Sie liest den **Quelltext** und einen Lauf über einem leeren Baum. Ein Wächter, dessen
Vorbedingung erst mitten im Lauf wegbricht — ein Werkzeug, das nach der Sprechprobe stirbt,
eine Datei, die zwischen zwei Schritten verschwindet —, ist hier nicht erfasst. **Der leere
Baum ist die billigste Absage, nicht die einzige.** Und ein `2` an der richtigen Stelle sagt
nur, dass der Wächter seine Absage BENENNT; ob er sie an der richtigen Stelle bemerkt,
sagt es nicht (W10).
