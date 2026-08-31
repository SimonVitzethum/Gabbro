# Die Rücklaufwerte der 28 Wächter — was jeder Wert BEDEUTET

*Gemessen 2026-08-31. Grundlage: der Quelltext jedes Wächters und ein Lauf jedes Wächters
über einem **leeren Baum** (`instrumente/` kopiert, sonst nichts) — die Messung, die
„leere Grundgesamtheit" von „nichts gefunden" trennt.*

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
| 1 | `mutiere-pruefer.py` | sauber | tote Anker, unbekannte Fläche | `crates/` schmutzig, **4 Sprechproben** | 1 → 1¹ | Sprechprobe → 1 |
| 2 | `pruefe-abstieg.py` | sauber/gebucht | neue Lücke, veraltete Buchung | **6 Sprechproben, `lib.rs::unterbloecke` fehlt** | 1 → 1¹ | **kein `2`** |
| 3 | `pruefe-aufloesung.py` | sauber | Ratsche | Sprechprobe | 1 → 1¹ | — |
| 4 | `pruefe-beweise.sh` | ALL PASS | Fehler, **`ROOT`-Lücke** | **Isabelle fehlt · Sprechprobe · Wachhund · OHNE NACHWEIS · keine `.thy`** | 1 → **2** | **kein `2`** |
| 5 | `pruefe-emission.sh` | ALL PASS | ~50 Stufenbefunde | **kein `cargo`/`cc` · 10 Sprechproben** | 1 → **2** | **kein `2`** |
| 6 | `pruefe-englisch.py` | ALL PASS | Ratschen | drei Sprechproben, **leere Quellenmenge** | **0 → 2** | **leer → grün** |
| 7 | `pruefe-grammatiktafel.py` | 0 ungedeckt | ungedeckte Zellen | Sprechprobe, **„KEIN LAUF"** | 1 → 1¹ | Abbruch → 1 |
| 8 | `pruefe-gruende.py` | sauber | — | **Sprechprobe · null Absagetexte** | **0 → 2** | **leer → grün**, Sprechprobe → 1 |
| 9 | `pruefe-kennungen.py` | ALL PASS | Doppelbelegung | **Sprechprobe · null Kennungen** | **0 → 2** | **leer → grün** |
| 10 | `pruefe-klauseln.py` | keine neue | neue Fundstelle | **Selbsttest** | 1 → **2** | Abbruch → 1 |
| 11 | `pruefe-konstrukte.py` | keine neue | neue ohne Probe | **Sprechprobe (enthält den Leertest)** | 1 → 1¹ | Abbruch → 1 |
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
| 22 | `pruefe-todo.py` | ALL PASS | Befunde | **Sprechprobe** | 1 → 1¹ | Sprechprobe → 1 |
| 23 | `pruefe-vergabe.py` | Ratsche hält | Ratsche | **Sprechprobe** | 1 → **2** | Sprechprobe → 1 |
| 24 | `pruefe-waechter.py` | keine Verletzung | Verletzungen | **Sprechprobe** | 0 → 0² | Sprechprobe → 1 |
| 25 | `pruefe-widerruf.py` | ALL PASS | lebende Vorkommen | Eintrag · Sprechprobe · **Gegenstand fehlt** | 1 → **2** | **VORBILD**, bis auf den Absturz |
| 26 | `pruefe-wortschatz.py` | deckt | fehlt/tot/unerreichbar | **Sprechprobe · leere Tabelle/EBNF** | 1 → 1¹ | **kein `2`**; leer → grün |
| 27 | `pruefe-zahlen.py` | keine Abweichung | Abweichung, Selbstbezug, **4 Sprechproben**, **„0 von 0"** | — | 1 → 1 | **GEBUCHT — fremde Bahn** |
| 28 | `pruefe-zitate.py` | Ratsche hält | Ratsche | Sprechprobe, **2 ABORT-Zweige** | 1 → **2** | Abbruch → 1 |

¹ Der leere Baum trifft diese sieben in einem `FileNotFoundError`, bevor irgendein Riegel
greift: Python beendet mit `1`. **`abnahme.py` liest den Traceback und bucht `ABBRUCH`**;
alleingefahren ist der Rücklaufwert weiter `1`. Siehe *Was offen bleibt*.

² `pruefe-waechter.py` liest `instrumente/pruefe-*` und findet sich dabei immer selbst —
seine Grundgesamtheit kann nicht leer werden. Die `0` ist kein Fehlurteil.

**Über dem leeren Baum standen vorher 3 benannte Absagen mit `2`, heute 18.**

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

| | |
|---|---|
| über dem Stand vor Posten 3 (`99e2145`) | **44 Stellen in 15 Dateien** |
| heute | **0**, plus 1 gebucht |
| über den 18 `zaehle-*` (außerhalb) | **40 Stellen** — gedruckt, damit jemand die Grenze verschieben kann |

Sie gilt für die 29, deren Rücklaufwert `abnahme.py` als URTEIL liest. Die `zaehle-*` stehen
außerhalb, weil dieser Rücklaufwert dort niemanden interessiert — *sie messen, sie bewachen
nicht*.

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

## Was offen bleibt

* **Sieben Wächter sterben an einem `FileNotFoundError`, bevor ein Riegel greift** —
  `pruefe-abstieg.py`, `-aufloesung.py`, `-grammatiktafel.py`, `-konstrukte.py`, `-todo.py`,
  `-wortschatz.py`, `mutiere-pruefer.py`. Python beendet mit `1`. `abnahme.py` erkennt den
  Traceback und bucht `ABBRUCH`, **alleingefahren bleibt der Wert `1`.** Die Heilung wäre je
  Wächter ein Gegenstandsriegel wie in `pruefe-widerruf.py` — sieben Stellen, nicht gemacht.
* **Forderung 6 sieht eine gefallene Sprechprobe nicht, die nichts druckt.**
  `if not sprechprobe(): return 1` trägt kein Absagewort auf der druckenden Zeile und käme
  durch. Neun solche Stellen wurden von Hand nachgezogen; die zehnte fiele nicht auf. *Sie
  verpflichtet, sie spricht nicht frei* (W10).
* **`pruefe-kennungen.py` fährt seine Sprechprobe nur mit `--sprechprobe`.** Der Regellauf —
  und damit die Abnahme — prüft nie, ob der Wächter überhaupt rot werden kann.
* **Die 18 `zaehle-*` sind außerhalb**, mit 40 Stellen derselben Klasse. Ob die Grenze
  richtig liegt, ist eine Entscheidung; sie steht mit ihrer Zahl da, damit jemand sie fällt.
* **`pruefe-zahlen.py` bleibt unangetastet** — drei Stellen, fremde Bahn.

## Was diese Tafel NICHT sagt

Sie liest den **Quelltext** und einen Lauf über einem leeren Baum. Ein Wächter, dessen
Vorbedingung erst mitten im Lauf wegbricht — ein Werkzeug, das nach der Sprechprobe stirbt,
eine Datei, die zwischen zwei Schritten verschwindet —, ist hier nicht erfasst. **Der leere
Baum ist die billigste Absage, nicht die einzige.** Und ein `2` an der richtigen Stelle sagt
nur, dass der Wächter seine Absage BENENNT; ob er sie an der richtigen Stelle bemerkt,
sagt es nicht (W10).
