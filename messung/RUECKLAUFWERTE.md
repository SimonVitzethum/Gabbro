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

**Die Hausregel für die Sprechprobe steht schon in `abnahme.py`:** eine gefallene
Sprechprobe endet dort mit `2` und dem Wort *„Der Sammellauf misst nicht, was er behauptet.
ABBRUCH."* Ein Wächter, der seine eigene Logik nicht besteht, hat **nichts** gemessen — was
er danach über den Baum sagt, ist keine Aussage über den Baum. Dieselbe Regel gilt hier für
alle 28.

**Zwei Rangstufen der Gefahr**, und sie stehen in dieser Reihenfolge:

1. **Leere Grundgesamtheit → `0`.** *Ein positives Urteil über nichts* (W17). Es sieht aus
   wie ein Ergebnis, wird nie nachgerechnet und deckt alles.
2. **Fehlende Vorbedingung → `1`.** Sieht aus wie ein Rückstand. Kostet eine Stunde
   Suche nach einem Befund, den es nicht gibt — und wenn er gefunden wird, ist der Wächter
   inzwischen als „bekannt rot" gebucht.

## Die Tafel

*Spalte „leer" ist gemessen: der Rücklaufwert beim Lauf über dem leeren Baum.*

| # | Wächter | 0 | 1 | 2 | leer | Vermischung |
|---|---|---|---|---|---|---|
| 1 | `mutiere-pruefer.py` | sauber | tote Anker, unbekannte Fläche, **Sprechprobe** | `crates/` schmutzig | 1 | Sprechprobe → 1 |
| 2 | `pruefe-abstieg.py` | sauber/gebucht | neue Lücke, veraltete Buchung, **Sprechprobe**, **`lib.rs::unterbloecke` fehlt** | — | 1 | **kein `2`**; `sys.exit("…")` = 1 |
| 3 | `pruefe-aufloesung.py` | sauber | Ratsche | Sprechprobe | 1 | (Absturz bei fehlender Quelle) |
| 4 | `pruefe-beweise.sh` | ALL PASS | Fehler **und** vier reine Abbrüche | — | 1 | **kein `2`** — s. u. |
| 5 | `pruefe-emission.sh` | ALL PASS | ~60 Stellen, darunter **kein `cc`**, **Sprechprobe** | — | 1 | **kein `2`** |
| 6 | `pruefe-englisch.py` | ALL PASS | Ratschen | drei Sprechproben | **0** | **leer → grün** |
| 7 | `pruefe-grammatiktafel.py` | 0 ungedeckt | ungedeckte Zellen, **„KEIN LAUF — es wurde NICHTS gemessen"** | Sprechprobe | 1 | **Abbruch → 1** |
| 8 | `pruefe-gruende.py` | sauber | **Sprechprobe** | — | **0** | **leer → grün**, Sprechprobe → 1 |
| 9 | `pruefe-kennungen.py` | ALL PASS | Doppelbelegung, Sprechprobe (nur mit `--sprechprobe`) | — | **0** | **leer → grün**; Sprechprobe nicht im Regellauf |
| 10 | `pruefe-klauseln.py` | keine neue | neue Fundstelle, **„ABBRUCH … es wurde NICHTS gemessen"** | — | 1 | **Abbruch → 1** |
| 11 | `pruefe-konstrukte.py` | keine neue | neue ohne Probe, **„ABBRUCH … es wurde NICHTS gemessen"** | — | 1 | **Abbruch → 1** (enthält den Leertest!) |
| 12 | `pruefe-lean-beweis.sh` | LEAN GREEN | rote Module **und** fünf Abbrüche | — | 1 | **kein `2`** |
| 13 | `pruefe-lean-programm.sh` | LEAN GREEN | rot **und** sechs Abbrüche | — | 1 | **kein `2`** |
| 14 | `pruefe-luecken.py` | ALL PASS | offene/tote Anker | schmutzig · Nullauf rot · Rückgabe gescheitert | 2 | **VORBILD** |
| 15 | `pruefe-notation.py` | alles zu | stumme Absage, **„der Pruefer baut nicht"** | — | 1 | Abbruch → 1; **Bauausfall ohne `error[E` gar nicht erkannt** |
| 16 | `pruefe-p6-beweis.sh` | ISABELLE GRUEN | rot **und** sechs Abbrüche (Frist inbegriffen) | — | 1 | **kein `2`** |
| 17 | `pruefe-reichweite.py` | keine Lücke | ungelesen, **Sprechprobe** | — | 1 | Sprechprobe → 1 |
| 18 | `pruefe-saetze.py` | sauber | Ratsche, erfundene Kennung | Sprechprobe · Binärprogramm fehlt/veraltet · Frist · Werkzeug lief nicht | 2 | **VORBILD** |
| 19 | `pruefe-schablonen.py` | sauber | Ratsche, Prämisse ohne Adresse | Binärprogramm fehlt · Frist · Werkzeug lief nicht · Format passt nicht | 2 | **Sprechprobe → 1** (im selben Werkzeug!) |
| 20 | `pruefe-sonden.sh` | keine widerlegt | widerlegt, ungebaut, **Sprechprobe** | unbekanntes Argument | **0** | **leer → grün** („0 von 0 Sonden") |
| 21 | `pruefe-syntax.sh` | ALL PASS | verbotene Form, **vier Sprechproben**, **fehlende `SYNTAX.md`** | — | 1 | **kein `2`**; **fehlgeschlagener `cargo build` → grün** |
| 22 | `pruefe-todo.py` | ALL PASS | Befunde, **Sprechprobe** | — | 1 | Sprechprobe → 1 |
| 23 | `pruefe-vergabe.py` | Ratsche hält | Ratsche, **Sprechprobe** | — | 1 | Sprechprobe → 1 |
| 24 | `pruefe-waechter.py` | keine Verletzung | Verletzungen, **Sprechprobe** | — | 0¹ | Sprechprobe → 1 |
| 25 | `pruefe-widerruf.py` | ALL PASS | lebende Vorkommen | unvollständiger Eintrag · Sprechprobe | 1 | **VORBILD**; fehlende `PLAN.md` stürzt ab |
| 26 | `pruefe-wortschatz.py` | deckt | fehlt/tot/unerreichbar, **Sprechprobe** | — | 1 | **kein `2`**; **leere Tabelle → grün** |
| 27 | `pruefe-zahlen.py` | keine Abweichung | Abweichung, Selbstbezug, **vier Sprechproben**, **„0 von 0 … NICHTS gemessen"** | — | 1 | **kein `2`** — *fremde Bahn, s. u.* |
| 28 | `pruefe-zitate.py` | Ratsche hält | Ratsche, **„ABORT: no checker sources"**, **„catalogue unreadable"** | Sprechprobe | 1 | **Abbruch → 1, Sprechprobe → 2 in EINER Datei** |

¹ `pruefe-waechter.py` liest `instrumente/pruefe-*` und findet sich dabei immer selbst — seine
Grundgesamtheit kann nicht leer werden. Die `0` im leeren Baum ist deshalb kein Fehlurteil.

## Die vier Vorbilder

`pruefe-luecken.py`, `pruefe-saetze.py`, `pruefe-widerruf.py` und der `2`-Zweig von
`pruefe-schablonen.py` trennen die drei Klassen sauber. **Die Form, die alle vier teilen:**

```python
    if not BIN.is_file():
        print(f"ABBRUCH: {BIN} fehlt -- gebaut wird auf ki-pc-fisch-101 (CLAUDE.md).",
              file=sys.stderr)
        sys.exit(2)
```

Drei Bestandteile, und keiner ist Schmuck: das **Wort** `ABBRUCH`, der **Grund** samt Heilung,
und der **Rücklaufwert 2**. Wer nur zwei davon schreibt, hat einen Wächter, dessen Absage
sich als Befund liest.

## Die zwölf Nachzüge und die Buchungen

**Nachgezogen** (Abbruch bekommt `2`):

* `pruefe-grammatiktafel.py` — „KEIN LAUF"; **der Fall aus der Aufgabe selbst**
* `pruefe-klauseln.py`, `pruefe-konstrukte.py`, `pruefe-zitate.py` — Zweige, die das Wort
  `ABBRUCH` bereits DRUCKEN und mit `1` enden
* `pruefe-schablonen.py`, `pruefe-todo.py`, `pruefe-vergabe.py`, `pruefe-waechter.py`,
  `pruefe-reichweite.py`, `pruefe-gruende.py`, `mutiere-pruefer.py`, `pruefe-abstieg.py` —
  gefallene Sprechprobe
* `pruefe-beweise.sh`, `pruefe-lean-beweis.sh`, `pruefe-lean-programm.sh`,
  `pruefe-p6-beweis.sh`, `pruefe-emission.sh`, `pruefe-syntax.sh` — fehlendes Werkzeug,
  fehlender Gegenstand, Frist, Sprechprobe
* `pruefe-notation.py` — Abbruch auf `2`, **und der Bauausfall wird überhaupt erst erkannt**

**Leere Grundgesamtheit bekommt `2`:** `pruefe-englisch.py`, `pruefe-gruende.py`,
`pruefe-kennungen.py`, `pruefe-wortschatz.py`, `pruefe-sonden.sh`, `pruefe-beweise.sh`,
`pruefe-syntax.sh`.

**Gebucht statt geheilt** — und der Grund steht dabei:

| Stelle | Warum sie bleibt |
|---|---|
| `pruefe-zahlen.py`, ganz | **Fremde Bahn.** Sie übersetzt diese Datei in derselben Nacht; zwei Läufe auf einer Datei zerstören einander (`CLAUDE.md`). Die drei Stellen sind hier benannt und gehören ihr. |
| tote Anker in `mutiere-pruefer.py` → 1 | Ein toter Anker ist ein Befund ÜBER DEN KATALOG, nicht bloß eine ausgefallene Messung. Er verkleinert die Bezugsgröße, und genau das ist die Klage. |
| `UNGEBAUT` in `pruefe-sonden.sh` → 1 | Teilmessung: die anderen Sonden sind gelaufen. Ein Loch mit einer Zahl steht schon in der Ausgabe. |
| „ergibt keine Theorie" / „zwei Einheiten heißen gleich" (p6, lean) → 1 | Das ist eine Aussage über das ERZEUGNIS, nicht über das Werkzeug: der Erzeuger liefert etwas, das die vereinbarte Form nicht hat. |
| `pruefe-waechter.py`, leere Besetzung | Nicht erreichbar — er liest sich selbst mit. |
| `pruefe-aufloesung.py`, leere Quellenmenge | Nicht erreichbar — dieselbe Menge trägt `umgebung.rs`; ist sie leer, stürzt der Wächter vorher ab. |
| ~50 weitere `exit 1` in `pruefe-emission.sh` | Echte Befunde je Stufe. Nur der Kopf (kein `cc`, Sprechprobe, „diese Zählung misst NICHTS") ist Abbruch. |

## Was diese Tafel NICHT sagt

Sie liest den **Quelltext** und einen Lauf über einem leeren Baum. Ein Wächter, dessen
Vorbedingung erst mitten im Lauf wegbricht — ein Werkzeug, das nach der Sprechprobe stirbt,
eine Datei, die zwischen zwei Schritten verschwindet —, ist hier nicht erfasst. **Der leere
Baum ist die billigste Absage, nicht die einzige.** Und ein `2` an der richtigen Stelle sagt
nur, dass der Wächter seine Absage BENENNT; ob er sie an der richtigen Stelle bemerkt,
sagt es nicht (W10).
