# Der Ankerhaken — gemessen, und er hält nicht

*(2026-08-30, `./instrumente/pruefe-zitate.py`, `./instrumente/mutiere-pruefer.py --anker`)*

## Was behauptet war

`pruefe-zitate.py` steht auf **274 Kandidaten** gegen ein Ziel von **207**. Der Ordner hatte
am 2026-08-28 entschieden, hier nicht das Ziel zu erreichen, sondern **die Grundgesamtheit zu
berichtigen** — mit diesem Grund:

> `emit.rs`' Kommentarzeilen sind zum Teil **Mutationsanker** von `mutiere-pruefer.py`. Sie
> umzuschreiben gefährdet den Katalog — `--anker` fällt still auf `FEHLT`.
> **Ein Ziel, dessen Erreichen ein anderes Instrument stilllegen kann, ist falsch gesetzt.**

Der Satz ist richtig. **Seine Voraussetzung ist es nicht.**

## Was gemessen ist

| | Zahl |
|---|---:|
| Mutationen im Katalog | 340 |
| Ankerzeilen, verschieden, über 30 Dateien | 499 |
| davon **Kommentarzeilen** | **4** |
| Anker, die eine Kennung in Rückstrichen tragen | **0** |
| Kandidaten, die die Ankerregel herausnimmt | **0** (274 → 274) |

Die vier Kommentarzeilen, die überhaupt Anker sind — vollständig, das ist die ganze Menge:

| Datei | Mutation | Zeile |
|---|---|---|
| `typen.rs` | `breite-passt-immer` | `/// **Ein Bereich, der KEINEN Wert` |
| `aufrufgraph.rs` | `some-ist-ein-ruf` | ``// `Some`/`None` sind Konstruktoren, keine Aufrufe (s. «B35»).`` |
| `emit.rs` | `markiertes-match-bekommt-einen-sammelzweig` | `// **Wenn JEDER Zweig zurueckkehrt` |
| `phasen.rs` | `endender-zweig-zaehlt-mit` | `// **Ein `if` ohne `else`` |

Keine davon zitiert eine Kennung der Form `[A-Z][0-9]{3}` in Rückstrichen. Die eine, die
überhaupt Rückstriche trägt, meint `Some`/`None` und «B35» — beides keine Kennung.

## Der Befund

**Die beiden Grundgesamtheiten sind disjunkt, und zwar bauartbedingt.** Ein Anker ist ein Lauf
wörtlichen *Quelltextes*; ein Kandidat braucht eine *Kennung in Rückstrichen*. Kein Anker hat
eine. Also:

* `emit.rs` führt **135** Ankerzeilen, davon ist **eine** ein Kommentar — und sie zitiert
  nichts. Die **40** `emit.rs`-Kommentare, die `pruefe-zitate.py` nennt, sind **keine Anker**.
* Alle 274 Kandidaten sind frei umschreibbar. `--anker` kann davon nicht auf 339 fallen.

> **Damit ist der angeordnete Weg versperrt: es gibt keine Grundgesamtheit zu berichtigen.**
> Die Berichtigung ist kein Streit über ihre Größe — sie ist leer.

## Was daraus folgt

1. **Die Marke wird NICHT neu gebucht.** Sie steht weiter auf `MARKE = 274`, das Ziel bleibt
   207, und die Schuld bleibt eine Schuld: 67 Kommentare in zwanzig Prüfer-Dateien, die sagen
   müssen, wo ihre Regel lebt. Zähler und Nenner bewegen sich nicht.
2. **Die Regel ist trotzdem eingebaut** (`anker_kommentare`, Ausschluss in `erhebe`) — nicht
   um etwas herauszunehmen, sondern um die Disjunktheit **zu prüfen statt sie anzunehmen**.
3. **`ankerprobe` spricht die Null bei jedem Lauf aus.** Eine Grundgesamtheitskorrektur, die
   niemand nachzählt, ist eine Behauptung; diese wird beidseitig gerechnet (`erhebe()` gegen
   `erhebe(anker=False)`) und die Differenz gedruckt. Schreibt jemand eine Kennung in einen
   Anker, hört die Zahl auf, null zu sein — und sagt es.
4. **Ein unlesbarer Katalog ist rot, keine stille Null.** Kann `mutiere-pruefer.py` nicht
   geladen werden, bricht `pruefe-zitate.py` mit `ABORT` ab. Ein Ausschluss, der nichts
   ausschließt, weil er nichts sieht, sieht genauso aus wie einer, der gewirkt hat.

## Die Fehlerrichtung dieser Messung

*Sie misst die Zeilengleichheit.* Ein Kandidat gilt als Anker, wenn seine abgestreifte Zeile
**wörtlich** eine Ankerzeile ist. Zwei Gegenproben liefen mit:

* **Teilstring statt Zeile** — steht der Kandidatentext *irgendwo* in einem `m.alt` derselben
  Datei? **0 Treffer.**
* **Kennung im Anker** — trägt irgendein `m.alt` das Muster `` `[A-Z][0-9]{3}` ``?
  **0 Treffer.** Das ist die stärkere der beiden: sie schließt die Überschneidung aus, ohne
  über Zeilengrenzen reden zu müssen.

Was sie **nicht** ausschließt: dass das Umschreiben eines Kommentars einen Anker *mehrdeutig*
macht, indem der neue Text zufällig eine zweite Kopie einer Ankerzeile erzeugt. Das ist
`ANKER MEHRDEUTIG`, nicht `ANKER FEHLT`, und `--anker` fängt es. **Genau dafür läuft der
Wächter nach jedem Posten.**

## Belegt durch

`./instrumente/pruefe-zitate.py` → 274 Kandidaten, drei Proben, Ankerregel nimmt 0.
`./instrumente/mutiere-pruefer.py --anker` → **340 von 340**, unverändert vor und nach dem Eingriff.
