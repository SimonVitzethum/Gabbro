# Die tragenden Zahlen ohne Befehl — 37 Stück, und keine davon ist Schuld

**Gemessen 2026-08-30.** `./instrumente/pruefe-zahlen.py --reichweite` zählte an diesem Morgen
**64 bewachte Kennzahlen**, **154 fettgedruckte Zahlen in Tabellenzellen ohne Befehl**, davon
**40 tragend** — eine in einer Zusage oder einem Vergleich. Der Auftrag lautete: *nimm die
tragenden, gib jeder einen Befehl daneben; für jede, die du nicht bewachen kannst, schreib hin,
warum.*

**Die zweite Hälfte war die ganze Arbeit.**

## Das Ergebnis in einer Zeile

    76 Kennzahlen mit Befehl, 146 fettgedruckte Zahlen ohne einen
    davon TRAGEND: 37    davon mit geschriebenem GRUND: 37    OFFEN: 0

**Von den 37 tragenden konnte genau EINE einen Befehl bekommen**, und sie stand nicht in der
Liste — sie steht im Fließtext und nicht fettgedruckt in einer Tabellenzelle (§4). Die
übrigen 36 sind nicht ungemessen. **Sie sind unbewachbar, und zwar aus drei Gründen, die man
nicht addieren darf.**

## §1 — Die vier Klassen

| Klasse | wie viele | was sie heißt |
|---|---:|---|
| `PROTOKOLL` | **14** | eine datierte Aufzeichnung. Ein Befehl daneben machte aus einem Protokoll eine Behauptung über heute |
| `KEIN INSTRUMENT` | **14** | über einem FREMDEN Baum gemessen (seL4, Verus, Caprock) oder von einem Messlauf, den dieser Ordner nicht wiederholt |
| `KEINE KENNZAHL` | **8** | eine ORDNUNGSZAHL. *„Ziel Nummer vier"* ist nicht die Zahl vier |
| `URTEIL` | **1** | in seiner eigenen Zeile argumentiert; ein Argument zählt kein Werkzeug |

### `PROTOKOLL` — und die Datei sagt es über sich selbst

`dokumente/MESSUNGEN.md` trägt in seiner Vorrede den Satz, an dem diese Klasse hängt:

> *„no measured figure in this file is pulled up to a later state. A number that fell stays
> where it fell, with its date."*

**Eine solche Zahl zu bewachen hieße, dieses Versprechen zu brechen** — der Wächter verlangte
bei jedem Lauf, dass die Geschichte auf den heutigen Stand geschrieben wird. Vierzehn der 37
sind von dieser Art: die Zeilen der Neuzuweisung vom 2026-08-17 (`Plumbing (K) 173`,
`hanging 50 / 36 K`, `K carried 137`), die Vorher/Nachher-Tafeln einzelner Tage
(`proved 1 → 4`, `mutations 67 → 87`, `ZUSAGE 17`), und die Zusammenführungstafel vom
2026-08-30 (`Mutationsanker 332 | 335 | 340`).

> **Die letzte ist die schönste Probe auf die Klasse.** `340` ist heute falsch — `--anker`
> sagt 345. Aber die Zeile berichtet, was die Zusammenführung an jenem Punkt *ergab*, und
> genau das ist ihr Inhalt. *Eine Zahl, die der Bericht über ihre eigene Widerlegung ist,
> darf nicht mitwandern.*

### `KEIN INSTRUMENT` — der Befehl steht woanders

seL4s `proof/refine` (95 915 Zeilen), Caprocks `cap_space.rs` (16 Pflichten), die
Laufzeitverhältnisse `117 ms | 117 ms`. **Die Zahlen sind echt; der Baum, über dem sie
gemessen wurden, liegt nicht in diesem Ordner** — Caprock steht schreibgeschützt daneben,
seL4 ist eine Veröffentlichung, und die Messreihe ist ein Lauf, den niemand wiederholt.

*Ein Befehl, der `../caprock-messbasis` liest, wäre `W21` in Reinform:* fehlt der fremde Baum,
ist der Rücklaufwert ein Fehlaufruf und kein Befund — rot ohne Fehler oder grün ohne Messung.

### `KEINE KENNZAHL` — der Zähler liest eine Aufzählung

Acht der 37 sind gar keine Messungen:

    | **4** | keine Klempnerei beim Endnutzer — das ist K100 |
    | **1** | der Maßstab | **C** | `H` misst zu sieben Zwölfteln …
    | **9** | der Prüfer als Mathematik, in Lean 4 | **D** | …

**Das ist Ziel Nummer vier, eins und neun.** Der Reichweitenzähler sucht eine fettgedruckte
Zahl in einer Tabellenzelle, und eine nummerierte Liste wird genau so geschrieben. *Er irrt in
beide Richtungen und sagt es selbst* (`W10`) — hier ist gemessen, wie oft: **acht von 37, also
gut einer von fünf in der teuersten Klasse.**

## §2 — Warum ein Register und kein Absatz

**Ein geschriebener Grund altert genau wie eine geschriebene Zahl.** Wird die Zeile, die er
erklärt, umformuliert, senkt der Grund weiter den Zähler und erklärt nichts mehr — *das ist
schlimmer als gar kein Grund, denn er macht aus einem toten Muster eine kürzere Arbeitsliste.*

Deshalb steht jeder Grund in `UNBEWACHBAR` (`instrumente/pruefe-zahlen.py`) mit dem Muster, auf
das er sich bezieht, und **ein Grund, dessen Muster keine Zeile mehr trifft, FÄLLT** — dieselbe
Regel, unter der die bewachten Einträge stehen. Die Sprechprobe fährt sie in beide Richtungen:

    Gruenderegister: ok (ein Grund ohne Zeile faellt)
    Gruende leben:   ok (jeder gebuchte Grund trifft eine Zeile)

## §3 — Und was das NICHT heißt

**Ein Freispruch ist es nicht.** Eine Zahl mit Grund ist weiter unbewacht; was sie nicht mehr
ist, ist unerklärt. Die Zahl, die zählt, ist die dritte:

    OFFEN, also Arbeitsliste: 0

**Null heißt hier nicht *fertig*, sondern *dieser Durchgang ist zu Ende*.** Wer morgen eine
tragende Zahl hinschreibt, findet sie in dieser Zeile wieder — und das ist der Zweck.

## §4 — Die einzige lebende, die falsch war — und der Zähler sah sie nicht

`TODO.md` führt bei Ziel 9 (*der Prüfer als Mathematik, in Lean 4*) den Auslöser:

> *„seit PL.1 (2026-08-21) stehen **52** Sätze über 12 von 12 Pässen, keiner bewiesen"*

`cargo run -q --bin gabbro -- paesse` sagt **71**. Neunzehn Sätze Unterschied, und die Zahl ist
eine **Auslösebedingung** — die teuerste Sorte unbewachter Zahl, denn sie wird einmal gelesen,
in dem Augenblick, in dem jemand entscheidet, ob er anfängt.

> **Der Reichweitenzähler konnte sie nicht finden.** Er sucht fettgedruckte Zahlen in
> Tabellenzellen; diese steht in einem Fließtext. **Die Reichweitenzahl ist damit eine UNTERE
> Schranke für die Schuld und kein Maß für sie** — derselbe `W10`-Satz, den das Werkzeug über
> seine eigene Einteilung druckt, gilt auch für seine Grundgesamtheit.

Berichtigt und bewacht seit dem 2026-08-30, mit `SENTENCES: (\d+) over (\d+) passes` als
Suchweg.

## Die Befehle

```bash
./instrumente/pruefe-zahlen.py --reichweite     # die drei Eimer, tragende zuerst
./instrumente/pruefe-zahlen.py                  # die Sprechprobe des Gruenderegisters
cargo run -q --bin gabbro -- paesse             # die Zahl aus §4
```
