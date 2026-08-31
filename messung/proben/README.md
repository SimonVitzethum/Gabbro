# `messung/proben/` — die kleinsten Programme, die eine Frage entscheiden

*Angelegt am 2026-08-31, Bahn V des Vollständigkeitsdurchlaufs.*

> **Der `W24`-Vorlauf, als Datei.** Bevor eine Absage des Erzeugers entschieden wird, gehört
> das kleinste Programm hingeschrieben, das die Form enthält, und durch den **unveränderten**
> Prüfer und Erzeuger gefahren. *Ein Kommentar, der sagt „das fängt der Prüfer schon", ist
> keine Messung.*

Sie liegen hier und nicht in `messung/fragmente/`: dort stehen die **zehn eingefrorenen
Ausschnitte** `F01`–`F10`, ein Korpus mit einer eigenen Zählung (`zaehle-fragmente.py` liest
`F*.gab`). Eine Probe ist kein Fragment — sie ist ein Argument in Programmform.

| Datei | die Frage | die Antwort, gemessen |
|---|---|---|
| `probe-elems.gab` | welchen Typ gibt der Prüfer der Laufvariablen von `elems of`? | der Erzeuger senkte sie als `uint32_t` ab — eine Verengung, an der `F06`s C bei `-Werror=type-limits` scheiterte. **Ursache im Erzeuger** (`UEBERSETZUNGSREICHWEITE.md`) |
| `probe-vergleich.gab` | sagt der Prüfer etwas zu einem Vergleich, den sein eigener Bereich konstant macht? | **nein** — 0 Fehler bei 100 % Typdeckung. Der Posten steht in `TODO.md` |
| `probe-match-ruf.gab` | senkt `match` über einem Ruf ab, der einen `tagged type` liefert? | **seit dem 2026-08-31 ja** (`ZWEI-ABSAGEN.md` V2) |
| `probe-unbekannter-ruf.gab` | nimmt der Prüfer einen Ruf an, den niemand deklariert hat? | **ohne Kostenzusage ja** — nur `E009`, ein Hinweis. Mit Kostenzusage fällt `K003`. *Der Befund gehört dem Prüfer* |
| `probe-f32-literal.gab` | welche Breite hat ein Gleitkommaliteral im erzeugten C? | **`double`** — `x * 0.1` rechnet bei `x : f32` in doppelter Breite. 39 974 von 200 000 Werten weichen ab |
| `probe-vier-zellen.gab` | nimmt der Prüfer `state`, `queue`, `chain in`, `threads` wirklich an? | **ohne Kostenzusage ja** — 0 Fehler, vier `C001`. Dieselbe Wurzel: `K003` hängt an einer Zusage, die ein `divergent fn` nicht macht |

**Was eine Probe nicht ist:** ein Beispiel. `beispiele/` zeigt, was die Sprache kann; eine
Probe hier zeigt, was sie an einer Stelle TUT — und mehrere davon sind absichtlich Programme,
die der Erzeuger absagt. *Sie stehen im Baum, damit die Messung nachfahrbar bleibt und nicht
in einem Absatz steht.*
