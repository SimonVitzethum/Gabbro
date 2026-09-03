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
| `probe-erzeugernamen-frei.gab` | weist `N042` sechs Wörter ab, die wie ein Anhang des Erzeugers *aussehen*? | **nein** — 0 Fehler, `cc` nimmt an. `fn gueltig`, `const Kappe_speicher`, `type Baum_knoten`, ein Feld `setz_b` ohne ein Feld `b`, ein Feld `marke` in einem `format`, eine Variante `gueltig` in einem `tagged type`. *Eine Wortliste hätte alle sechs abgewiesen* ([`../ERZEUGERNAMEN.md`](../ERZEUGERNAMEN.md)) |
| `probe-probenurteil-typ.gab` | sieht jemand den TYP des Wertes, den eine Probe zurückgibt? | **nein** — `return 7;` in einem `can_fail`: 0 Fehler, `emit` schreibt `return 7;` in eine `bool`-Funktion, und `cc -Werror` nimmt es an. *Alle vier Stufen laufen durch; anders als bei `N044` gibt es keine vierte, die absagt* |
| `probe-rueckgabetyp.gab` | ist das eine Lücke des `check` oder eine von `M1`? | **von `M1`** — eine von vier Verfälschungen fällt (`-> u8 { return 300; }` an `M101`), die drei über die `bool`/Zahl-Grenze schweigen. `m1.rs::passt` vergleicht BEREICHE, und `Typ::Wahrheit` hat keinen |
| `probe-probenurteil-schleife.gab` | greift `N045` an einer Probe, deren einziger Ausgang in einem `forever` steht — und zu Recht? | **er greift, und NICHT zu Recht** — `cc -Werror` nimmt das C derselben Schleife an (`for (;;)` hat kein Ende). `endet_immer` liest jede Schleife als durchfallend; ein `forever` ohne `leave` fällt nicht durch |
| `probe-traverse-grundname.gab` | wie viele `traverse`-Stellen laufen über einen Namen, den nur ein `let` trägt? | **null von 41** — und `D017` probehalber am `traverse` angeschaltet gibt über 476 Dateien **null** neue Absagen. Die Regel fänge nichts und wiese die `let`-Form falsch ab. *Benannt, nicht gebaut.* **Nebenbefund:** `K003` weist dieselbe korrekte `let`-Form schon heute ab — derselbe fehlende Blockgeltungsbereich, eine Stelle weiter |
| `probe-elems-feldname.gab` | liest jemand den Feldnamen im Suffix von `elems of`? | **niemand** — dieselbe Verfälschung in `ensures`, `requires` und einem `spec fn`-Rumpf: **0 Fehler**. Auch `M109` nicht, obwohl es jeden Namen einer Nachbedingung liest. *Der GRUNDname fällt sehr wohl* (Kontrolle im selben Lauf). Daraus wurde `D019` ([`../../beispiele/gift/431-elems-feldname-gibt-es-nicht.gab`](../../beispiele/gift/431-elems-feldname-gibt-es-nicht.gab)) |

| `probe-transport-poll-used.gab` | ist `poll_used` (`caprock-virtio/src/lib.rs`:363) in Gabbro schreibbar, oder nur ungeschrieben? | **ungeschrieben** — `10 items, 0 errors, 0 hints`, senkt ab, `cc` nimmt an. Der Ueberlauf hat in Gabbro einen NAMEN statt eines `None` ([`../FUENFTE-MARKE.md`](../FUENFTE-MARKE.md)) |
| `probe-transport-kick-berechneter-versatz.gab` | traegt ein `device … at mmio` eine Weckadresse, die erst zur Laufzeit feststeht? | **ja** — die Laufzeithaelfte geht in die Geraete-BASIS. *Und der Pruefer allein haette falsch geurteilt:* 0 Fehler, und der Erzeuger sagte `C001` ab, bis das `let` einen Typ trug |
| `probe-transport-merkmale-aushandeln.gab` | `offered`/`negotiate` -- 64 Bit durch ein 32-Bit-Fenster | **ungeschrieben**. `want as u32` faellt an `M101`: Rust schneidet dort STILL ab |
| `probe-transport-warteschlange-aufsetzen.gab` | `queue_setup` gibt ein `Option<(Queue, u16)>` -- hat Gabbro die Form? | **nicht als `tagged`** (kein Konstruktor, `O8`), **wohl als Fehlerkanal** -- und der sagt mehr: die Abwesenheit traegt einen Namen |
| `probe-transport-ruecksetzen.gab` | die begrenzte Wartestelle auf `STATUS == 0` | **ungeschrieben**. Caprock spinnt 100 000 mal und faehrt dann trotzdem weiter; `on_exceeded` laesst das nicht still |
| `probe-ecam-faehigkeitenlauf.gab` | `probe_ecam` + `bar_addr` -- ein Lauf durch eine Liste, die das GERAET schreibt | **ungeschrieben** -- `17 items, 0 errors, 0 hints`. `K006` faengt dabei die Falle: `bounded N ops` zaehlt OPS, nicht Durchgaenge |
| `probe-region-schnitt-und-nullen.gab` | `Region::carve` und Nullen ueber eine LAUFZEIT-Laenge | **ungeschrieben**, beide |
| `probe-netz-rahmen-und-ergebnis.gab` | der ganze ARP-Rahmen statt vier Feldern, und ein Ergebnis mit getrennt pruefbaren Feldern | **ungeschrieben**. Der `format` macht `ethertyp = 0x0800` zum Uebersetzungsfehler statt zu einem falschen Paket |
| `probe-opak-am-feld.gab` | greift `N030` auch, wenn der falsche `opaque`-Wert aus einem FELD kommt? | **nein** -- ein Fehler bei VIER falschen Stellen. Am Parameter faellt es; am Zeigerfeld, an einer Bindung daraus und an einem `opaque` VERBUND nicht. Daraus wurde `O7` |
| `probe-tagged-wird-gebaut.gab` | laesst sich ein `tagged type`-Wert BAUEN? | **nein**, in keiner von vier Schreibungen. Neun `tagged type`s im Korpus, alle nur zerlegt, keiner gebaut -- «B9» ein drittes Mal. Daraus wurde `O8` |
| `probe-marke-an-retry-und-traverse.gab` | senkt `next` an einer `retry`-Marke ab? | **bis 2026-09-03 nein** -- `0 errors` beim Pruefer, `C001` beim Erzeuger; der EINZIGE `schleifen.push` der Datei stand im `forever`-Schreiber. Der Korpus verdeckte es: alle `leave`/`next` von `beispiele/41` nennen `forever`-Marken. Daraus wurde `D21` -- `retry` lowert jetzt dieselbe Marke |
| `probe-fehlerkanal-verbundwert.gab` | `let x = f() else (e)` mit einem VERBUND -- was schreibt der Erzeuger? | **bis 2026-09-03**: `W w;` und dann `w->a`. `0 errors` beim Pruefer, `cc`: *invalid type argument of '->'*. **Durch LESEN des Rumpfs gefunden, nicht durch ein Muster.** Daraus wurde `D22` -- `verbundlokale` registriert die Bindung jetzt, `w.a` |

**Was eine Probe nicht ist:** ein Beispiel. `beispiele/` zeigt, was die Sprache kann; eine
Probe hier zeigt, was sie an einer Stelle TUT — und mehrere davon sind absichtlich Programme,
die der Erzeuger absagt. *Sie stehen im Baum, damit die Messung nachfahrbar bleibt und nicht
in einem Absatz steht.*
