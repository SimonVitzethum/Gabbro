# Die Unterbefehle bekommen englische Erstnamen — additiv, und **null** Aufrufstellen bewegt

*Gemessen und gebaut am 2026-08-31, lokal (`free -g`: 31 GB gesamt, 12 GB verfügbar,
20 Kerne).*

Der Nutzer hat es gesetzt: *„alles englisch"*. Die Rechnung lag vor: **812 Aufrufstellen,
608 hängen an den 12 deutschen Namen** — und **der additive Weg kostet null davon**, mit
Vorbild im Baum (`main.rs`:448 führte schon `"--hilfe" | "-h" | "hilfe"`).

---

## 1. Die zwölf Paare

**Englischer Erstname zuerst, deutscher Zweitname läuft weiter.**

| Erstname (englisch) | Zweitname (deutsch) |
|---|---|
| `check` | `pruefe` |
| `fragments` | `fragmente` |
| `assumptions` | `annahmen` |
| `k-condition` | `k-bedingung` |
| `costs` | `kosten` |
| `contexts` | `kontexte` |
| `obligations` | `pflichten` |
| `blindspots` | `blindstellen` |
| `certificate` | `zeugnis` |
| `ceremony` | `zeremonie` |
| `templates` | `schablonen` |
| `passes` | `paesse` |
| `help` / `--help` | `hilfe` / `--hilfe` / `-h` |

**Nicht in der Tabelle, weil sie von Anfang an englisch waren:** `abi`, `emit`, `lean` — und
`build` (der neue Bau, mit dem Zweitnamen `bau`). *Ein Paar aus einem Wort ist kein Paar.*

**`alias` behält seinen Namen.** Er ist englisch, und er bedeutet hier den **Zeigeralias** —
`gabbro alias` misst die Aliasfläche eines Korpus. Genau darum heißt die zweite Schreibweise in
diesem Baum **Zweitname** und nicht *alias*: *ein Wort für zwei Dinge ist, wie ein Register
anfängt auseinanderzulaufen.*

## 2. Der W16-Haken, und er war ein echtes Loch

`split_with("pruefe", …)` und `read_preamble("pruefe", …)` reichten einen **festen** Namen an
ihre eigene Fehlermeldung weiter. Unter dem anderen Namen nannte die Absage einen Befehl, den
niemand getippt hatte:

```
$ gabbro check --with beispiele/16-by-ops-am-feld.gab …
gabbro pruefe: … is not a `.gabi`          <- der Name, den niemand tippte
```

**Der getippte Name wird jetzt durchgereicht** (`befehl_pruefe(getippt, …)`,
`command_emit(getippt, …)`), und beide Schreibweisen melden sich selbst:

```
$ gabbro check  --with …    ->  gabbro check: … is not a `.gabi`
$ gabbro pruefe --with …    ->  gabbro pruefe: … is not a `.gabi`
$ gabbro emit   --with …    ->  gabbro emit: … is not a `.gabi`
```

> **Dieselbe Klasse wie `W16`:** ein Messgerät, das seinen eigenen Namen meldet statt den des
> Gegenstands. Und dieselbe Klasse wie das `pgrep -f` aus `CLAUDE.md`, nur eine Ebene tiefer.

## 3. Die Gegenrichtung

| Probe | Ergebnis |
|---|---|
| jedes Paar, beide Schreibweisen, stdout+stderr+Rücklaufwert | **byteidentisch, 12 von 12** |
| jeder Erstname ist ein **bekannter** Befehl (Rücklauf ≠ 2) | **12 von 12** |
| `help`, `--help`, `hilfe`, `--hilfe`, `-h` | **eine Ausgabe** |
| die Absage nennt den getippten Namen | **3 von 3** |
| ein unbekannter Befehl (`pruefen`) fällt weiter, mit Zitat | **ja** |
| **491 Dateien, zwei Binärprogramme, `pruefe` und `emit` byteweise** | **NICHTS BEWEGT** |

**Der zweite Punkt ist der, den man vergisst.** Ohne ihn wäre die Gleichheitsprobe erfüllt,
wenn *beide* Schreibweisen in den Unbekannt-Zweig fielen — zwei gleiche Absagen sehen wie ein
gleiches Verhalten aus. *Eine Probe, die Gleichheit misst, muss zuerst messen, dass etwas da
ist.*

## 4. Die Mutation

**454 `absage-nennt-wieder-den-erstnamen`** — `read_preamble` bekommt wieder den festen Namen
`"pruefe"`. **Eine Probe fällt** (`die_absage_nennt_den_getippten_namen`). Im Katalog;
`--anker` meldet **377 von 377**.

## 5. Was ungemessen bleibt

* **Die 608 Aufrufstellen sind nicht umgestellt worden**, und das ist der Punkt: der additive
  Weg kostet null. *Ob sie umgestellt werden sollen, ist eine andere Frage und hier nicht
  beantwortet.*
* **Die deutschen Zweitnamen haben kein Ablaufdatum.** Nichts in diesem Bau sagt, wann oder ob
  sie fallen.
* **Die FAHNEN sind nur teilweise englisch.** `--paesse`, `--je-satz`, `--je-stelle`,
  `--tafel`, `--tor`, `--berechnet`, `--vergleich`, `--weit` stehen weiter deutsch; neu kamen
  `--unit`/`--einheit` und `--dry-run`/`--trocken` als Paare dazu. **Eine Fahnenrechnung wie
  die Befehlsrechnung ist nicht gemacht worden.**
* **Die Hilfe ist die einzige Stelle, an der die Regel steht.** Kein Wächter prüft, dass ein
  NEUER Unterbefehl einen englischen Erstnamen bekommt — `erstnamen.rs` hält die zwölf, die es
  gibt, und nicht den dreizehnten, den jemand morgen hinzufügt.
