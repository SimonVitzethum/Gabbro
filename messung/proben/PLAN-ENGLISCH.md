# Was eine vollständige Übersetzung kostet — gemessen

**Gemessen am 2026-08-31**, lokal (`free -g`: 31 GB gesamt, 13 GB verfügbar, 20 Kerne),
gegen `9f88c2e` + die Diagnostikübersetzung dieses Laufs.

Der Auftrag des Nutzers: *„Alles soll auf Englisch sein — Kommentare, `.md` usw."*
Dieses Dokument zählt, was das heißt. **Es entscheidet nichts** — die Entscheidungen,
die es vorbereitet, stehen unten als Rechnung, nicht als Vorschlag.

> **Ausdrücklich ausgenommen: `CLAUDE.md` und die Commit-Nachrichten.** Das ist die
> **Arbeitssprache des Nutzers**, keine Außenfläche. `CLAUDE.md` ist in jeder Zahl
> dieses Dokuments herausgerechnet; die Commit-Nachrichten sind gar nicht erst gezählt.
> *Wer die Arbeitssprache übersetzt, übersetzt das Werkzeug und nicht das Erzeugnis.*

---

## 0. Was schon erledigt ist

| Fläche | Stand |
|---|---|
| **Diagnostik** (`crates/gabbro-check`) | **33 → 0** Meldungszeilen mit deutscher Prosa |
| **`gabbro hilfe`** und alle Unterbefehls-Hilfetexte | schon vollständig englisch |
| **`README.md`** | schon vollständig englisch — kein Umlaut, keine deutsche Überschrift, keine deutsche Tabellenzelle |

Die drei verbleibenden deutschen Zeichen im `README.md` sind **kein Rest, sondern
Absicht**: die Marke `<!-- widerruf:aus -->` (liest `pruefe-widerruf.py`), das
wörtliche Linkerzitat `Mehrfachdefinition von` (der *Beleg* für die Locale-Forderung —
übersetzt wäre er kein Beleg mehr) und die Unterbefehls- und Ordnernamen.

---

## 1. Die `.md`-Fläche

| Ordner | Dateien | Zeilen (nichtleer) | davon deutsch |
|---|---|---|---|
| `messung/` | 72 | 14 297 | 9 488 |
| `dokumente/` | 14 | 20 768 | 7 210 |
| Wurzel (`TODO.md`, `DONE.md`, `README.md`, …) | 4 | 5 045 | 3 207 |
| `passlogik/` | 2 | 382 | 252 |
| übrige (`sonden/`, `messung/netz/`, …) | 6 | 387 | 281 |
| **Summe** | **98** | **40 879** | **20 438  (49 %)** |

> **W25 — der Nenner:** „deutsch" heißt hier *eine Zeile, die mindestens ein Wort aus
> der geschlossenen Funktionswortliste trägt*. Das ist eine **untere** Schranke für den
> Aufwand und eine **obere** für die Zeilenzahl: eine Zeile mit einem deutschen Wort ist
> gezählt wie eine ganz deutsche. Codeblöcke, Tabellenrahmen und Zitate sind mitgezählt.

---

## 2. Die Unterbefehlsnamen — die Rechnung, nicht die Entscheidung

Von 17 Unterbefehlen sind **4 schon englisch** (`emit`, `abi`, `lean`, `alias`).
**13 wären umzubenennen**, `hilfe` → `help` eingeschlossen.

| Name | Code-Stellen | Dokumentstellen | englisch wäre |
|---|---|---|---|
| `pruefe` | 46 | 141 | `check` |
| `pflichten` | 52 | 54 | `obligations` |
| `schablonen` | 27 | 24 | `templates` |
| `paesse` | 24 | 33 | `passes` |
| `zeugnis` | 16 | 37 | `certificate` |
| `annahmen` | 14 | 33 | `assumptions` |
| `blindstellen` | 10 | 21 | `blindspots` |
| `fragmente` | 9 | 4 | `fragments` |
| `kosten` | 8 | 12 | `costs` |
| `kontexte` | 8 | 11 | `contexts` |
| `zeremonie` | 8 | 10 | `ceremony` |
| `k-bedingung` | 3 | 3 | `k-condition` |
| **Summe der 12 deutschen** | **225** | **383** | **608 Stellen** |
| *`emit` · `abi` · `lean` · `alias` (schon englisch)* | *71* | *133* | *— kein Eingriff* |
| **alle 16 zusammen** | **296** | **516** | **812** |

**66 Code-Dateien** (`.py` · `.sh` · `.rs`) würden brechen, **140 Dokumentdateien**
veralten.

### Der additive Weg — und er ist im Baum schon vorgezeichnet

`crates/gabbro-cli/src/main.rs:19` ist ein flaches `match befehl.as_str()`, und
**Zeile 448 führt den Mehrfachzweig bereits vor**:

```rust
"--hilfe" | "-h" | "hilfe" => { … }
```

Ein englischer Erstname als zusätzliches Muster kostet je Unterbefehl **eine Zeile**:

```rust
"check" | "pruefe" => befehl_pruefe(rest),
```

**Damit brechen null der 608 Stellen.** Die Rechnung gegenübergestellt:

| | harter Umbau | additiv (Alias) |
|---|---|---|
| Zeilen in `main.rs` | 13 geändert | 13 geändert |
| Code-Stellen nachzuziehen | **225**, in 66 Dateien | **0** |
| Dokumentstellen | **383**, in 140 Dateien | 0 (nachziehbar, wann man will) |
| Bruchgefahr | jeder Wächter, jedes `.sh` | keine |
| Kosten für den Beta-Nutzer | — | er liest den englischen Namen zuerst |

**Zwei Haken, die zur Entscheidung gehören:**

1. `split_with("pruefe", …)` und `read_preamble("pruefe", …)` bekommen den Namen als
   Zeichenkette **für ihre Fehlermeldung**. Unter dem Alias meldete die Absage den
   deutschen Namen. Heilung: den tatsächlich getippten Namen durchreichen — *eine
   Meldung, die einen anderen Befehl nennt als den getippten, ist die Klasse `W16`.*
2. `alias` ist schon englisch, meint aber die **Zeigeraliasanalyse** und nicht einen
   Befehlsalias. Ein Dokument, das „aliases" für Befehlszweitnamen sagt, kollidiert mit
   einem Unterbefehl dieses Namens. *Ein Wort, zwei Begriffe, eine Verwechslung.*

> **Entschieden wird das hier nicht.** Beide Spalten stehen da, damit der Nutzer sie
> vergleichen kann.

---

## 3. Die Zahl, die kein Zähler sieht: Wächter an deutschem Dokumenttext

**Das ist die eigentliche Zahl dieses Vorhabens.** Ein Zähler sieht Zeilen; er sieht
nicht, dass ein Wächter aufhört zu messen, wenn eine Überschrift übersetzt wird.

**21 von 54 Instrumenten** lesen eine `.md` **und** tragen ein deutsches Literal in
einer *Erkennungsstellung* (Regex, `in`-Test, `startswith`, `split`, `grep`). Davon
sind nach Durchsicht **falsch positiv**: Treffer, deren deutsches Literal ein
**CLI-Schalter** ist (`--probe`, `--tafel`, `--je-datei`, `--je-satz`) oder eine
**Rust-Quelle** liest (`Absage::fehler\(`), nicht ein Dokument.

**Bestätigt am Text, drei Klassen:**

### (a) Wer eine deutsche BESCHRIFTUNG aus einem Dokument parst — *wird blind, ohne rot zu werden*

| Instrument | liest | deutsches Muster |
|---|---|---|
| `pruefe-todo.py` | `TODO.md`, `README.md`, `DONE.md`, `PLAN.md`, … | `(\d+) Kennzahlen mit Befehl`, `(\d+) fettgedruckte Zahlen in Tabellenzellen ohne einen`, `EBNF: (\d+) Regeln` |
| `pruefe-zahlen.py` | `MESSUNGEN.md`, `PFLICHTEN.md`, `PASSREGISTER.md`, `README.md`, … | `Vertrauen\|Zusage\|bewiesen…`, `der Lauf sagt` |
| `pruefe-grammatiktafel.py` | `SYNTAX.md`, `GRAMMATIKTAFEL.md`, `DOMAENENNAMEN.md`, `EINSAME-WOERTER.md` | `startswith("GEMESSEN")` |
| `pruefe-widerruf.py` | `DONE.md`, `MESSUNGEN.md`, `FRAGMENTE.md`, … (104 Dateien) | `<!-- widerruf:aus --> … <!-- widerruf:an -->` |

### (b) Wer die deutsche AUSGABE anderer Wächter liest — *wird rot, aber massenhaft*

| Instrument | Muster |
|---|---|
| `pruefe-waechter.py` | `ABBRUCH\|ABORT:\|KEIN LAUF\|NICHTS gemessen\|NICHTS geprueft\|NICHTS an ihnen` |
| `abnahme.py` | `es wurde NICHTS gemessen` |
| `abschnitt.py` | `ABGESCHNITTEN in: Stufe 2: der Kopf` u. a. |

`pruefe-waechter.py` **fordert** von allen 50 Instrumenten ein Abbruchwort aus dieser
Liste (Forderung 3, *ROT BEI ABBRUCH*). Übersetzt man ein Instrument auf
*„nothing was measured"*, verliert es seine Forderung — **das wird sichtbar rot**, nicht
still. Die Liste ist bereits halb zweisprachig (`ABORT:` steht darin, `ABBRUCH` auch).

### (c) Der Beleg, dass (a) kein Gedankenspiel ist — **es ist hier schon passiert**

`instrumente/pruefe-todo.py` führt es in seinem eigenen Kommentar:

> **The rule count stands in `TODO.md` today as „153 EBNF-Regeln"**, no longer as
> „**N Regeln, 0 offen**" — the old wording has been gone for weeks. *So this pattern hit
> nothing, and the TODO half did not say so until 2026-08-28.*

**Eine bloße UMFORMULIERUNG — nicht einmal eine Übersetzung — hat den Wächter wochenlang
still blind gemacht.** Genau diese Klasse, in genau dieser Datei, schon bezahlt. Eine
Übersetzung ist dieselbe Operation auf 20 438 Zeilen auf einmal.

### Und die Heilung steht auch schon da

Dieselbe Datei zeigt das Muster, das den Übergang trägt — **das Muster wird
zweisprachig, bevor das Dokument übersetzt wird:**

```python
(r"(\d+) (?:EBNF-Regeln|Regeln, 0 offen|rules, 0 open)", r_heute, "EBNF-Regeln"),
(r"(\d+) (?:Terminale gegen|terminals against)",         t_heute, "EBNF-Terminale"),
(r"\((?:heute|today) (\d+) / \d+\)",                     r_heute, "EBNF-Regeln (heute-Klammer)"),
```

**Die Reihenfolge ist die ganze Regel:** erst das Muster beidsprachig, dann das
Dokument, dann — viel später — das deutsche Alternativ entfernen. Wer sie umdreht,
bekommt einen grünen Wächter, der nichts mehr misst.

---

## 4. Was daraus folgt — als Rechnung

| Stufe | Umfang | Gefahr |
|---|---|---|
| Diagnostik | **erledigt** (33 → 0) | — |
| `README.md` | **erledigt** (war schon englisch) | — |
| Unterbefehle additiv | 13 Zeilen `main.rs` + 2 Haken | keine |
| **Wächtermuster zweisprachig machen** | **~7 Instrumente**, (a) und (b) | **muss VOR jedem Dokument kommen** |
| `dokumente/` übersetzen | 7 210 deutsche Zeilen, 14 Dateien | Klasse (a) |
| `messung/` übersetzen | 9 488 deutsche Zeilen, 72 Dateien | Klasse (a) |
| `TODO.md` / `DONE.md` | 3 207 deutsche Zeilen | **höchste** — `pruefe-todo.py` und `pruefe-zahlen.py` hängen beide daran |

> **Die Zahl, um die es geht, ist nicht 20 438.** Es ist **7**: so viele Wächter müssen
> zweisprachig sein, bevor die erste Dokumentzeile übersetzt wird. Die 20 438 sind
> Fleißarbeit; die 7 sind der Unterschied zwischen einer Übersetzung und einer
> Prüfkette, die grün aussieht und nichts mehr hält.

---

## Wie man diese Zahlen nachrechnet (W7)

```bash
# 1. Deutsche Prosa in der DIAGNOSTIK (ohne Quelltext-Echo, ohne `...`):
for f in beispiele/gift/*.gab beispiele/*.gab; do ./target/debug/gabbro pruefe "$f"; done > /tmp/lauf.txt
# 2. `.md`-Fläche und Aufrufstellen: die Zähler dieses Laufs liegen im
#    Arbeitsprotokoll des Commits, sie sind reines Textzählen.
grep -rnoE 'gabbro (pruefe|paesse|zeugnis|blindstellen|zeremonie|schablonen|annahmen|pflichten|kontexte|k-bedingung|fragmente|kosten|alias|abi|lean|emit)\b' . --include=*.py --include=*.sh --include=*.rs --include=*.md
# 3. Wächter an Dokumenttext:
grep -ln '\.md' instrumente/*.py instrumente/*.sh
```

**Und was das NICHT heißt:** die 21 sind *Kandidaten*, die vier in (a) und drei in (b)
sind *durchgesehen*. Was hier nicht steht, kann trotzdem an deutschem Text hängen —
dieses Dokument verpflichtet, es spricht nicht frei (W10).
