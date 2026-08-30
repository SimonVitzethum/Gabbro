# Zwei Giftproben, die einander decken — die Teilmenge, gemessen

*(2026-08-30, `./instrumente/pruefe-vergabe.py --liste`)*

## Die Zahl war überholt

Der Auftrag sprach von **18** doppelt vergebenen Kennungen. Das Werkzeug führt seine eigenen
Erhöhungen mit (`14 → 18` am 2026-08-21, `18 → 19`, `19 → 20` am 2026-08-28). **Gemessen am
2026-08-30 vor dem Eingriff: 20.** Danach: **19**.

## Warum „alle zwanzig durchgehen" die falsche Frage ist

Eine Doppelbelegung ist für sich genommen harmlos. Sie wird erst dann zu einer **falschen
Aussage**, wenn zwei Giftproben unter derselben Kennung **verschiedene** Vergabestellen
treffen — denn eine Giftprobe prüft nur die Kennung (`-- erwartet: CODE`).

> Fällt dann eine der beiden Regeln ganz aus, bleibt ihre Probe **grün**, getragen von der
> anderen Regel. **Zwei Proben, die einander decken, decken nichts.**

Das ist ein schärferes Kriterium als „sind das zwei Regeln?". Es fragt nicht nach dem Urteil
über die Regel, sondern nach einer nachprüfbaren Eigenschaft der Probenmenge.

## Die Messung

Für jede der 20 Kennungen wurde bestimmt, welche Vergabestelle jede ihrer Giftproben
auslöst — durch Lesen der Probe (Kopf und Programmtext) gegen die Bedingung an der
Vergabestelle. Die Zuordnung ist **gelesen, nicht ausgeführt** — das ist ihre
Fehlerrichtung, und sie steht unten.

> **`ki-pc-fisch-101` war nicht erreichbar** (`ssh` bricht im Bannertausch ab, rc 255).
> **Der Bau lief trotzdem — LOKAL, und er lief grün.** `cargo test` meldet **0 failed** über
> alle Sammlungen; das Binärprogramm wurde dabei mit `P041` neu gebaut. *Die Zuordnung oben
> bleibt gelesen; die TRENNUNG unten ist übersetzt und getestet.*

### A — gegenseitige Deckung: **9 von 20**

| Kennung | Stellen | belegt durch Proben auf | unbeprobte Stellen |
|---|---:|---|---|
| `E008` | 4 | **alle vier** (a 290 · b 140,161,162,173,179,180,49 · c 164 · d 139,242,261) | — |
| `M104` | 2 | **beide** (a 01,14,15,16,17,22,23,48 · b 12,167,212,214,24,26,32) | — |
| `P034` | 2 | **beide** (a 05-auffangzweig · b 45-pub) | — |
| `F002` | 2 | **beide** (a 84,85 · b 93) | — |
| `H011` | 2 | **beide** (a 141 · b 103) | — |
| `M124` | 2 | **beide** (a 236,293 · b 239) | — |
| `N030` | 2 | **beide** (a 200 · b 198,199) | — |
| `O011` | 2 | **beide** (a 344 · b 342) | — |
| `R009` | 5 | **zwei von fünf** (b 404 · d 403) | a, c, e |

### B — keine gegenseitige Deckung: **3 von 20**

Alle Proben liegen auf **einer** Stelle; die andere ist gar nicht beprobt. Das ist ein
*anderer* Befund — eine unbeprobte Regel, keine falsche Deckungsaussage.

| Kennung | Stellen | alle Proben auf | ohne jede Probe |
|---|---:|---|---|
| `D012` | 2 | (b) `opsruf.rs:598` — alle sieben | (a) `opsruf.rs:571` |
| `H012` | 2 | (a) `geteilt.rs:1166` — beide | (b) `geteilt.rs:1416` |
| `K009` | 2 | (b) `kosten.rs:1363` — beide | (a) `kosten.rs:1290` |

### C — gegenseitige Deckung **strukturell unmöglich**: **8 von 20**

Weniger als zwei Proben. Ohne zwei Proben kann keine die andere decken.

| Proben | Kennungen |
|---:|---|
| 0 | `P022`, `P023` |
| 1 | `O001`, `O006`, `N023`, `P035`, `R010`, `F005` |

**9 + 3 + 8 = 20.** ✓

## Was geheilt wurde: `P034`

Der im Ordner ausgeschriebene Fall, und der einzige hier geheilte.

| | vorher | nachher |
|---|---|---|
| `parse.rs:213` — fehlender Auffangzweig | `P034` | `P034` |
| `parse.rs:501` — verirrtes `pub` | `P034` | **`P041`** |
| `beispiele/gift/05-auffangzweig` | `erwartet: P034` | `erwartet: P034` |
| `beispiele/gift/45-pub-wo-es-nicht-steht` | `erwartet: P034` | **`erwartet: P041`** |

Mitgezogen: `crates/gabbro-check/tests/korpus.rs` (`P041` in `BENANNT`), `TODO.md`, `DONE.md`.
`crates/gabbro-syntax/tests/sprechprobe.rs` prüft den Auffangzweig und **bleibt** bei `P034` —
richtig so, das ist die Regel, die `P034` behält.

**Beide Ratschen sind daraufhin GEFALLEN:** `MARKE` 20 → **19**, `MARKE_PROBEN` 61 → **59**.

## Was NICHT geheilt wurde, und warum

Die acht übrigen aus Gruppe A stehen weiter offen. **Der Grund ist keine Aufwandsfrage:**

1. **`E008` (vier Stellen) und `R009` (fünf Stellen) sind keine Buchungsfrage.** Sie zu
   trennen hieße, drei bzw. vier neue Kennungen zu erfinden — und damit zu *entscheiden*, was
   hier eine Regel ist. `messung/PHASENKLASSE.md` hat für `R009` ausdrücklich die
   Gegenrichtung entschieden (die Zugriffsverletzung benutzt `R005`/`R006` wieder, statt eine
   Kennung zu erfinden, *weil es dieselbe Regel mit anders nachgeschlagener Klasse ist*).
   **Das hier zu überschreiben wäre kein Heilen, sondern ein zweites Urteil ohne neue
   Messung.**
2. **Der Umfang, nicht die Prüfbarkeit.** ~~Es gibt keinen Übersetzer.~~ Den gibt es —
   lokal, und `cargo test` ist grün gelaufen. **Was bleibt, ist die Zuordnung:** sie ist
   *gelesen*, nicht gefahren, und eine Trennung ist nur so lange durch Lesen nachprüfbar,
   wie sie eine Quellzeile, eine Probenzeile und eine Testliste umfasst. **Acht davon über
   acht Dateien und rund dreißig Proben sind es nicht** — dort trüge jede einzelne
   Zuordnung, die ich falsch gelesen habe, eine Probe auf eine Regel, die sie nicht prüft.
   *Grün wäre das trotzdem.*

**Gruppe B (3) und Gruppe C (8) sind hier ausdrücklich NICHT zu heilen** — bei ihnen deckt
keine Probe eine andere. Ihr Befund ist ein anderer und gehört nicht in diesen Posten: bei
Gruppe B fehlt eine Probe, bei Gruppe C fehlen zwei.

## Die Fehlerrichtung dieser Messung

* **Sie ist gelesen, nicht gelaufen.** Ohne `cargo` konnte keine Probe gefahren werden. Die
  Zuordnung Probe → Vergabestelle folgt aus der Bedingung, die der Probentext wörtlich
  herstellt, und aus dem Code an der Vergabestelle. *Wo eine Probe mehrere Absagen auslöst
  (bei `139` ist das der Fall), ist die genannte Stelle die erste.*
* **Sie erbt die Fehlerrichtungen von `pruefe-vergabe.py`.** Dessen Grundgesamtheit sind die
  20 Kandidaten; **22 Kennungen stehen in den Quellen und in keinem Absagekonstruktor** und
  kommen hier gar nicht vor. Über sie sagt auch dieses Dokument nichts (W10).
* **Sie spricht nichts frei.** Eine Kennung in Gruppe B oder C ist nicht in Ordnung — sie ist
  nur nicht *dieser* Befund.

## Belegt durch

```
./instrumente/pruefe-vergabe.py            vor:  20 Kandidaten, 61 von 308 Proben
./instrumente/pruefe-vergabe.py            nach: 19 Kandidaten, 59 von 308 Proben
./instrumente/pruefe-kennungen.py          ALL PASS -- 239 vergeben, jede genau einer Datei
./instrumente/pruefe-saetze.py             45 von 239 ohne Satz -- die Ratsche HAELT
cargo test --quiet                         RC=0, 0 failed
```

**`P041` trägt seinen Satz** (`parser.pub-nur-wo-die-grammatik-es-fuehrt`) — ohne ihn wäre
die Ratsche `Kennungen ohne Satz` von 45 auf 46 gestiegen, und eine Ratsche steigt nicht.
