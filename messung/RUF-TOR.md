# Das kompositionale Ruf-Tor — und warum die Zahl davor eine andere war

*Gemessen am 2026-08-28, Bahn B, Schritt B1. **Der Schritt war als der größte Posten der
Bahn geplant und endet als Berichtigung** (§1.8) — mit einer echten Fehlübersetzung darin,
die niemand gesucht hat.*

---

## 1. Der Befund

`dokumente/PLAN-AUTONOM.md` schreibt zu B1:

> Heute: **17 `call-not-compositional`**, gewachsen von 11, weil die neuen `ops`-Rufe
> hineinlaufen. […] **Erwartete Wirkung:** 17 Absagen fallen, und die Rumpfdeckung steigt
> von 89 auf ~106 von 181.

Die 17 stimmen. **Was nicht stimmt, ist, dass sie Rufe sind.**

```bash
# Der Befehl aus dem Plan, unveraendert -- der PROGRAMMkanal:
ssh ki-pc-fisch-101 'cd gabbro-B && for f in beispiele/*.gab messung/*/*.gab; do
    ./target/debug/gabbro lean "$f" 2>/dev/null; done \
  | grep -oE "^-- REFUSED  [^ ]+  \([a-z-]+\)" | grep -oE "\([a-z-]+\)" | sort | uniq -c | sort -rn'
#      92 (foreign-body)
#      24 (loop)
#      17 (call-not-compositional)   <-- der Posten
#      13 (carrier-not-a-table)
#       …
```

**Und der zweite Kanal, den der Plan gar nicht misst** — der PFLICHTENkanal, in dem das Tor
sitzt, das B1 bauen wollte:

```bash
ssh ki-pc-fisch-101 'cd gabbro-B && ./instrumente/zaehle-lean.py'
# == BODY CHANNEL: 70 obligations, 4 goals, 66 refused ==   <-- Stand 2026-08-28
#    call-not-compositional     1
# nachgemessen 2026-08-30: 75 obligations, 9 goals, 66 refused
#    call-not-compositional     1   <-- unveraendert
```

**Eine.** Nicht siebzehn. Die siebzehn stehen im Programmkanal, und dort ist das Tor
**seit dem Bau offen**: `routines()` setzt `allow_calls: true` (`lean.rs`:1596), `stmt_term`
schreibt `.call`, `.bindCall` und `.retCall`, und `Body.lean` trägt alle drei als
`Stmt`-Konstruktoren. *Die Erzeugerseite, die der Plan als fehlend führt, steht.*

### 1.1 Was die siebzehn wirklich sind

Nachgerechnet Routine für Routine, an der Quelle:

| Zahl | was dort steht | Beispiel |
|---:|---|---|
| **6** | ein Ruf einer **erzeugten Tabellenoperation** | `Verzeichnis::insert(v, i)` (`47-ops-wortmenge`) |
| **6** | ein **Konstruktor** — Verbund oder Gerätegriff | `return Completion(id: k, len: n);` (`21`) · `let g : Dma = Dma(GERAETEBASIS);` (`40`) |
| **4** | ein **`transition`** eines `device` — ein Registerschreiben | `anerkennen(g)` (`virtio-net`:45) |
| **1** | **`return Some(i);`** | `27-freiliste :: belegen` |
| **0** | ein Ruf einer Gabbro-Routine über ihren Vertrag | — |

**Kein einziger.** Das Tor, das B1 bauen wollte, hätte im Programmkanal null Absagen
genommen.

> **Die erste Auszählung stand hier ~~5 `transition` / 2 Gerätegriff~~ und war um eins
> daneben** (berichtigt 2026-08-28 nach dem Bau). `09-ohne-zeiger :: scharfschalten` trägt
> BEIDES — `let v = Vtd(basis);` und danach `wurzel_setzen(v)` — und wird an der ersten Tür
> abgesagt, die es trifft. *Eine Routine steht unter EINEM Grund, auch wenn zwei auf sie
> zutreffen*, und das ist der Grund, warum die Zahlen je Grund kleiner sind als die Zahl der
> Stellen. Nachgerechnet wird es am Werkzeug, nicht an dieser Zeile.

`call_parts` (`lean.rs`:616) sagt fünf verschiedene Dinge mit einem Wort ab: das Tor selbst,
einen fehlenden Pfad, einen Gerufenen, der nicht in `callees` steht, und eine Stelligkeit,
die nicht passt. **Der dritte Fall ist der Sammeltopf** — in ihm landet alles, was
syntaktisch wie ein Ruf aussieht und keine `fn`-Deklaration hat: Operationen, Übergänge,
Konstruktoren. *Genau die Klasse, die dieselbe Datei drei Absätze weiter oben selbst bucht:*

> „**A refusal filed under the wrong reason names a missing form where a missing translation
> stands**" — der `Carrier`/`FieldShape`-Riss, `lean.rs`:113.

### 1.2 Und die eine echte Stelle trägt es auch nicht

Die eine Absage des Pflichtenkanals ist `beispiele/01-tabelle.gab :: blatt_loeschen ::
ensures #1`, und ihr Rumpf ruft `aushaengen(c, s)` — **eine echte Gabbro-Routine.** Also die
Probe, mit dem unveränderten Prüfer bis auf eine Zeile:

```bash
# lean.rs:1119   allow_calls: false   ->   allow_calls: true
ssh ki-pc-fisch-101 'cd gabbro-B && ./instrumente/zaehle-lean.py'
# == BODY CHANNEL: 70 obligations, 4 goals, 66 refused ==     <-- unveraendert
#    (Stand 2026-08-28; am 2026-08-30 sind es 75 / 9 / 66)
#    call-not-compositional     0
```

**Vier Ziele vorher, vier Ziele nachher.** `duty_8` wandert von `call-not-compositional`
nach `no-shape-for-field` — der Ruf war nie die bindende Schranke, das Feld `art` ist es,
und dahinter steht noch ein `match` über einem `tagged`. *Das Tor zu öffnen kauft im
Pflichtenkanal exakt null Ziele.*

> **Und es wäre nicht einmal ungefährlich.** Ein offenes Tor ohne Vertragshypothese schreibt
> `∃ s', finalState (exec ρ body s) = some s' ∧ …` unter einem **allquantifizierten `ρ`** —
> eine Aussage über *jede* Umgebung, also über einen Gerufenen, der alles tun darf. Sie ist
> nicht falsch, sie ist unbeweisbar; und `pruefe-lean-beweis.sh` färbt jedes Modul rot, dessen
> Ziel nicht durchgeht. *Dass heute kein Ziel entstand, ist ein Zufall des Korpus und keine
> Zusage.*

---

## 2. Zwei Formen, beide Seiten je Form

### Form 1 — das Vertragstor bauen, wie der Plan es beschreibt

`Body.lean` bekäme eine `Contract`-Struktur (`pre`, `post`) und ein `Honours ρ κ`, der
Abstieg prüfte die Vorbedingung am Rufort und bliebe **stecken**, wo sie nicht gilt — womit
sie zum Beweisziel würde, weil die starke Form ein Ende des Rumpfs verlangt.

* **Dafür:** es ist die richtige Form, sie steht sauber im Modell, und die Vorbedingung wird
  ohne einen zweiten Konjunktionsteil zum Ziel. Sie ist die Form, die der Kanal irgendwann
  braucht.
* **Dagegen:** `step` und `exec` bekämen einen weiteren Parameter, und damit ändert sich
  **jedes erzeugte Modul und `programmlogik/beispiel/Spec.lean`** — auch die von Rümpfen ohne
  jeden Ruf. Gemessener Ertrag heute: **null Ziele, null Rümpfe.** Regel A sagt dazu das,
  wofür sie dasteht.

### Form 2 — den Sammeltopf aufteilen und die Fehlübersetzung heilen

`call-not-compositional` behält seinen Namen für einen **wirklichen** Ruf; die vier anderen
Dinge bekommen je einen eigenen. Und `return Some(i);` läuft dorthin, wo es hingehört.

* **Dafür:** das Register sagt danach die Wahrheit, und die Wahrheit ist **teilbar**: sechs
  Stellen warten auf die `ops`-Schablone als Vertrag (das ist B4s Nachbarschaft), fünf auf
  ein Hardwaremodell (also nie), sechs auf eine Verbundform im `Value`. *Drei verschiedene
  Preise, die heute unter einer Zahl liegen.* Und `27-freiliste :: belegen` bekommt einen
  Rumpf, den das Modell die ganze Zeit tragen konnte.
* **Dagegen:** es baut das Tor nicht. Wer nur die Überschrift liest, sieht eine Zahl fallen
  und hält sie für Deckung — deshalb steht §4 dieses Dokuments da.

---

## 3. Die Entscheidung, und ihr Grund ist ein Begriff

**Form 2. Das Vertragstor wird NICHT gebaut, und der Grund ist nicht der Preis.**

> **Ein Vertrag ist eine Hypothese über einen Gerufenen — und keiner der siebzehn Rufe hat
> einen Gerufenen mit Vertrag.** Eine erzeugte Operation hat eine **Schablone**, ein
> `transition` hat ein **Register**, ein Konstruktor hat eine **Form**. Das sind drei andere
> Begriffe, und keiner von ihnen wird von einem `requires`/`ensures`-Paar getragen. Ein Tor,
> das sie alle durchließe, hätte den Vertrag zu einem Wort für „irgendetwas ist bekannt"
> gemacht.

Das ist dieselbe Unterscheidung, die `lean.rs` schon zwischen `Carrier` und `FieldShape`
zieht, und dieselbe, die `Body.lean` zwischen `.call` und `.loop` zieht, obwohl beide
dasselbe `Env` befragen: **wovon man etwas weiß, entscheidet, was man annehmen darf.**

Gebaut wird darum:

1. `Some(e)` und `None` in Anweisungsstellung laufen über `expr_term` statt über
   `call_parts`. **Eine echte Fehlübersetzung** — `.someOf` und `.absent` stehen seit dem
   ersten Tag im Modell, und der `let`/`return`-Zweig hat sie nie erreicht.
2. Drei neue Absagegründe — `generated-op`, `device-transition`, `constructed-value`.
3. `call-not-compositional` bleibt und liest danach die ehrliche Zahl.

---

## 4. Was die Entscheidung NICHT kauft

* **Sie baut das Vertragstor nicht.** Es fehlt weiter, und der Tag, an dem der Korpus einen
  Ruf einer Routine mit `ensures` in einem Rumpf trägt, den dieser Kanal sonst tragen könnte,
  ist der Tag, an dem es gebaut gehört. Heute gibt es diese Stelle nicht.
* **Sie senkt keine Absage, die auf ein Modell wartet.** Die sechs `constructed-value` und
  die fünf `device-transition` stehen danach genauso da wie vorher — nur unter ihrem Namen.
  *Eine Zahl, die durch eine Berichtigung fällt, ist keine Arbeit* (§1.8), und die
  siebzehn fallen hier nicht, sie werden aufgeteilt.
* **Sie sagt nichts über `blatt_loeschen`.** Dessen Pflicht bleibt abgesagt; sie hängt nach
  dem Ruf an `no-shape-for-field` und danach an einem `match` über einem `tagged`. **Drei
  Türen hintereinander, und B1 hat auf die erste gezeigt.**
* **Und sie kauft keine Rumpfdeckung im zweistelligen Bereich.** Der Plan erwartete 89 → ~106
  von 181. Gemessen: **89 → 90.** Ein einziger Rumpf kommt dazu — `27-freiliste :: belegen`.
  *Die erwartete Wirkung war die Zahl des Sammeltopfs, nicht die des Tors.*

---

## 5. Gemessen, nachher

```bash
ssh ki-pc-fisch-101 'cd gabbro-B && for f in beispiele/*.gab messung/*/*.gab; do
    ./target/debug/gabbro lean "$f" 2>/dev/null; done \
  | grep -oE "^-- REFUSED  [^ ]+  \([a-z-]+\)" | grep -oE "\([a-z-]+\)" | sort | uniq -c | sort -rn'
```

| | vorher | nachher |
|---|---:|---:|
| `call-not-compositional` (Programmkanal) | 17 | **0** |
| `generated-op` | — | 6 |
| `constructed-value` | — | 6 |
| `device-transition` | — | 4 |
| Rümpfe | 89 | **90** |
| `call-not-compositional` (Pflichtenkanal) | 1 | **1** |
| Ziele (Pflichtenkanal) | 4 | 4 |

> **Nachgezogen am 2026-08-30:** die Bilanzzeile lautet heute **75 Pflichten, 9 Ziele,
> 66 abgesagt** — ~~70 · 4 · 66~~. Die Absagen sind gleich geblieben, Register und
> Ziele nicht: dazwischen liegen Bahn Bs vier Tore und drei geheilte Erzeugerfehler.
> **Der Satz dieses Berichts steht unverändert** — `call-not-compositional` steht weiter
> auf 1, und das Öffnen des Tores kauft weiter null Ziele
> (`messung/RUMPFKANAL-ABSAGEN.md` §4.1). *Eine Zahl, die durch eine Berichtigung fällt,
> ist keine Arbeit* (§1.8).

**6 + 6 + 4 + 1 = 17.** Die Bilanz geht auf, und die einzige Zahl, die sich bewegt hat, ist
die Rumpfdeckung um eins. *Alles andere war ein Name.*
