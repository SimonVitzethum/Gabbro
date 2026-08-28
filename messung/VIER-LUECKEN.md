# «B6», «B14», «B12», «B31» — vier Einträge, ein Bau

*Gemessen am 2026-08-28, Bahn B, Schritt B3. **Drei der vier Einträge sind veraltet, und der
vierte steht seit acht Tagen als entschieden da.** Was übrig bleibt, ist ein Tor im
Rumpfkanal — und das Modell trug es schon.*

---

## 1. Der Befund: eine Probe, vier Fragen

Alle vier Formen in **einer** Datei, durch den **unveränderten** Prüfer:

```gab
-- «B6»
impl fn doppelt(x : Klein) -> u32   ensures result == x + x  … { return x + x; }
-- «B31»
impl fn senke(b : ptr<normal, rw> B, i : index into B)
    ensures b.slots[i].zaehler <= old(b.slots[i].zaehler) … { if … { … -= 1; } }
-- «B14», an drei Stellen: Parameter, `let`, Rückgabe
impl fn setze_elter(…, p : option index into B) … { b.slots[i].elter = p; }
impl fn lies_elter(…) -> option index into B … { let e : option index into B = …; return e; }
```

```bash
ssh ki-pc-fisch-101 'cd gabbro-B && ./target/debug/gabbro pruefe w24-b3.gab'
# w24-b3.gab: 9 Items, 0 Fehler, 0 Hinweise
```

**Null Fehler.** `result`, `old(place)` und `option index into B` als Parameter-, `let`- und
Rückgabetyp stehen alle drei in der Sprache.

> **Der erste Anlauf meldete vier Fehler, und alle vier waren meine.** `x + x` verlässt die
> Breite von `u32` (`M104`), und `zaehler -= 1` braucht die Wache im RUMPF, weil `M1` Rümpfe
> prüft und keine Prädikate — ein `requires` reicht ihm nicht. *Eine Probe, deren eigene
> Zahlen nicht aufgehen, misst die Probe und nicht die Sprache.*

### 1.1 «B6» — und `PFLICHTEN.md` widerspricht sich selbst

| Zeile | was dort steht |
|---|---|
| **176** | *„gap: «B6» — `fndecl` binds no name for it; `old(place)` exists, a **`result` does not**"* |
| **291** | *„`P(a: …, b: …)` + `ensures result` — **both closed**; **«B6» was already**, «B7» on 2026-08-17"* |

**Dieselbe Datei, zwei Zeilen, entgegengesetzte Auskunft.** Und der Korpus entscheidet:
`result` steht an **acht Stellen** (`06-annahmen`:115, `03-format`:86, `39-auftragsdienst`:115,
`22-bootstrecke`:80, `41-handschlag`:101, `udp-echo`:84, `F10`:31, `F06`:140), und `primary`
trägt es seit langem (`SYNTAX.md`:572). **Zeile 176 ist die veraltete.**

### 1.2 «B31» — `old` hängt längst unter `primary`

Der Eintrag sagt: *„`old` hängt unter `atompred`, nicht unter `primary`. Keine
Differenzaussage schreibbar."* `SYNTAX.md`:572 trägt `oldexpr` in `primary`, und `SYNTAX.md`:41
führt genau diesen Fehler als **behoben** auf:

> **`old(x)` hung under `atompred` instead of under `primary`** — it could stand as a
> predicate on its own, but could occur in **no expression**, hence never next to `==`.

Die Probe oben schreibt `b.slots[i].zaehler <= old(b.slots[i].zaehler)` und geht durch.
**«B31» ist in der Sprache geschlossen.**

### 1.3 «B12» — entschieden, und die Zeile stimmt noch

```bash
grep -n 'decided 2026-08-20' dokumente/SYNTAX.md
# 691:  | "elems" "of" place  (* «B12», decided 2026-08-20: binds an INDEX into the array *)
```

Die Zeile steht, mit dem ausgeschriebenen Grund darunter: *„aus dem Index bekommt man das
Element, aus dem Element den Index nicht"*, und dem tragenden Beispiel
`forall i in elems of dst.msg : dst.msg[i] == old(src.msg[i])`. **Nichts zu tun, und der
Auftrag hat genau danach gefragt.**

### 1.4 Und was übrig bleibt, steht im RUMPFKANAL

Dieselbe Probe durch die beiden Lean-Kanäle:

```bash
ssh ki-pc-fisch-101 'cd gabbro-B && ./target/debug/gabbro lean w24-b3.gab | grep @program'
#   @program 1  units 1  routines 4  bodies 4  refused 0     <-- «B14» wird GETRAGEN
ssh ki-pc-fisch-101 'cd gabbro-B && ./target/debug/gabbro pflichten --lean w24-b3.gab'
#   old-state (1): `old(x)` -- a predicate over TWO states
#   result-in-ensures (1): `result` in an `ensures` -- one gate away, not far
```

**«B14» ist auch im Modell fertig** — vier Rümpfe, null Absagen. **«B6» und «B31» sind es
nicht**, und die beiden haben verschiedene Preise.

---

## 2. Zwei Formen für «B6», beide Seiten je Form

### Form 1 — `result` wird eine Form des `Expr`

`Expr` bekommt `.result`, und `eval` bekommt den Rückgabewert als zweiten Parameter.

* **Dafür:** `result` steht dann im Ausdruck, wo es syntaktisch steht.
* **Dagegen:** `eval` hat **sieben** Aufrufstellen im Modell und steht in jeder erzeugten
  Zeile; einen Parameter anzuhängen ändert jeden Satz, auch jeden über einem Rumpf ohne
  `result`. **Und es wäre eine Erfindung:** ein `result` ist im Ausdruck von einem Namen
  nicht zu unterscheiden, und das Modell hat Namen.

### Form 2 — `result` ist ein NAME, gebunden an den zurückgegebenen Wert

Der Satz bindet ihn vor der Auswertung: `eval { s' with local' := bindLocal s'.local' "result" v }`.

* **Dafür:** **keine Zeile des Modells ändert sich.** `finalValue` steht seit dem ersten Tag
  da, und seine eigene Doku-Zeile sagt wofür: *„For an `ensures` that names `result`."*
  `bindLocal` gibt es, Parameter werden schon so gelesen. Und `result` ist ein
  **reserviertes Wort**, also kann die Bindung nichts verdecken, was ein Rumpf geschrieben hat.
* **Dagegen:** der Satz sieht anders aus als die anderen — er hat drei Konjunktionsglieder
  statt zwei. *Das ist kein Schönheitsfehler, sondern die Aussage:* der Rumpf muss einen Wert
  **erzeugt** haben.

---

## 3. Die Entscheidung, und ihr Grund ist ein Begriff

**Form 2 für «B6». «B31» wird benannt abgesagt.**

> **`result` ist ein Name für den zurückgegebenen Wert, und ein Modell, das Namen hat, braucht
> für einen Namen keine neue Form.** Was fehlte, war nie die Schreibweise — sie steht in
> `primary` — sondern die **Bindung**: eine Nachbedingung wird über einem `State` ausgewertet,
> und ein Ergebnis gehört keinem. Der Satz bindet es, und damit ist die Lücke da geschlossen,
> wo sie wirklich lag.

Und der Satz wird dabei **strenger**, nicht bequemer:

```lean
: ∃ s' v, finalState (exec ρ body s) = some s'
    ∧ finalValue (exec ρ body s) = some v
    ∧ eval { s' with local' := bindLocal s'.local' "result" v } post = some (.bool true)
```

**Das mittlere Glied ist die neue Hälfte.** Ein Rumpf, der hinten hinausläuft, hat kein
Ergebnis — `finalValue` ist dort `none` —, und ein Satz ohne dieses Glied hätte die Zusage
einer Routine bewiesen, die nie eine macht. *Gemessen in beide Richtungen, drei Fälle:*

| | |
|---|---|
| Rumpf gibt 5, Zusage sagt 5 | **geht durch** |
| Rumpf gibt 5, Zusage sagt 6 | **fällt auf `⊢ False`** |
| Rumpf gibt **nichts**, Zusage spricht über `result` | **fällt auf `⊢ False`** |

**«B31» bleibt abgesagt, und die Absage ist das Ergebnis.** `old(x)` ist ein Prädikat über
ZWEI Zuständen; alles hier spricht über einen. Der Satz müsste den Eintrittszustand mitführen,
und jede Nachbedingung müsste über einem Paar ausgewertet werden. **Gemessener Bedarf im
Register: null** (`old-state 0`). Die acht `old`-Fundstellen des Korpus sind zu fünf
`exchange … when old(X)` — die atomare Vergleichsform, keine Differenzaussage — und zu drei
Fragmentzeilen (`F01`:262/263, `F03`:132), die dieser Kanal aus anderen Gründen nicht liest.
*Regel A: kein Konstrukt ohne gemessenen Bedarf.*

---

## 4. Was die Entscheidung NICHT kauft

* **Sie schließt «B6» nicht in der Sprache** — dort war es schon zu. Sie schließt es im
  **Rumpfkanal**, und das ist ein Ziel mehr, nicht acht. *Sieben der acht Korpusstellen
  stehen an einem `extern fn` oder hinter einer anderen Absage;* `03-format :: kopf_lesen`
  ist die eine, die heute ankommt.
* **Sie modelliert `old` nicht.** Eine Differenzaussage bleibt unschreibbar für diesen Kanal,
  und der Eintrag «B31» bleibt in `PFLICHTEN.md` stehen — mit dem Zusatz, dass er die SPRACHE
  meint und nicht mehr trifft, und den Rumpfkanal meint und dort weiter zutrifft.
* **Sie sagt nichts über den Programmexport.** Dort bleibt `result` bewusst aus: die
  `post`-Liste ist, was ein RUFER annehmen darf, und ein Rufer liest das Ergebnis an seiner
  eigenen Rufstelle. *Eine Zusage weniger macht das Ziel des Rufers schwerer, nie falsch* —
  dieselbe Richtung wie eine fallengelassene Vorbedingung, gespiegelt.
* **Und sie räumt drei Einträge ab, ohne eine Zahl zu heben.** «B6», «B14» und «B31» waren in
  der Sprache erledigt, «B12» seit dem 2026-08-20 entschieden. *Eine Zahl, die durch eine
  Berichtigung fällt, ist keine Arbeit* (§1.8) — was hier fällt, ist die Zahl der offenen
  Einträge, und das ist die einzige, die fällt.
