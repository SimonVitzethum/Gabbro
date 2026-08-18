# Memo: Gleitkomma — der Preis ist eine zweite Faktenlogik, und der Bedarf ist null

> **Stand 2026-08-18.** Ein Memo mit Bedarfszählung, kein Bau. *Der Ordner baut nichts, dessen
> Bedarf er nicht gemessen hat (W3), und dies ist die Messung.*

---

## 1. Was bricht — und es ist nicht die Arithmetik

**Berichtigt 2026-08-18.** Die erste Fassung dieses Abschnitts las sich, als sei Gleitkomma
schwer zu verifizieren. *Das ist falsch, und die Berichtigung gehört an den Anfang.* IEEE 754
ist eine **vollständig deterministische** Spezifikation: jede Basisoperation liefert bei
festem Rundungsmodus genau ein Bitmuster. Gleitkommazahlen sind logisch nicht schwerer als
Bitvektoren — sie sind Bitvektoren mit einer unhandlichen Interpretationsfunktion.

Verifiziert wird auf einer von zwei Ebenen, beide gebaut und im Einsatz:

| | |
|---|---|
| **bitgenau** | SMT-LIB führt seit 2014 eine `FloatingPoint`-Theorie (Z3, CVC5, MathSAT). Intern meist Bit-Blasting; eine 64-Bit-Multiplikation wird ein brutaler Schaltkreis. Gut für *kein NaN, kein Überlauf*, schlecht für *numerisch korrekt* |
| **reell + Fehlerschranke** | `fl(x ∘ y) = (x ∘ y)(1+δ)` mit `|δ| ≤ u` — Gappa, Flocq, FPTaylor, Daisy, PRECiSA. Skaliert besser und liefert die Aussage, die man eigentlich will |

Und die Belege sind industriell, nicht akademisch: Russinoff hat AMDs Division und Wurzel in
ACL2 verifiziert (nach dem FDIV-Fehler), Harrison dieselbe Klasse bei Intel in HOL Light,
CompCert beweist Semantikerhaltung **einschließlich** Gleitkomma auf Flocq, Astrée weist
Laufzeitfehlerfreiheit in Flugsteuerungscode nach, der fast nur aus Gleitkomma besteht, und
NASAs PRECiSA verifiziert DAIDALUS mit realer Gleitkommasemantik.

> **Schwer ist nicht die Ausführung, sondern die SPEZIFIKATION.** Bei Ganzzahlen ist korrekt
> meist offensichtlich; hier braucht es zwei Semantiken — reell und Maschine — plus die
> Relation dazwischen.

Was in **Gabbro** bricht, ist damit keine Aussage über Gleitkomma, sondern eine über M1:
**die NEGATION einer Vergleichsbedingung.**

Ist ein Operand `NaN`, sind *alle* Vergleiche falsch — `x < y`, `x >= y`, `x == x`. Damit gilt
nicht mehr:

```
!(x < y)   ⟹   x >= y
```

`m1::fakten_aus(…, negiert = true)` wäre unsicher. **Das ist die Maschinerie, mit der jede
Verengung in dieser Sprache arbeitet:** `if x < n { … } else { … }` gewinnt im `else`-Zweig
das Faktum `x >= n`, und darauf ruhen die Indexschranke, die Überlaufregel und jedes `narrow`.

> Ein Zahlentyp, der die Negation eines Vergleichs ungültig macht, ist **keine Erweiterung des
> Zahlbereichs, sondern eine zweite Faktenlogik neben der ersten.**

Zwei Auswege, beide teuer:

| | |
|---|---|
| **`NaN` durch Konstruktion ausschließen** | eine Laufzeitprüfung an jeder Erzeugung — und W6 verlangt, dass eine entfernte Prüfung M1-begründet ist, nicht gehofft |
| **die Negation kein Faktum liefern lassen** | sicher, und dann **ungeprüft genau dort, wo man prüfen wollte** |

---

## 1a. Die Landminen — und eine davon liegt im eigenen Ordner

| | |
|---|---|
| **Nicht-Assoziativität** | `(a+b)+c ≠ a+(b+c)`. Jede Umsortierung durch einen Übersetzer ist unsound; `-ffast-math` ist im verifizierten Kontext tot, und parallele Reduktionen sind nur mit **expliziter Reihenfolge** deterministisch |
| **libm** | IEEE 754 fordert für `sin`, `exp`, `log` **keine** korrekte Rundung (2019 empfiehlt sie nur). Die Verifikation endet am libm-Rand, sofern man nicht axiomatisiert oder selbst verifiziert |
| **Rundungsmodus** | MXCSR/FPCR ist ein **impliziter Eingang jeder Operation** und damit kompositional giftig. Fast alle Beweise pinnen round-to-nearest-even und verifizieren das Pinnen separat |
| **Excess precision** | x87 mit 80 Bit und Doppelrundung — der Grund, warum CompCert auf x86 SSE2 voraussetzt. `FLT_EVAL_METHOD` ignoriert zu lassen ist ein Loch |
| **NaN-Nutzlasten** | implementierungsdefiniert; bitgenaue Aussagen sind hier plattformspezifisch |

**Und die erste Zeile trifft eine BEWIESENE Schablone dieses Ordners.**

`accumulates.monoid` ist bewiesen — *unter der Prämisse, dass die Merge-Menge ein kommutatives
Monoid ist.* Der Eintrag sagt, warum diese Prämisse mechanisch prüfbar ist: **der Wortschatz
ist geschlossen** (`max`, `min`, `add`, `or`, `and`). Mit einem Gleitkommatyp wäre das nicht
mehr genug:

```
merge add   ueber f64   ->  NICHT assoziativ, das Monoid faellt
merge max   ueber f64   ->  NaN vergleicht sich mit nichts
```

`faltung_ist_reihenfolgeunabhaengig` ruht auf `assoz` und `komm`. **Der Satz bliebe wahr und
seine Prämisse würde falsch** — und die Absenkung faltet die Kernzellen in einer Reihenfolge,
die niemand festlegt. *Das ist genau die Lage, für die Zahn 3 gebaut wurde: eine Prämisse, die
heute vom geschlossenen Wortschatz hergestellt wird und morgen von ihm allein nicht mehr.*

> **Ein Gleitkommatyp müsste `merge` also einschränken, mechanisch** — und dann lautet die
> Prämisse nicht mehr *der Wortschatz ist geschlossen*, sondern *der Wortschatz ist geschlossen
> UND alle Zahlentypen sind ganzzahlig*.

## 2. Die Bedarfszählung — gemessen, nicht geschätzt

Gezählt an der Messbasis (Caprock, Zweig `arch/x86_64`, schreibgeschützt gelesen):

```
139  Rust-Dateien im Kernel
  0  Stellen, die mit Gleitkomma RECHNEN
  2  Erwähnungen von `f32`/`f64` -- beide in KOMMENTAREN
```

**Und die erste Erwähnung verneint den Bedarf ausdrücklich** (`kernel/src/colors.rs:1156`):

> *„Der Kernel rechnet nirgends mit `f64`; die Zahl ist trotzdem nötig, weil die
> Ganzzahldivision auf Plattformen mit grobem Zähler sonst `0` liefert — und `0` ist keine
> Messgröße, sondern eine verlorene Aussage."*

Die eine Stelle, die eine Nachkommastelle braucht, löst sie als **`(Ganzzahl, Zehntel)`** —
*handgemachtes Festkomma.*

---

## 3. Und genau das kann Gabbro schon

Am selben Tag gemessen (`MESSUNGEN.md`, „Festkomma"): **M1 rechnet mit dem deklarierten
BEREICH, nicht mit der Typbreite.** Damit ist das Muster, das Caprock von Hand schreibt, in
Gabbro eine Deklaration:

```gabbro
type Q16 = i64 in -2147483648 .. 2147483647;
impl fn mal(a : Q16, b : Q16) -> i64 effects { pure } { return (a * b) >> 16; }
```

```c
int64_t mal(int64_t a, int64_t b) { return (a * b) >> 16; }
```

Keine Laufzeitprüfung — **der Bereich beweist sie weg.** Der Träger ist die Breite, der
Bereich ist die Zusage.

> **Was die Leute wollen, wenn sie „Gleitkomma" sagen, ist meistens eine Nachkommastelle.**
> Die gibt es, sie kostet keine zweite Faktenlogik, und sie ist heute schreibbar.

---

## 4. Der Nebenbefund, und er ist der teuerste: Gleitkomma ändert die ABI

`kernel/src/arch/x86_64/bringup.rs:463`, gemessen am 2026-08-09:

> *Dieselbe Funktion `f64 -> f64` übergibt ihre Argumente auf einem normalen x86_64-Ziel in
> `xmm0`/`xmm1`, auf `x86_64-caprock-user` dagegen in `rdi`/`rsi`. Das sind zwei
> Aufrufkonventionen. Ein upstream gebautes musl nimmt die erste an; der Linker sieht nur
> gleiche Symbolnamen und kann die Verwechslung nicht bemerken.*

**Stille Korruption, kein langsamer Code.** Das ist keine Aussage über Zahlen, sondern über
die **Absenkung** — und es trifft die Bibliotheks-ABI, die dieser Ordner ohnehin schuldet:
zwei Übersetzungseinheiten mit verschiedener Gleitkommaentscheidung reden aneinander vorbei,
und kein Zeugnis sagt es heute.

---

## 4a. Warum verifizierte Kernel Gleitkomma ausschließen — und es hat wenig mit Beweisen zu tun

Fast alle, seL4 eingeschlossen, halten Gleitkomma aus der TCB heraus: der Kernel wird
soft-float bzw. `-mgeneral-regs-only` übersetzt, FPU-Zustand ist **Kontext, nicht Rechnung**.
Drei Gründe, und **alle drei gelten unabhängig von Verifizierbarkeit**:

1. **Der Rundungsmodus ist vom Userspace kontrollierter globaler Zustand.** Man müsste ihn
   beim Kerneleintritt sichern und normalisieren.
2. **Lazy FPU switching hat eine eigene Leckklasse** — LazyFP, CVE-2018-3665.
3. **FP-Kontext im Kernel macht Preemption teurer.**

*Die Verifikationsersparnis ist Nebeneffekt, nicht Motiv.* **Das ersetzt eine Begründung
dieses Memos durch eine bessere:** nicht *weil es schwer zu beweisen wäre*, sondern weil der
Rundungsmodus fremder globaler Zustand ist und der Kontextwechsel eine Angriffsfläche hat.

## 4b. Wenn doch — dann gehört der Rundungsmodus in den TYP

Das ist die eigentliche Designfrage, und sie ist **von der Arithmetik unabhängig**. Ein
`f64<RNE>`, das sich mit `f64<RTZ>` nicht mischen lässt, beseitigt eine ganze Fehlerklasse
**strukturell — ohne einen einzigen Beweis über Zahlenwerte.**

**Und es wäre die vierte Instanz eines Musters, das dieser Ordner längst führt:**

| | |
|---|---|
| `ptr<normal, rw>` | Adressraum und Rechte stehen **am Typ**, nicht in Umgebungszustand |
| `atomic … seq` | die Ordnung steht **an der Deklaration**, nicht in einer Übersetzerschalterei |
| `format … endian big` | die Byteordnung steht **am Format** |
| `f64<RNE>` | der Rundungsmodus stünde **am Typ** statt in MXCSR |

Gemessen: `ptr<…>` ist **kein allgemeiner Typparameter**, sondern ein eigener Typkonstruktor
mit zwei geschlossenen Wortmengen (`space()`, `rights()`). *Genau diese Form hätte `f64<RNE>`
— und das Nichtmischen ist dieselbe Maschinerie, mit der `opaque` seit `5e9f31e` beißt.*

**Der Schritt danach ist eine andere Größenordnung:** Fehlerschranken im Typ (Rosa, Daisy)
hängen vom Eingangsbereich ab und verlangen faktisch Refinement-Types. *Das ist die
wertgetragene Schranke aus Punkt 1 noch einmal, eine Stufe schärfer.*

## 5. Und „nur auf der GPU" ist keine Erweiterung, sondern eine Ablesung

Was ein Renderer selbst ausrechnen müsste — Transformationsmatrizen — rechnet die GPU im
Shader. **Der Shader ist Gastcode**, also dieselbe Konstruktion wie der JIT: `entrust`,
Isolation statt Beweis. *Dafür ist seit heute ein Wort da, und es braucht keinen Zahlentyp.*

---

## Beschluss

**Die erste Fassung hat zwei Entscheidungen vermengt.** Sie sind zu trennen:

**(i) Gleitkomma-ARITHMETIK mit numerischen Zusagen — nicht bauen.**

1. Der Bedarf ist **gemessen null** an 139 Dateien eines echten Mikrokernels.
2. Was tatsächlich gebraucht wird — eine Nachkommastelle — ist **heute schreibbar**.
3. Der Preis ist eine zweite Faktenlogik in M1, und die zahlt jede Verengung mit, auch die,
   die nie eine Gleitkommazahl sieht. *Nicht, weil es unbeweisbar wäre — sondern weil die
   Spezifikation zwei Semantiken plus ihre Relation verlangt.*
4. Und ein Gleitkommatyp würde die Prämisse einer **bewiesenen** Schablone brechen (§1a).

**(ii) Der Rundungsmodus im TYP — die Entscheidung ist offen und billig.**

Sie kostet keinen Beweis über Zahlenwerte, sie ist die vierte Instanz eines vorhandenen
Musters, und sie hängt nicht daran, ob Gabbro je rechnet: **auch der Gast hinter `entrust`
hat einen Rundungsmodus, und heute sagt darüber niemand etwas.**

**Was stattdessen zu tun ist:** die ABI-Frage aus §4 in der Bibliotheks-ABI führen. *Sie
besteht auch dann, wenn Gabbro nie eine Gleitkommazahl kennt* — denn der Gast, dem `entrust`
den Raum gibt, kann eine haben.
