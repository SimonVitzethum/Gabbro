# Memo: Gleitkomma — der Preis ist eine zweite Faktenlogik, und der Bedarf ist null

> **Stand 2026-08-18.** Ein Memo mit Bedarfszählung, kein Bau. *Der Ordner baut nichts, dessen
> Bedarf er nicht gemessen hat (W3), und dies ist die Messung.*

---

## 1. Was bricht — und es ist nicht die Arithmetik

Intervallarithmetik über IEEE-754 ist gebaut, bekannt und teuer, aber nicht neu. **Was in
Gabbro bricht, ist die NEGATION einer Vergleichsbedingung.**

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

## 5. Und „nur auf der GPU" ist keine Erweiterung, sondern eine Ablesung

Was ein Renderer selbst ausrechnen müsste — Transformationsmatrizen — rechnet die GPU im
Shader. **Der Shader ist Gastcode**, also dieselbe Konstruktion wie der JIT: `entrust`,
Isolation statt Beweis. *Dafür ist seit heute ein Wort da, und es braucht keinen Zahlentyp.*

---

## Beschluss

**Nicht bauen.** Drei Gründe, in dieser Reihenfolge:

1. Der Bedarf ist **gemessen null** an 139 Dateien eines echten Mikrokernels.
2. Was tatsächlich gebraucht wird — eine Nachkommastelle — ist **heute schreibbar**.
3. Der Preis ist eine **zweite Faktenlogik**, und die zahlt jede Verengung mit, auch die, die
   nie eine Gleitkommazahl sieht.

**Was stattdessen zu tun ist:** die ABI-Frage aus §4 in der Bibliotheks-ABI führen. *Sie
besteht auch dann, wenn Gabbro nie eine Gleitkommazahl kennt* — denn der Gast, dem `entrust`
den Raum gibt, kann eine haben.
