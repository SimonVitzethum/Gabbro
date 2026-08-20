# Toolbox — working rules this folder earned

**Admission condition:** a rule gets in here only if it comes from a **mistake in this folder**
and the mistake is named. No good intentions, no borrowed wisdom. Whoever reads a rule should
be able to see the damage it was paid for.

> The **trap** numbering (`Falle 80` …) lives in
> [`fallen-klassifikation.tsv`](../fallen-klassifikation.tsv) — 100 paid-for Caprock traps, source
> `CLAUDE.md`, as of 2026-08-13. That file is a **measured inventory with a named source**;
> nothing is added to it after the fact. The `W` numbers here are our own and stand beside it,
> not inside it.
>
> `Falle 80` reads there, literally: *a number a human runs parallel to the truth* (class `S`,
> `ableitung`). **W1 and W2 below are both children of that trap** — once in the instrument,
> once in the declaration.

---

## W1 — A coverage number counts evidence, not attempts

*Next to trap 80: a number a human runs parallel to the truth.*

**The damage.** On 2026-08-14 the checker grew by five rules, and I wrote five mutations to go
with them. The summary line printed `37 of 37` — from `len(MUTATIONEN)`, i.e. from the number
of **written** mutations. At the same time an older mutation (`sperre-egal`) had lost its
anchor because I had rebuilt the line it targeted. It did not run at all. **A dead mutation
counted as coverage.**

**Why that is worse than an unchecked rule.** A hole you know about is an item. A coverage
number that counts holes as coverage **devalues every other number in the folder** — because it
is the number you check the others with. It is the wished-for form *inside the instrument*.

**The rule.** Every coverage, completeness or progress number is formed from **verified
evidence**, never from the number of attempts, entries or lines. Where a piece of evidence can
drop out (dead anchor, skipped probe, unbuilt surface), the dropout must **lower** the number,
not leave it untouched.

**The handle.** `mutiere-pruefer.py` now counts `caught` out of `valid`; a lost anchor appears
as `ANKER FEHLT` and **falls out of the denominator, not into the numerator**.

---

## W2 — The zero promise: the checker is the instrument for the numbers it checks

**The occasion.** For a new example I needed three `costs` lines. Instead of estimating them I
pushed them down to `1 ops`, let the checker name the true numbers (`4`, `2`, `2`) and entered
those. **The numbers fell out of the body, not out of the wish.**

**The relapse inside that.** The procedure was right, the handle was manual work — and manual
work on a number is exactly where a number starts running parallel to the truth. A procedure
that needs discipline is a procedure with an expiry date.

**The rule.** Where a pass **checks** a declared number, it must also be able to **name** it. A
promise is copied down, not guessed.

**The handle.** `gabbro kosten datei.gab` prints, per function, the computed body figure next to
the promised one, and per `locks` block the computed hold time next to `held` resp.
`shared held`.

```
-- Site                                    computed   promised  slack
rechte_aufloesen                           4          4         0
  rechte_aufloesen / shared held KAPPEN    4          4         0
```

**The `slack` column is a difference, not a verdict** — and the two cases differ: for `costs`
slack is often right (a signature should not break on every body change), for `held` it is
almost always wrong, **because the latency statement computes with the promise, not with the
computation**.

**Where it will be needed again:** `held`, `shared held` (already today), `per_pass bounded` —
there with the known caveat that an input-dependent bound is not a number but a term.

---

## W3 — No construct without measured need

**Paid for twice.** `abi { … }` was stopped before it was written. `locks ordered` died at the
paper test of 2026-08-14 with **zero test cases** — and the answer was stronger than the
question: in the whole tree there was not a single repeated acquisition of the same lock class.

**The rule.** A construct needs **counted** sites in real code before the first line of grammar
is written. Not plausible ones, not remembered ones — counted ones.

**The probe for whether the rule works:** the test must be allowed to kill its own candidate. A
paper test that only confirms is a demonstration. *That same test found, instead of the
confirmed construct, two gaps that were on no list — the yield was larger than the loss.*

---

## W4 — A loud overstatement is cheaper than a silent exception

**The case.** `locks shared` stands, but the witness at the **call boundary** needs the call
graph, which does not exist yet. Without a rule the boundary would be not merely unchecked but
**permeable**: the callee writes with exclusive rights, the caller holds only shared — `H001`
through the back door.

**The rule.** Where a load-bearing rule has a hole that can only be closed properly later, the
**coarse, too-strict** version goes in front — not nothing. It has to be **named** as an interim
rule, together with what it forbids too much, and together with the check that will replace it.

**Why.** Somebody goes looking after a loud overstatement — it is in the way. Nobody goes
looking after a silent exception, because it looks like a green.

**The handle.** `H005`: a shared block calls no function with `requires Held(…)`. Full stop.
Including one for a different lock, which is too much and says so in the refusal.

---

## W5 — An interim rule carries three parts, otherwise it becomes permanent

*W4 says **that** the coarse version goes first. W5 says **how** it must be written so that it
really gets replaced later and not merely grown accustomed to.*

**The occasion.** `H005` is deliberately too strict. A too-strict rule without an expiry note is
taken for the right one after three months — nobody remembers what it forbids too much, so
nobody dares touch it. **The overstatement that W4 justifies is exactly what later makes it
untouchable.**

**The rule.** A conservative interim rule names, in its own refusal:

1. **the rule** — what it forbids;
2. **the price** — what it forbids too much, concretely, not as "possibly too strict";
3. **the replacement** — which check will replace it and what that check must be able to do.

**Why in the refusal and not in a ticket.** A ticket is read by whoever tidies up. The refusal
is read by whoever is running into it right now — and that is the person paying the price, and
therefore the one who can report it.

**The handle.** `H005` carries all three parts as notes. At pass 8 it will not have been the
last time.

---

## W6 — Omitting a runtime check is justified by M1 alone, never by an invariant

**The damage, already booked one level up.** `5904cae`: smoothing a claim about the tree instead
of surveying the tree. The same grip one level down would be: striking a range check from the
generated C **because the proof says it cannot go negative**.

**The two nets, and why they are not the same.**

| | what it hangs on | who recomputes it |
|---|---|---|
| **M1** | on the **type** (`u32 in 0 ..= NSLOTS`) | the type system, **per program**, every time |
| **invariant** | on the **template** that preserves it | the trust surface — once, for all |

The Verus template `cap_space.rs` carries `refcount : nat` and proves `oldrc >= 1` (line 792)
**from the invariant**. That is correct — and it is **exactly one net**. Gabbro's
`u32 in 0 ..= NSLOTS` gives a second one that holds **without** the invariant; it was the one
that fell as `M104` next to `D001` in the speech test.

**The rule, mechanically, at every emission decision that cites a proof:**

> **The cited fact must be derivable from M1 alone. Otherwise the check stays in the C.**

**Why that is cheaper than the special version.** The narrow form — *no field generated by a
template carries a type without a width* — covers fields. It does not cover intermediate values,
and it covers future constructs even less; there the same hole opens again. W6 instead sits **at
the decision** rather than at the subject: **one line in the emission pass instead of one per
construct.**

*Noted in advance for a surface that does not yet exist.* The emission pass is not built —
`mutiere-pruefer.py` reports it with **0 mutations**. This rule is therefore a **prior
commitment** today, not a checked promise, and it stands here so that it need not be reinvented
when the building starts. **What has 0 mutations is not covered, it is undamageable.**

---

## W7 — A number without a source list does not belong in a document

**Paid for three times, found in one day.**

| Number | Aggregate | Attribution |
|---|---|---|
| 74 proof obligations (17 logic / 57 plumbing) | in the folder | **lost** |
| 19 hanging obligations in eleven classes | in the folder | **6 of 11** |
| `delete_leaf` 3,6–6 : 1 | in the folder | **lost** |

**The damage is not vagueness but irrefutability.** A number whose attribution is missing cannot
be checked by anyone — not even by its author. It gets quoted, it carries decisions, and it is
immune to every correction, because there is nothing to hold it against.

**Two of the three had already tipped once someone recounted:** `delete_leaf` from 3,6–6 : 1 to
**1,75 : 1** (different counting: obligations instead of proof steps), and the eleven classes
from "19 hanging" to **N_neu = 5 hanging classes** — not convertible, because the old set was
never evidenced.

**The rule.** A reported number carries the list it came from: per item `file:line` or a
re-runnable command line. If the list does not fit in the document, it goes in a file beside it
— **but it exists.**

**The flip side, and it is the actual promise:** a number **with** a list is allowed to be
wrong. It is then checkably wrong, and that is the whole difference. *Trap 80 says a number must
not run parallel to the truth; W7 says how to prevent it.*

**The handle, where it can be mechanical:** `pruefe-luecken.py` and `zaehle-bereichspflichten.py`
print their sites; `gabbro kosten` and `gabbro k-bedingung` likewise. Where a number arises by
hand, the list belongs in the same change.

### **The addition, measured on 2026-08-16: the SWEEP reads table cells as claims**

**The W7 sweep of 2026-08-15 missed a number, and the reason is not carelessness but the
procedure.** It went through the folder's **sentences**. The 89 closures sat in a **table
cell** — and survived.

> **The sweep reads table cells as claims, not only sentences.**
>
> *Otherwise every future table is a hiding place — and this folder has just measured that it
> works.*

**That is a gap in the procedure, not an escaped number.** A number escapes once; a procedure
that never looks at an entire presentation form lets every future one escape.

---

## **The number pair for W7 — the folder's second quantitative piece of evidence**

R14 has its own (**factor 130 between discarded rule versions, factor 1 afterwards**). Since
2026-08-16 W7 has one too, and it is cleaner, because both numbers come from **the same
measurement on the same tree**:

| Number | Search path | Reproduction |
|---|---|---|
| **67** `dyn` sites | stated in the measurement | **exact** |
| **89** closures | **stated nowhere** | **64 — deviation −28 %** |

> **Same measurement, two numbers, one with a search path, one without.** The one with a list
> reproduces to the digit; the one without was off by more than a quarter — **and nobody would
> have noticed, because it looked plausible.**

**That is the whole rule in one number pair:** a number with a list may be wrong, because it is
checkably wrong. One without a list is not wrong — *it is uncheckable*, and that is the more
expensive state.

---

## W8 — A compositional check is probed over **two levels**, not one

**The occasion.** `E008` includes the effects of callees. The obvious probe would be: *caller
declares `writes`, callee declares `writes`, it arrives.* **That measures nothing** — it is
already green if the pass only sees the first level.

**The rule.** A probe for a transitive property puts an **intermediate function** in between
that does **not have the property itself**:

```gabbro
extern fn ganz_tief() effects { masks IRQ } …   -- only HERE does `masks` appear
impl fn mitte()       effects { pure }     …    { ganz_tief(); }
impl fn oben()        effects { pure }     …    { mitte(); }
```

The assurance is: *`masks IRQ` arrives at `oben`.* **If the pass falls back to the first level,
the effect disappears** — and the probe tips. It thereby demonstrably hangs on the subject
(R14b), and specifically on **transitivity**, not on a single hit.

**Where it will be needed again:** the **pairing pass** needs the same probe shape — a
`publishes`/`awaits` pairing **across an intermediate function**. Every analysis that says
"includes …" needs it.

---

## W9 — If an analysis coarsens, the **direction** is checked, not the convenience

*R8 says: overstate only in the safe direction — that applied to **refusals**. W9 is the same
for **analyses**.*

**The case.** `E008` computes over **sets**, not over **paths**. That is the right coarseness —
**but only because here it is coarse in the safe direction**: the pass sees more effects than
there are, never fewer.

**And the same coarseness is inadmissible in one place.** `diverges` does **not** travel upward:
whoever calls a diverging function does not diverge — only whoever calls it on **every** path.
That is a statement about **paths**. Computed over sets it would be coarse in the **unsafe**
direction: it would force `diverges` onto functions that return.

**The rule.** Before an analysis coarsens, ask per property: *does the coarse version err in the
safe or in the unsafe direction?* **The answer goes in the pass comment, not in someone's
head.** A coarsening without a direction check is a convenience with a random result.

---

## W10 — The third state: not refused does not mean confirmed

**The near miss.** `E008` does not refuse on the basis of a **lower bound** — correct (R16): a
refusal from a lower bound would be a claim. But the first version thereby let the function pass
**silently**, and a `pure` promise behind a cycle was green.

**That is the escape-hatch assurance from R15 through the back door** — *"satisfied, because
nothing happened"*, only one level down: not in the assurance but in the **pass**.

**The rule.** Where an analysis may **not refuse** out of incompleteness, it may also **not
confirm**. The honest third state is called **undecidable**, has a diagnostic code of its own,
and is **visible**.

**The handle.** `E009` names the reason (`cycle over …`, `… is unknown to the graph`) and says
explicitly that the `pure` promise is **not checked** at this site. *A side benefit showed up
immediately:* two of the first three `E009` were **gaps in the graph**, not in the program —
`transition`s were missing from it. The third state turned first against our own tool.

---

## W11 — Every gate ratio names its N, and a jump in N is itself a test case

**The near miss.** I sharpened the separation *excerpt / translation unit* and searched for `…`
in the **raw text**. That threw out five of the six fragments — there `…` appears in
**comments**. Gate P2 would have reported:

```
Uebersetzungseinheiten: 1 von 1 ohne Fehler (100 %)
```

**And that is also 100 %.** A filter that shrinks the population **masquerades as success** —
the ratio rises while coverage falls.

**The rule.** Every gate ratio names its **N**, and a **jump in N against the previous run is
itself a test case**. The right report would not have been *"1 of 1 green"* but:

> **"N fell from 6 to 1."**

*The second report is the one that shows the error.* A ratio without a denominator is not a
number — that is trap 80 — and a denominator that moves without cause is a finding.

**The kinship.** W1 says: a coverage number counts evidence, not attempts. **W11 says the flip
side:** when the denominator shrinks, that must be louder than the rising numerator. *Both
errors look the same in the report — only the denominator tells them apart.*

**The handle.** `gabbro fragmente` has always printed N; what was missing was attention to its
**change**. Where a tool defines a population, its size belongs in the same sentence as the
ratio — and its previous value beside it, as soon as there is one.

### **Confirmation came one day after the rule — in pure form**

**B3, 2026-08-16.** The R14(a) probe put a broken brace into a copy of the subject. The tool
reported `Abbrueche: 1` — **and the reported number silently fell from 26 to 24**, because two
bodies dropped out of the inventory.

> **Without the abort counter the measurement would have delivered a number two too low and
> looked healthy doing it** — with a gate that passes *downward*, i.e. in the flattering
> direction.

*The same construction as the P2 case: the numerator is right, the denominator has moved, and
the report looks identical in both cases.* **A rule that catches its second case one day after
being written down is no longer a precaution.**

---

## **The number pair for R14 — the most quantitative argument this folder owns**

R14 (*a measuring tool proves it can measure*) stood on justifications until now. **B3 gives it
numbers, and they are uncomfortably clear:**

| | |
|---|---:|
| spread between the **discarded** rule versions (0,03 % … 4,36 %) | **factor 130** |
| distance between **tool and truth** after the three R14 probes | **factor 1** |

**Four versions, three of them wrong:**

```
version 1   0,03 %   saw only bodies WITH a loop -- loopless surgery invisible
version 2   4,36 %   read `for x in segs` as a non-domain -- ONE body made up 2 %
version 3   0,74 %   missed index, edge and donation chains
version 4   0,95 %   the reported one
```

> **The two discarded versions bracket the right answer and span a factor of 130 doing it. Both
> could have been presented with the same list of sites.** The only difference between them and
> the final version is **R14** — the full count of all 347 `for` heads and the three mutation
> probes.

**The rule that follows fits on one line:** *a number from this class of tool without R14 is not
imprecise, it is worthless.* **Three of four versions were wrong, and none of them looked
wrong.**

---

## W12 — A filled map is no evidence of a **complete** map

**The damage.** The domain bound for `mappings of` was there — `levels × node length`, from the
`walk` declaration, entered into `walkschranken` and demonstrated by a probe (`t::W → 2048`).
**It still did not bite.** Type resolution knew formats, devices and tables — and no walks.
`ptr<normal, r> Seitenabstieg` was simply `Unbekannt`.

**`Unbekannt` did not drop out. It ran along as an empty entry.** I spent half an hour searching
at the wrong end, because the map was filled.

**The class.** That is structurally the same error as the vocabulary guardian claiming closure
over a set it had never seen: **a resolution with a catch-all branch claims a completeness it
does not have.**

**The rule.** At every resolution site, match **exhaustively over the declaration kinds**,
**without a `_` branch**. A new kind is thereby a **compile error** at every chain that does not
handle it.

> **The same D2 medicine the language prescribes to its users, applied to the checker itself** —
> Gabbro demands exhaustive `match` over `tagged`, and Rust hands it over for free here.

**The handle.** `Traegerart::ALLE` (`umgebung.rs`) with five variants and two `match`es without
a catch-all. *The order of the array is the resolution order* — it therefore lives in one place
instead of in the nesting of an `if-else` chain.

**The flip side, and it is the price:** `Typ::Unbekannt` remains admissible as a *result* — a
name no declaration carries is unknown, and that is right. What is no longer possible is **being
unknown because nobody looked.**

---

## W13 — Berührung ist keine Prüfung

**Ein Pass, der ein Konstrukt anfasst, prüft es nicht.** `schleifen.rs` liest
`ItemArt::Check` — aber nur, um in `can_fail` hineinzulaufen. `kbedingung.rs` liest `ops` — als
`!t.ops.is_empty()`, also als **boolesche** Frage, nie als Menge. **Beide Konstrukte gelten
damit als „gelesen", und keine ihrer Zusagen fällt je.**

**Die Feldstufe hatte die Unterscheidung schon.** `pruefe-klauseln.py` trennt seit jeher
**ZUSAGE** (eine Aussage, die kein Pass hält) von **ABSENKUNG** (der Erzeuger ist ihr richtiger
Leser) — genau, weil ein Feld, das nur in einer Absenkung auftaucht, nicht geprüft ist.

> **Maß 1 des Konstruktwächters hat diese Unterscheidung auf der Item-Ebene wieder verloren**
> und meldete 21 von 23 als gelesen — `ops` und `check` darunter, also die zwei Fundstellen,
> für die er gebaut wurde.

**Die Regel.** Wer Deckung misst, fragt nicht *„greift jemand zu"*, sondern **„ist daran je
etwas gefallen"**. Für ein Konstrukt heißt das: *gibt es eine Giftprobe, die es zum Fallen
bringt?* — 7 von 19 hatten keine.

**Und die neue Frage wird NEU abgeleitet, nicht die alte gedehnt.** Maß 1 zu erweitern hätte
geheißen, „gelesen" umzudefinieren, bis es passt; Maß 2 fragt etwas anderes und misst darum
etwas anderes.

---

## W14 — Die eigene Deckung wird systematisch um eine Größenordnung zu hoch geschätzt

**Drei Wächter, drei Messungen, dieselbe Form:**

| Werkzeug | erwartet | gemessen |
|---|---:|---:|
| `pruefe-klauseln.py` — Felder ohne Leser | **4** | **48** |
| `pruefe-englisch.py` — deutsche Meldungstexte | **41** *(erste Schätzung)* | **151** |
| `pruefe-konstrukte.py` — Konstrukte ohne Probe | **2** | **7** |

**Das ist inzwischen selbst ein Datum**, und es sagt etwas Unbequemes: *die Intuition über die
**eigene** Deckung liegt um etwa eine Größenordnung zu optimistisch.* **Nicht über fremden
Code — über den eigenen.**

**Die Regel.** Wer eine Erwartung aufschreibt, bevor er misst (und das verlangt R11 ohnehin),
rechnet mit dem **Faktor**, nicht mit der Zahl: *eine Schätzung von vier heißt „vermutlich
einige Dutzend".*

> **Und der Grund, warum es keine Nachlässigkeit ist:** man zählt, woran man sich erinnert, und
> man erinnert sich an das, was man gebaut hat. **Was nie gebaut wurde, hinterlässt keine
> Erinnerung** — und genau das ist die Klasse, die diese drei Werkzeuge messen.

**Der Preis der Regel, damit sie nicht zur Ausrede wird:** sie rechtfertigt keine Schätzung
nach oben statt einer Messung. *Sie sagt nur, welche Größenordnung eine Überraschung ist und
welche keine.*

---

## W15 — Ein Sammelzweig ist eine stille Zusage, kein Vorbehalt

**Der Befund.** Der Prüfer hatte **78 `_ => {}`-Zweige** über `StmtArt`. Jeder Pass stieg
selbst in die Anweisungen ab, jeder schloss mit einem Sammelzweig — und **jeder vergaß einen
anderen Arm**. Gemessen:

| Anweisungsart | war unsichtbar für |
|---|---|
| `observes` | `m3`, `phasen`, `paarung`, `gruppe`, `kbedingung`, **`aufrufgraph`** |
| `exchange` | `m1`, `m2`, `m3`, `namen`, `geteilt` |
| `narrow … else` | `m1`, `wirkungen` |

**Die Zeile, die es zeigte:** ein Ruf **in** einem `observes`-Block kam im Aufrufgraphen nicht
an. Damit verschwanden zwei `E008` — `masks IRQ` und `writes G` standen im Gerufenen und in
keiner Wirkungsliste. *Derselbe Ruf eine Zeile höher fiel.*

**Warum `_ => {}` schlimmer ist als eine fehlende Regel.** Es liest sich wie ein Vorbehalt
(*„damit befasse ich mich nicht"*) und wirkt wie eine Zusage (*„hier steht nichts, was mich
angeht"*). **Niemand prüft sie nach, wenn eine Anweisungsart dazukommt** — und die neue Art
erbt schweigend so viele Löcher, wie es Sammelzweige gibt.

> **Der Unterschied zwischen einem Sammelzweig und einer Weigerung ist der Unterschied
> zwischen einer Lücke und einem Eintrag.** `emit.rs` schliesst mit `_ => weigere(…, "statement
> kind")` und nennt jede Form, die es nicht kann, beim Namen (`C001`). *Derselbe Zweig, die
> andere Richtung* — und darum steht der Erzeuger in `pruefe-abstieg.py` als gedeckt da.

**Die Regel.** Was über einen Baum absteigt, matcht **erschöpfend, ohne `_`** — an **einer**
Stelle (`lib.rs::unterbloecke`, `lib.rs::endet_immer`), und alle anderen nehmen sie. Dann ist
eine neue Anweisungsart ein **Übersetzungsfehler an jeder Kette, die sie nicht behandelt.**

**Und der Nebenbefund, der die Regel bezahlt:** `endet_immer` stand **dreimal** im Prüfer,
jedes Mal unvollständig und jedes Mal anders. Alle drei hielten `locks L { return x; }` für
*fällt durch*. Eine Zusammenlegung schloss drei Löcher mit einer Funktion.

*Gemessen von `pruefe-abstieg.py` — und zuerst zu grob: die Dateiebene zählte `m2` als gedeckt,
weil `sammle_forever` nannte, was `gehe` fehlte. **Auf Funktionsebene wurden aus 7 Lücken 15**
(W14, zum vierten Mal).*

---

## W16 — Ein Messwerkzeug ohne Abstiegsschritt misst seine eigene Leseweite

**Drei Werkzeuge in einer Woche haben plausibel ausgesehen und etwas anderes gemessen als
ihren Gegenstand.** Die Signatur ist in allen drei Fällen dieselbe, und sie ist so einfach,
dass sie eine Prüfliste hergibt:

| Werkzeug | stieg **nicht** ab in | und meldete deshalb |
|---|---|---|
| die Rufhülle | die Gerufenen | ein Ruf in einem `match`-Zweig war unsichtbar — *und der Korpus hat genau diese Gestalt* |
| `enthaelt_schritt` | geschachtelte Rümpfe | ein `locks { }` um denselben Schritt machte `O006` stumm |
| `pruefe-gruende.py` | über die abgeschnittene Zeile hinaus | **`N011` als verdächtig** — die eine Regel, deren Notiz den tragenden Grund wörtlich nennt |

**Die Regel ist eine Frage, und sie wird vor dem ersten Lauf gestellt:**

> *Ist der Gegenstand rekursiv oder mehrzeilig — und steigt das Werkzeug ab?*

Zusammen mit **W8** (die Zweiebenenprobe) ist das eine mechanische Vorabprüfung für jedes neue
Messwerkzeug: ein Gegenstand mit zwei Ebenen bekommt eine Probe mit zwei Ebenen, und wo keine
zweite Ebene geprüft wird, ist die erste die ganze Messung.

### Und der teuerste Fall ist nicht der Verlust, sondern die Umkehrung

Die ersten beiden Werkzeuge **verloren** eine Antwort; das dritte **kehrte sie um**. Der
Unterschied ist der Grund, warum der dritte der schärfste war:

> **Bei einer verlorenen Antwort fehlt etwas. Bei einer umgekehrten steht das Gegenteil da —
> und sieht vollständig aus.**

Die Umkehrung entsteht genau dort, wo das Abgeschnittene das **entlastende** Material enthält.
`pruefe-gruende.py` las Rusts `\`-Zeilenfortsetzung nicht und sah damit von jeder Absage nur
die Meldung, nie die Notizen — und die Notiz ist die Stelle, an der eine Regel ihren tragenden
Grund nennt. *Ein Werkzeug, das nur die Anklage liest und nie die Entlastung, findet
zuverlässig Schuldige.*

**Es ist R16 in Textform**: eine untere Schranke, die nicht sagt, dass sie eine ist, liest sich
als Ergebnis.

### Und die Sippe reicht über Werkzeuge hinaus: ein Bau aus einer MISCHUNG

Am 2026-08-20 meldete `cargo test` auf `ki-pc-fisch-101` einen Test rot, der lokal grün war —
bei **byteidentischen Quellen** (md5 über den ganzen Baum, beidseitig verglichen). `M107` fiel
hier und dort nicht.

Die Ursache war nicht der Code: **`rsync -a` erhält Zeitstempel, und `cargo` entscheidet
Aktualität nach Zeitstempel.** Eine übertragene Datei behält ihre alte `mtime`; ist die älter
als das Bauartefakt auf dem Server, gilt sie als aktuell — und der Bau ist eine Mischung aus
neuer Quelle und altem Objekt. Ein `touch` heilte es.

> **Dieselbe Signatur eine Ebene tiefer:** das Werkzeug las nicht die Hälfte seines
> Gegenstands, es las die Hälfte seines *Zustands*. Und wie dort sah das Ergebnis vollständig
> aus — eine Zahl, kein Zweifel.

*Die Regel ist dieselbe Frage:* **misst dieser Lauf, was ich glaube, dass er misst — oder
misst er, was einmal da war?** Der Riegel steht in `CLAUDE.md`: `-rlpgoD` statt `-a`, damit
jede übertragene Datei die aktuelle Zeit bekommt.

### Und derselbe Riegel hat ein SPIEGELBILD — gefunden am 2026-08-20

**`-rlpgoD` heilt `cargo` und bricht `pruefe-beweise.sh`.** Der Beweiswächter verlangt einen
*Nachweis*, dass wirklich gebaut wurde (W17: `isabelle build` schweigt bei leerer Auswahl),
und der zweite Weg zu diesem Nachweis lautet: *„kein Bauwerksbuch, das jünger ist als jede
Quelle."* **Das ist eine Zeitstempelfrage.**

Wer den ganzen Baum mit `-rlpgoD` überträgt, gibt jeder `.thy` die aktuelle Zeit. Isabelle
rechnet nach **Inhalt**, wählt korrekt nichts aus und schweigt; der Wächter rechnet nach
**Zeit**, findet keinen Nachweis und meldet `OHNE NACHWEIS` — über einer Sitzung, die
vollständig aktuell ist.

| | `cargo` | `isabelle build` |
|---|---|---|
| entscheidet Aktualität nach | **Zeit** | **Inhalt** |
| braucht deshalb | `-rlpgoD` (neue Zeiten) | `-a` (erhaltene Zeiten), damit der NACHWEIS trägt |

**`CLAUDE.md` führt beide Übertragungen längst getrennt** — `rsync -a beweise/` und
`rsync -rlpgoD ./`. *Das sieht nach zwei Gewohnheiten aus und ist eine Bedingung.* Wer sie zu
einem Befehl zusammenzieht, bekommt einen roten Wächter ohne Fehler.

> **Zwei Begriffe von „aktuell" in einer Kette, und keiner von beiden ist falsch.** Die
> vorherige Instanz log grün (der Bau aus einer Mischung), diese lässt einen richtigen Lauf
> durchfallen. *Die Richtung wechselt, die Frage bleibt.*

Der Wächter sagt seit dem 2026-08-20 in seiner Absage, welche der zwei Ursachen die häufigere
ist und wie man sie unterscheidet — **eine Absage, die ihren wahrscheinlichsten Grund nicht
nennt, kostet jedes Mal dieselbe halbe Stunde.**

---

## W17 — Erfolg ohne Arbeit: ein positives Urteil über nichts

**Am 2026-08-20 hat dieselbe Form dreimal zugeschlagen, in drei ganz verschiedenen
Werkzeugen:**

| | tat | und meldete |
|---|---|---|
| `isabelle build -D .` | wählte **nichts** aus | *„Finished"* — grün |
| `zaehle-b3.py` | druckte `! ABBRUCH` | Rücklaufwert **0** |
| `pruefe-todo.py` | ein Muster traf **nichts** mehr | *„Kennzahlentafel deckt sich mit dem Gegenstand"* |

**Das ist nicht ein falsches Urteil, sondern ein *positives Urteil über nichts*** — und das
ist die gefährlichere Hälfte, weil es wie ein Ergebnis aussieht. Ein falsches Urteil hat einen
Gegenstand und irrt sich über ihn; dieses hier hat keinen und sagt trotzdem *ja*.

> **Die Regel:** neben dem Urteil steht die **Arbeitsmenge**. Wie viele Dateien, wie viele
> Stellen, wie viele Treffer. *Ohne sie ist ein grüner Lauf von einem leeren nicht zu
> unterscheiden.*

**Die Verwandtschaft ist ausdrücklich W11** — *jede Quote nennt ihr N* — nur eine Ebene höher:
W11 spricht über das Verhältnis in einem Bericht, W17 über das Urteil eines Werkzeugs. **Und
über beide steht dieselbe Ursache: ein Nenner, den niemand ansieht.**

**Der Griff.** `pruefe-waechter.py` führt die Arbeitsmenge seit dem 2026-08-20 als **vierte
Forderung** neben Frist, Sprechprobe und rotem Abbruch. Der Lauf mit `--lauf` liest die
wirkliche Ausgabe und meldet jeden Wächter, der ein Urteil ohne Zahl abgibt. *Wo eine Frist
steht, fehlt die Zahl daneben oft noch.*

### Und eine Ebene darüber: die AUSNAHMELISTE, deren Grund niemand nachrechnet

**Derselbe Tag, vierter Fall — und der teuerste.** `pruefe-waechter.py` führte fünf
Instrumente als *„zu schwer für einen Lauf hier"*, jedes mit einem Grund daneben. **Vier der
fünf Gründe waren falsch:**

| | stand da | gemessen |
|---|---|---:|
| `pruefe-emission.sh` | *„46 Einheiten … ~25 min"* | **13,7 s** |
| `pruefe-luecken.py` | *„baut dreizehnmal neu"* | 10,7 s (27,8 s CPU) |
| `pruefe-beweise.sh` | *„zwölf Isabelle-Theorien"* | 8,1 s — es sind dreizehn |
| `pruefe-notation.py` | *„vierzehn `cargo run`"* | **0,56 s, und kein einziges `cargo run`** |

Die 25 Minuten stammen vom **Vormittag desselben Tages**, als derselbe Wächter an `baum41`
HING — einundzwanzig Läufe nebeneinander. Die Frist hat den Hänger beseitigt; die Zahl, die
ihn beschrieb, blieb stehen — **als Begründung dafür, ihn nicht mehr zu messen.**

> **Eine Ausnahme, deren Grund niemand nachrechnet, ist dieselbe Klasse wie eine Zahl, die
> niemand nachrechnet — nur teurer.** Eine falsche Zahl *verfälscht* eine Messung. Eine
> falsche Ausnahme **ordnet sie gar nicht erst an**, und danach gibt es nichts mehr, das
> auffallen könnte.

**Die Regel:** eine Ausnahme von der Messung trägt ihren Grund **als Messung**, mit Datum und
Ort — und wo der Grund eine Zeit ist, steht die Zeit daneben, die der Lauf selbst gemessen
hat. *Sonst überlebt die Ausnahme genau das Ereignis, das sie gerechtfertigt hat.*

**Der Griff.** `--lauf` druckt seit dem 2026-08-20 die Wanduhrzeit **je Wächter** und die
Summe darunter (heute: 19 von 25 in 4,4 s). Die vier verbliebenen Ausnahmen stehen mit dem
Grund da, der wirklich trägt, und keiner davon ist die Zeit: der **Ort** (Speicherspitze über
der lokalen Grenze; Rechenlast gehört auf den Server) oder die **Wirkung** (es schreibt in
Quellen, zwei Läufe zerstören einander).

---

## W18 — Ein Register, das seine eigene Ausgabe enthält, hat einen Fixpunkt statt einer Messung

**Der Fall, in Reinform, und er ist mein eigener.** `pruefe-zahlen.py` hält Kennzahlen gegen
den Befehl, der sie ableitet. Am Tag seiner Entstehung habe ich die zwei Zahlen, die es **über
sich selbst** druckt — bewachte und unbewachte Kennzahlen — in sein eigenes Register
eingetragen.

Der Eintrag ruft das Werkzeug, das Werkzeug prüft den Eintrag, der Eintrag ruft das Werkzeug.
Nach zwei Minuten abgebrochen.

**Und der Rücklauf ist nicht das Schlimme daran.** Ein Fixpunkt, der **terminiert**, wäre
gefährlicher:

> Die Zahl stimmt dann **immer** — und zwar unabhängig davon, ob irgendetwas gemessen wurde.

*Das ist die Ausweg-Zusicherung aus **R15** in ihrer reinsten Form — „erfüllt, weil nichts
geschah" — eine Ebene über dem Werkzeug.* W10 hat dieselbe Bewegung eine Ebene tiefer gefunden
(im Pass); hier steht sie im **Register**, also in der Instanz, die über alle anderen Zahlen
urteilt.

**Die Regel ist mechanisch prüfbar und billig, und darum steht sie als Code und nicht als
Satz:**

> **Kein Registereintrag darf einen Befehl nennen, der das registerführende Werkzeug selbst
> ist.**

`pruefe-zahlen.py` prüft das vor jedem Lauf und trägt dafür seine eigene Sprechprobe. **Die
zwei eigenen Zahlen tragen ihr Datum**, wie jede Zahl aus einem Lauf — ein Register braucht
einen Gegenstand außerhalb seiner selbst.

### Und der Riegel war EINEN SCHRITT tief — nachgezogen am Nachmittag desselben Tages

Der Riegel suchte den **Namen** des Werkzeugs im Befehl eines Eintrags. Das fängt den Ring der
Länge eins und **keinen längeren** — und einer der Länge zwei lag unmittelbar bereit:

> `pruefe-zahlen.py` → `./instrumente/pruefe-waechter.py --lauf` → *jeder leichte Wächter* → `pruefe-zahlen.py`

**Ein einziger Registereintrag mit `--lauf` hätte den Ring geschlossen**, und der Namensriegel
hätte ihn durchgelassen: im Befehl steht `pruefe-waechter.py` und nicht `pruefe-zahlen.py`.

*Der Fehler ist derselbe wie im Werkzeug, das die Regel gefunden hat:* **eine Prüfung, die aus
dem naheliegenden Grund gebaut wurde** — hier: „der Zyklus steht im Text" — **deckt nicht, was
der eigentliche Grund verlangt** — „der Zyklus steht im Prozessbaum".

**Die Fassung, die in jeder Tiefe greift, hängt nicht am Text, sondern an den Kindprozessen:**
eine Marke in der Umgebung, die an jeden Registerbefehl vererbt wird. *Wer sie beim Start
vorfindet, ist von sich selbst gerufen worden.* Sie wird an einem echten Kindprozess gemessen
und nicht behauptet.

> **Die Regel in ihrer allgemeinen Form:** ein Riegel gegen einen Kreis muss an der Kante
> hängen, die den Kreis WIRKLICH schließt. *Ein Namensvergleich schließt einen Kreis über
> Namen; ein Prozess schließt einen Kreis über Prozesse.*

**Und der Nebenbefund ist der beste Beleg für die Messschicht selbst:** der Fehler fiel
**innerhalb einer Minute** auf, weil seit demselben Morgen überall eine Frist steht. *Die
Reparatur der Messschicht hat an ihrem ersten Tag einen Fehler gefangen, den sie erst
ermöglicht hat.*

---

## W19 — Ein Urteil, das sich als Messung liest, bekommt die Autorität der Messung

**`N_ritus` ist der Fall.** K100.1 buchte als Tor: *„`zaehle-bereichspflichten.py`
unterscheidet die drei Fälle."* **Das Werkzeug tat es nicht** — die Unterscheidung stand in
`PFLICHTEN.md`, also im Urteil. Die Zahl las sich, als käme sie aus einem Lauf.

Die Auflösung hat zwei Teile, und der zweite ist der wichtigere:

1. **Die Hälfte bauen, die ohne Urteil geht.** `N_folgenlos` — ein `narrow`, dessen Entfernung
   nichts ändert, ist Zierde. Zweiebenenprobe (W8), heute **0**.
2. **Sie ANDERS benennen.** Denn `N_ritus` ist über die *Erreichbarkeit* des `else`-Zweigs
   definiert, und eine unerreichbare Stelle trägt sehr wohl eine Pflicht — M1 sieht die
   Schranke nicht. **Zwei verschiedene Fragen, und bis dahin hießen beide gleich.**

> **Beide unter einem Namen zu führen hätte die Bewertung mit der Autorität der Messung
> ausgestattet.** *Ein Name ist kein Etikett, er ist eine Zuständigkeitserklärung.*

**Und dieselbe Trennung wird eine Stufe weiter noch einmal gebraucht.** Das
Nutzbarkeitsinstrument aus Stufe 2 (`gabbro zeremonie`) misst **ableitbar** gegen **tragend**
— und das ist derselbe Schnitt: was aus einer Deklaration abzulesen ist, gegen das, was
nirgends sonst steht. *Wer ihn dort nicht zieht, misst die Menge aller Klauseln und drängt
gegen die Zusage der Sprache.*

---

## W20 — Eine Kennzahl, die zum Ziel werden kann, trägt ihre Kalibrierung **im Werkzeug**

**W19 sagt, woran man den Fehler erkennt; W20 sagt, was man dagegen baut.**

Ein Nutzbarkeitsmaß wird sofort zum Optimierungsziel. Fällt es unkalibriert, fällt als erstes
das Billigste — und das Billigste ist hier `effects`, `costs`, die Paarungsklauseln. *Genau
der Gegenstand der Sprache.* Eine Kalibrierung in einer Fußnote schützt davor nicht: sie wird
nicht mitgelesen, wenn die Zahl zitiert wird.

**Die Bauform: zwei Achsen, und sie stehen nebeneinander in derselben Ausgabe.**

```text
ACHSE 1, gemessen    steht diese Tatsache ein ZWEITES Mal in dieser Einheit?
                     -> ableitbar / redundant / tragend
ACHSE 2, erklärt     darf die Zahl sinken? -- je Regel ein Ja/Nein MIT GRUND
```

`gabbro zeremonie --tafel` druckt beide. Ein Waechter liest die Tafel aus dem Werkzeug statt
sie nachzuschreiben (W7) und **verlangt je Regel einen Grund**: ein Nein ohne Satz wäre ein
Machtwort, ein Ja ohne Satz eine Einladung.

> **Erst die Trennung erlaubt den Fall, auf den es ankommt: `ableitbar` UND „darf nicht
> sinken".** `A4` ist so ein Fall — eine Wirkungszeile, die ein Gerufener ohnehin erklärt.
> Sie *ist* ableitbar; sie einfach zu streichen machte `E008` rückgängig. Mit einer Achse
> hätte man sich zwischen „nicht messen" und „zum Rückstand erklären" entscheiden müssen, und
> beides wäre falsch gewesen.

**Und die Sprechprobe wandert von den Mustern auf die Regeln.** Der Korpus meldete beim ersten
Lauf **null** redundante Stellen — ein sauberer Korpus und ein blindes Werkzeug sehen von
außen gleich aus (W17). Deshalb: *eine Regel der Tafel, die nirgends einen Treffer hat, ist
selbst ein Befund*, und was der Korpus nicht auslöst, löst eine absichtlich schlecht
geschriebene Probe aus.
---

## W21 — Ein Wächter, dessen Gegenstand woanders liegt, misst den Rechner

**Der Fall.** Am 2026-08-20 war `./instrumente/pruefe-waechter.py --lauf` auf dem Arbeitsrechner **grün**
und auf `ki-pc-fisch-101` **rot** — bei byteidentischen Quellen. Der rote Posten war
`zaehle-narrow.py` mit Rücklaufwert 2, danebengestellt als *„!! OHNE ARBEITSMENGE"*.

**Nicht der Code fehlte, sondern der Gegenstand.** `zaehle-narrow.py` misst den zweiten Korpus
(`~/Dokumente/SEL4Lake/SEL4Lake`), `zaehle-b3.py` die Caprock-Messbasis — **und beide liegen
nur auf dem Arbeitsrechner.** Auf dem Rechner, auf den `CLAUDE.md` die ganze Rechenlast legt,
gibt es sie nicht.

> **Beide Richtungen sind falsch, und das ist der Grund, warum es eine eigene Klasse ist:**
> ein fehlender Gegenstand kann als **rot ohne Fehler** erscheinen (der Ruf schlägt fehl) oder
> als **grün ohne Messung** (das Werkzeug zählt null und meldet „keine Befunde"). *Die zweite
> Richtung ist W17; die erste ist ihr Spiegelbild und genauso wertlos.*

**Und die Sippe reicht bis in den Arbeitsbaum.** `../caprock-messbasis` ist ein **relativer**
Pfad. In einem `git worktree` zeigt er neben den Arbeitsbaum statt neben die Hauptauscheckung
— dort ist er ebenfalls weg, auf demselben Rechner. `zaehle-b3.py` lief darüber bis in eine
`ZeroDivisionError` und meldete Rücklaufwert 1, also *einen Befund*.

**Die Regel:** ein Wächter, dessen Gegenstand außerhalb des Baums liegt, **deklariert den Pfad
und was dort steht**. Fehlt er, ist das Ergebnis weder rot noch grün, sondern **nicht
gemessen** — mit seiner Zahl neben dem Urteil.

    FREMDER_KORPUS = {
        "zaehle-b3.py":     ("../caprock-messbasis", "die Caprock-Messbasis"),
        "zaehle-narrow.py": ("~/Dokumente/SEL4Lake/SEL4Lake", "der zweite Korpus"),
    }

*Das ist kein Freibrief.* Der Unterschied zu einem stillen Überspringen ist genau die Zahl:
**„18 von 19 gelaufenen nennen ihre Arbeitsmenge, 1 weiterer nicht gemessen, weil sein fremder
Korpus fehlt"** — ein Loch, das sich zählen lässt, ist ein Posten; eines, das grün aussieht,
ist keiner.

**Und der Nebenbefund gehört zur Messschicht:** dass die Zählung über den zweiten Korpus
(*„wie viele der 637 `atomic_*()`-Stellen sind Zähler ohne obere Schranke?"*) seit Tagen
offensteht, hat **keinen** fachlichen Grund. Sie ist **ortsgebunden**, und der erste Schritt
ist eine Übertragung und kein Werkzeug. *Das stand nirgends, weil niemand den Ort aufgeschrieben
hatte.*
