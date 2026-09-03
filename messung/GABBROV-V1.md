# GabbroV V0 and V1 — are the 66 logic obligations sayable in the Lean fragment?

*Measured 2026-09-02 from tree `371dec6`. `dokumente/GABBROV.md` §10 puts V1 before
everything else, because it is the one stage that can fail before a line of code exists.
This file carries the answer and the way to it. Every count below names the command that
produced it.*

## The answer, up front

**56 of 66 stand as a Lean `Prop`, and `lean` accepted every one of them.**
`programmlogik/gabbrov/V1.lean` is the measurement — 66 rows, exit 0, no `sorry`, no
`native_decide`.

```
L total                    66
  not written as a Prop    10
  written as a Prop        56
demands on the fragment    3, over 8 rows (and §7 records ONE of the three)
```

> **CORRECTED 2026-09-03, and the correction is to this file's own sentence.** The line here
> read ~~**`G1` does not fire**~~. It should not have: `G1`'s condition is *"a noteworthy part
> of the 66"*, which is not a number, so **no count can clear it and none can trip it**. That
> was a judgement in a measurement's clothes, in a file whose whole subject is the difference.
> **No threshold is being supplied after the fact** — one chosen with 56 of 66 already on the
> table would be chosen to clear it (`R2`). `dokumente/GABBROV.md` §11 carries the withdrawal;
> `AUFTRAG-GABBROV.md` §1 carries the two criteria that replace it, and they were written down
> before the runs they judge. *The count below is untouched by this; only the verdict over it
> is gone.*

The ten are not ten accidents. They are four classes, and two
of the four are not an expressiveness gap at all:

| | rows | | what it is |
|---|---:|---|---|
| **EXTENSION** | 3 | L11 L12 L13 | a `tagged` variant with a RECORD payload; the shared `Value` must grow a form |
| **NOT — ordering** | 4 | L24 L34 L50 L52 | "in ONE step", "the invariant fails BETWEEN", "flush BEFORE reply" — **one missing means, four rows** |
| **NOT — environment** | 2 | L42 L46 | the progress measure is outside the program: **an `assumption` (§5), not an `obligation`** |
| **NOT — meta** | 1 | L57 | `counterprobe` — a statement about a SECOND, mutated program |

> **The finding is not the 56. It is the line under it.** §7 records **one** demand on the
> fragment (aggregation, «B13», carrying **one** row). The walk finds **three**, and the
> largest is not the one written down:
>
> | demand | rows | §7 records it? |
> |---|---:|---|
> | aggregation — `count` over a table domain | 1 | **yes** |
> | folds that are not `count` — *the FIRST x with P* | 2 | no |
> | **bounded reachability — `place reaches place via field`** | **5** | **no** |
>
> **And the language already has the third one.** `SYNTAX.md`:717 carries
> `reach = place "reaches" place "via" ident`, `parse.rs`:2117 builds `PredArt::Erreicht`
> from it, and a probe through the unchanged checker passes with **0 errors**. The Lean
> channel refuses it by name (`LeanReason::Quantified` — *"a QUANTIFIER, `reaches`, or a set
> membership"*), and the same obligation exported with `gabbro pflichten --lean` comes back
> as `table-invariant (1)` with no goal. ***§7's own argument about aggregation applies
> word for word: if the fragment does not carry it, the same gap moves one level up.***

---

## 1. What was fed in, and by which command

The population is the `L` column of `dokumente/PFLICHTEN.md` — the same rows the tree's own
counter counts, read with the tree's own row parser (`_zellen`, unescaped pipes only, third
column after markup is stripped).

```
./instrumente/zaehle-pflichten.py --spalten
```

| | |
|---|---:|
| obligations in total | 239 |
| plumbing (K) | 173 |
| **logic (L)** | **66** |
| of the 66, anchored at a `FRAGMENTE.md` line | 66 |
| of the 66, from the lowering rows | 0 |

**The lowering rows carry no `L`.** All ten are `K`, so the denominator of this run is
exactly the anchored rows, and `66` needs no adjustment.

---

## 2. Finding: the guard reach of a new `dokumente/*.md` is ONE loud number

*This is step A of the mandate, measured rather than assumed.*

`CLAUDE.md` records that seven guards read German document text and that **four go silently
blind** when it moves (`pruefe-todo.py`, `-zahlen.py`, `-grammatiktafel.py`,
`-widerruf.py`). Held against a **new** file in `dokumente/`, that list collapses:

| guard | reads `dokumente/GABBROV.md`? | why |
|---|---|---|
| `pruefe-todo.py` | no | reads `TODO.md`, `README.md`, `dokumente/PLAN.md` by name |
| `pruefe-grammatiktafel.py` | no | reads `dokumente/SYNTAX.md` only (`:148`) |
| `pruefe-zahlen.py` | **yes** — `rglob("*.md")` (`:1455`) | and it went **RED**, see below |
| `pruefe-widerruf.py` | **yes** — `glob("dokumente/*.md")` (`:243`) | already bilingual |

**`pruefe-zahlen.py` is loud, not blind, and it caught the right thing:**

```
BEFUND  TODO.md: „Dateien, die der Widerrufwaechter liest" steht als 179, der Lauf sagt 180
```

Adding one file to `dokumente/` moves `pruefe-widerruf.py`'s file count, and `TODO.md`
carries that count as a guarded number. *The guard for the document I was about to add was
a number about a different guard's reach* — exit 0 → 1 purely from the file's presence,
measured by adding and removing it and diffing the two runs.

**And `pruefe-widerruf.py` needs no work: it is already bilingual, and that is measured.**

```
== Sprechprobe (R14) ==
  eingesetzter Satz faellt:      ja, 24 von 24 Proben (je Eintrag deutsch UND englisch)
```

Twelve entries, both languages each, and every probe falls. Driven separately against the
German `GABBROV.md` text: **0 of 12 patterns fire on it.** So there is nothing this
translation can take away from that guard — the "pattern grasps into thin air" hazard has
no instance here, and that is a measurement and not a hope.

> **The order in the mandate was still the right one.** The reason it cost nothing this
> time is that the tree already paid it: `pruefe-widerruf.py`'s head records that `probe`
> and the second language became mandatory on 2026-09-01, *because* its green is
> indistinguishable from a miss. **A guard that cannot go red when its pattern dies has to
> carry the proof instead of inferring it** — and this run is what that purchase looks like
> from the outside.

---

## 3. V1, row by row — and the file is the measurement

`programmlogik/gabbrov/V1.lean` carries all 66. It **imports `Gabbro.Body` and defines no
second semantics**, because §8 is the reason V0 comes first: two formalisations believed
equal hide every defect in their difference. Where the existing four-form `Value` cannot
carry a row, the file says so and leaves it — it does not repair it locally.

```
cd programmlogik && lake build                       # Gabbro.Body, 2.1 s
LEAN_PATH=.lake/build/lib/lean lean gabbrov/V1.lean  # exit 0
```

The three means the fragment needs are built there from **Lean core only** — `programmlogik`
has no mathlib and its lakefile says why — so a table domain is a `List Int` and the
aggregation is `List.filter`. *That all three type-check over the unchanged `Gabbro.Body` is
the proof that they cost the shared semantics nothing*, and it is exactly what separates them
from the three rows that need a new `Value` form.

### The ten that do not stand as a `Prop`

**L11, L12, L13 — a record payload.** `tagged type ObjectKind = { Memory(Region), …,
Reply(ReplyRef), …, Dma(DmaRef), … }`. All three obligations speak about the payload —
*"**the region** goes back to the RAM allocator"*, *"**the caller** is unblocked"* — and
`Region`, `DmaRef`, `ReplyRef` are RECORDS. `Value` is four forms and `present` carries one
`Int`. The tree already books this by name: `LeanReason::ConstructedValue`, *"the price is a
MODEL EXTENSION, and it is a different price from a missing gate."*

> **Contrast L41, which costs nothing:** `tagged type BufPhase = { Driver, Device }` has no
> payload, so it is a tag, and a tag is an `Int`. *The price is the payload, not the `tagged`.*

**L24, L34, L50, L52 — ordering and atomicity, and they are ONE missing means.**

| | the obligation, in the fragment's own words |
|---|---|
| L24 | `caller` and `reply_owner` are **never half set** — two places in ONE move |
| L34 | *"Ohne ihn zwei Zuweisungen, und die Invariante gilt **dazwischen** nicht"* |
| L50 | `Flush` — the flush completed **before** the reply |
| L52 | `Stop` — the reply still goes out **before** the service ends |

Every means of §7 is a predicate over a state or over a pre/post pair. These four are about
what happens *between* them, and `Body.lean`'s `exec` is big-step: **there is no intermediate
state to name, let alone to quantify over.** L24 needs to say no third state exists; L34 needs
to say one does and what fails in it. Same means, opposite directions.

> **The two ways out are the two failure modes §5 and §7 already name.** Taking L24 as vacuous
> — under a big-step semantics the pair *is* atomic by construction — is §5's vacuity hazard
> exactly: it would read as proved and say nothing. Writing L50 as `flush ∧ reply` type-checks,
> reads right, and is a strictly weaker statement wearing the obligation's name — §7's
> *"translation that does not understand something and leaves it out"*, which it names as the
> commonest way such tools go unsound.
>
> **This is the only one of the four classes that is a genuine expressiveness gap in the cut**,
> and `GABBROV.md` §3 had already picked its site out as *the* place GabbroV would create value
> beyond convenience: `breaking` on the wrong-but-existing invariant. The measurement says
> V1's fragment cannot get there.

**L42, L46 — the measure is outside the program, so these are `assumption`s.** *"It ends
because **the device** completes or faults"*; *"it makes progress because a client calls or
the endpoint is revoked."* No predicate over a state pair says "this loop ends", and the
reason it ends lies with an agent the program does not contain. **In GabbroV's own vocabulary
they belong to §5's second class**, the one that already has a falsification discipline
against real hardware. *That is a finding about the manifest's booking, not about the cut —
and it is the cheapest of the ten to act on: it moves a row, it builds nothing.*

> **L66 is the counter-probe that makes this a class and not a complaint.** *"It ends because
> **a token is consumed**"* stands as a `Prop`, because `PFLICHTEN.md` names the difference in
> the row itself: *"the ALGORITHM's progress measure, not the machine's finiteness"*. The
> measure is a place in the program's own state. **L42 and L46 differ from L66 in exactly one
> respect, and it is the respect that decides.**

**And the classification finding is wider than those two rows — the grammar says so itself.**
`SYNTAX.md`:1074, at the `forever` form:

> ***"`progress` names WHO ends it — an assumption about the environment, with a falsifier.
> The watchdog IS the falsifier."***

The ten fragments carry **exactly three** `progress` clauses — `FRAGMENTE.md`@708beed:887,
:981 and :1656 — and they are precisely L42, L46 and L66. **`PFLICHTEN.md` books all three as
logic obligations.** So the misfiling is not "two rows in the wrong column": *the construct
that produces all three is documented as an assumption, and the manifest books all three as
obligations.*

> **What separates L66 is not the construct but the referent of the named predicate** —
> `token_verbraucht` is about the program, `device_completes_or_faults` about the world — and
> that is the line `PFLICHTEN.md` draws in L66's own row. **The classification question and
> the sayability question have different answers, and these three rows sit exactly where they
> differ.**
>
> *This paragraph corrects an earlier draft of this file, which said "two rows are misfiled"
> and had not yet counted the third. The count came from `grep -n progress` over the frozen
> fragment text — three hits, all three booked `L`.*

**L57 — a statement about a second program.** `counterprobe "Fuellung ausgehaengt" expects
erschoepft_waechst` — the speech test as a language construct. Every other of the 66 is about
one program's states; this one says that under a named mutation the check fails. The fragment
would have to quantify over PROGRAMS. *It is also the row whose absence would be least
visible, which is the whole reason the construct exists.*

### And three rows whose gap is at the OTHER end — counted as sayable, on purpose

`PFLICHTEN.md` marks these with `gap:`, and it is easy to add those gaps to V1's. **They are
different gaps, and adding them would inflate the finding.**

| row | the gap `PFLICHTEN.md` records | why it is still SAYABLE |
|---|---|---|
| L02 | «B14» — `pred` cannot resolve an `option index into` | `Value.present` carries the index in the open; resolving it is a pattern match |
| L40 | «B26» — no placeholder for the pre-state | a universally quantified pre-state is what a Lean `Prop` gives away free |
| L64 | *not in the fragment at all* — W^X was never written | V1 asks whether §7 can SAY it: a bounded ∀ with a negated conjunction |

> *One kind of gap says the corpus never stated a property, or that the grammar has no
> production for it; the other would say the specification language cannot state it.*
> **Only the second falsifies the cut.**

### The speech test, because three of the means are mine

`R11`: a guardian nobody has ever seen say no is an ornament. **A `reachesIn` that always
answered `true` would pass all five `cdtWf` rows without a word** — `W16`, one level below
where this folder usually books it. So every means is driven in both directions, all with
`decide` and none with `native_decide`:

* the chain `2 → 1 → 0` **is** reached; the same world with `2 → 2` **is not**;
* the bound is a real bound — budget 1 does not reach what budget 4 does;
* `countD` counts, and counts zero;
* `firstD` takes the **first** and not merely *some* — if it returned any satisfying element,
  L29 would be the obligation *"the fastpath takes A live receiver"*, and the fragment's own
  note calls that a different program;
* `absent ≠ int 0` — the distinction L44 and L53 rest on, proved rather than asserted.

---

## 4. V0 — what five REAL manifest lines mean

§10 asks for the meaning of the obligation texts *"written down, against real lines from
`PFLICHTEN.md`"*, and §8 says why this is the load-bearing step. The lines below are the
actual output of the actual binary over `beispiele/01-tabelle.gab` — a file whose shape is
F1's: `baum_wohlgeformt` is `cdt_wohlgeformt`, down to `reaches WURZEL via elter`.

```
./target/debug/gabbro pflichten beispiele/01-tabelle.gab
```

| # | the manifest line | | what it MEANS, in the shared semantics |
|---|---|---|---|
| 1 | `aushaengen :: ensures #1` | N | for every `s`, `f`: if `exec` of `aushaengen`'s body from `s` finishes in `s'`, then `s'.world (.slot "c" f "elter") = .absent`. **Carried today** — `duty_2` is a real theorem |
| 2 | `aushaengen :: baum_wohlgeformt` | E | if `cdtWf s.world d 4096 WURZEL` then `cdtWf s'.world d 4096 WURZEL`. Refused as `table-invariant`; DEMAND 3 is what it needs |
| 3 | `einsammeln :: blatt_loeschen requires #1` | V | at the call site, the callee's precondition holds of the state THERE — not of the caller's entry state. Refused as `call-site` |
| 4 | `einsammeln :: loop invariant #1` | S | `c.slots[s].benutzt` holds at entry to every pass of the traversal. Refused as `loop` |
| 5 | `blatt_loeschen :: ensures #1` | N | `s'.world (.slot "c" s "benutzt") = .bool false` — but the body CALLS `aushaengen`, so the meaning is only fixed once the callee's contract is. Refused as `call-not-compositional` |

**Three things this handful settles, and each is a sentence GabbroV's design owes:**

1. **An obligation's meaning is a relation between TWO states, not a predicate on one.**
   Lines 1, 2 and 5 all need `s` and `s'`. §7's phrase *"predicates over values"* reads as one
   state, and **20 of the 66 take both states as parameters** — read off the file rather than
   estimated:

   ```
   grep -c '^def L[0-9][0-9] (s s'"'"' : State)' programmlogik/gabbrov/V1.lean   # 20
   ```

   > *An earlier draft of this line said 42, and the number came from nowhere — it was
   > written before the file was counted, in a section whose whole subject is that the
   > meaning has to be written down rather than assumed.* **The grep is here so the next
   > reader need not take the corrected one on trust either.**

   *This is not a gap — the fragment holds all twenty — but it is a wording in §7 that will
   mislead the next reader if it stays.*
2. **Line 3 fixes the meaning of a call site**, and it is the one place where the meaning is
   not local: `requires #1` names a conjunct of a routine the manifest line does not name in
   full.
3. **Line 5 says the meaning is not compositional yet.** `blatt_loeschen`'s postcondition is
   only fixed once `aushaengen`'s contract is, and that gate is not built — the refusal says
   so by name.

> **And the second point has a sharper form that §2 of `GABBROV.md` should hear.** §2 shows a
> manifest carrying its obligation as TEXT —
> `obligation revoke.functional "ensures !exists k in descendants of s: k.used" offen` —
> and rests the design's premise on it: *"GabbroV does not read the Gabbro program. It reads
> the manifest."*
>
> **Today's manifest does not carry the text.** It carries `aushaengen :: ensures #1` — a
> function name, a clause kind and an ORDINAL. Reconstructing the obligation from that means
> reading the source and counting conjuncts. So either the manifest grows the text, or §2's
> sentence is wrong about the tool it describes. *`gabbro pflichten --lean` already carries it
> as a datum (`post_duty_2 : Expr`), so the material exists — it is the plain-text manifest,
> the one §2 quotes, that does not.*

---

## 5. §8 — what the carrier finding means for V0

`messung/LEAN-REICHWEITE.md` measured, hours before this run, that **101 of 119 place mentions
name a carrier absent from the export's own dictionary**, and showed in Lean that the
specification a person would write from `places` FALLS while the body's own frame theorem
passes. That is §8's hazard in the flesh: the obligation texts are supposed to have one
meaning, and the Lean channel disagreed with itself about what a place is called.

**Measured here on one file, both channels, one binary:**

```
./target/debug/gabbro lean             beispiele/01-tabelle.gab
./target/debug/gabbro pflichten --lean beispiele/01-tabelle.gab
```

| channel | what `wellFormed` / the hypotheses say | what the bodies say |
|---|---|---|
| `gabbro lean` — the PROGRAM | `.slot "Kappenraum"` ×7, `.slot "Objekte"` ×2 | `.place "c"` ×11, `.assign "c"` ×7 — **not one carrier in the dictionary** |
| `gabbro pflichten --lean` — the OBLIGATIONS | `.slot "c"` ×12 | `.place "c"` ×21, `.assign "c"` ×21 |

**The answer: GabbroV can proceed on today's manifest, and the carrier question does not have
to be settled first.**

The split is between the two channels, not inside the one GabbroV reads. The obligation
channel resolves every place against the body's own carrier — hypotheses, reads and writes all
say `"c"`, and `"Kappenraum"` does not occur in it at all. `LEAN-REICHWEITE.md` had already
named the cause from the other side: *"which is why the OBLIGATION channel has no such gap and
its ten theorems go through."* **This run confirms it by direct count rather than by
inference**, and V0's five lines above are written against that channel.

**But the exemption is exactly as wide as the composition gap, and no wider.** The obligation
channel buys its consistency by dropping the table identity: `.slot "c" k f` says nothing about
which table `c` points at. That is harmless while each obligation is its own theorem over its
own state — which is precisely what `call-site` and `call-not-compositional` being *refusals*
guarantees today. **The moment GabbroV links two obligations — a call site's `requires` against
the callee's `ensures`, which is V4's whole point — the carrier becomes a cross-routine
identity, and it is a PARAMETER NAME.** Two routines may both call their parameter `c` and
point it at different tables.

> So the honest scheduling is: **the carrier question is not V0's blocker, it is V4's.** It
> becomes load-bearing at exactly the step where `Body.lean`'s U3 — *"two different carrier
> names are two different objects"* — has to be read in the other direction, where it is false.
> *A hypothesis that is safe per theorem is not safe across theorems, and nothing in the tree
> currently says which of the two it is being used as.*

---

## 6. What V2 would cost — argued, and NOT built

V1 passed, so §10's next gate is V2: *"assumption check: satisfiability, vacuity"*, gated on
*"the assumption set of the ten fragments has a model."* **The set was measured, not
estimated.**

```
./target/debug/gabbro annahmen messung/fragmente/F02.gab   # 3
./target/debug/gabbro annahmen messung/fragmente/F04.gab   # 3
./target/debug/gabbro annahmen messung/fragmente/F05.gab   # 1
./target/debug/gabbro annahmen messung/fragmente/F10.gab   # 1
```

**The whole assumption set of the ten fragments is EIGHT.** F1, F3, F6, F7, F8, F9 declare
none. Seven of the eight carry a `falsifier` name; one (`gcmd_kein_rmw`) is expressly
`nicht-falsifizierbar` with its reason written out — *a probe would have to clear TE briefly,
opening exactly the window the mechanism is built against.*

### The finding that decides the cost

**Every one of the eight is a PROSE SENTENCE, not a formula.**

```
A1  device_completes_or_faults  assume  --  ungedeckt  --  --
    Ein Geraet, das einen Deskriptor genommen hat, meldet ihn innerhalb der
    zugesagten Leseoperationen zurueck oder faultet.
```

> **So `G5` cannot fire today, and it cannot be cleared today either.** "The assumption set
> has a model" is a question about formulas. Asking it of eight German sentences is not a hard
> problem — it is not yet a question. *A gate that cannot be evaluated is not a gate that
> passes.*

**Hence the cost of V2 is not a solver call.** Eight assumptions is nothing for Z3 — if they
were formulas. **The cost is the formalisation**, and it is the same work V0 and V1 just did
for the obligations, on a set that today has no formal content at all.

### And it is HARDER than V1's, for a reason V1 measured

The obligations speak about the program's state, and the fragment of §7 holds 56 of 66 of
them. **The assumptions speak about the world**: a device that will report back, a client that
will call, an ordering two accesses become visible in. *"Reports it back within the promised
read operations"* quantifies over time and over an external agent — **the same means the four
ordering rows lack, plus a temporal one on top.**

> So V2 inherits V1's one genuine gap and adds to it. **A fragment that cannot say "the flush
> completed before the reply" cannot say "the device reports back within N reads" either.**

### The half that IS cheap, and it is the half worth building

§5 names two things and they have opposite costs:

| | what it needs | cost |
|---|---|---|
| **contradiction** — does the assumption set have a model? | the eight assumptions as formulas | **the whole formalisation, and a vocabulary V1 measured as absent** |
| **vacuity** — is a precondition unsatisfiable? | the preconditions, which V1 showed ARE sayable | **small, and available now** |

**Vacuity needs no assumption formalisation at all.** It asks whether a `requires` is
satisfiable, and `requires` conjuncts are obligation-side objects — the fragment holds them.
That half could be built against today's manifest.

> *§5 says both are "cheap and only buildable early". The measurement splits them: one is
> cheap, the other is a second V0.*

### Three rows that are booked twice, and it costs nothing to fix

The strongest V2-adjacent finding is not about cost at all. **The three `progress` names of
the ten fragments are already `assume` declarations in the fragment source** — and
`PFLICHTEN.md` books each of them a second time as a logic obligation:

| the `assume` in the source | the same name as `progress` | booked in `PFLICHTEN.md` as |
|---|---|---|
| `F04.gab`:33 `assume device_completes_or_faults` | `FRAGMENTE.md`:887 | **L42, logic obligation** |
| `F05.gab`:87 `assume client_calls_or_endpoint_revoked` | `FRAGMENTE.md`:981 | **L46, logic obligation** |
| `F10.gab`:62 `assume token_verbraucht` | `FRAGMENTE.md`:1656 | **L66, logic obligation** |

And `F10.gab`:60 states the rule in its own words, as the reason the `assume` is there at all:

> ***"`progress` nennt eine Annahme mit Falsifikator; ohne `assume` steht der Name in keinem
> Manifest."***

**So these three sit in the assumption manifest and in the obligation column at once.** Two of
them (L42, L46) are among the ten V1 could not say — *and the reason they cannot be said as
obligations is precisely that they are not obligations.* **Moving them is a correction to the
manifest, not a construction**, and it would take the "not sayable" count from ten to eight
without touching the fragment.

> **What it would NOT do is make the cut look better than it is.** The four ordering rows stay
> exactly where they are, and they are the finding.

---

## 7. What this lane did not measure, named rather than left out

* **Whether any of the 56 is PROVABLE.** V1 asks whether the obligations can be SAID. Every
  `Prop` in `V1.lean` is a definition; not one is a theorem, and the file says so. *`Body.lean`'s
  `Outcome` has no arm for a `leave`, `call-not-compositional` is unbuilt, and both bite at
  proof time and not at statement time.*
* **Whether the 66 are the right 66.** The `K`/`L` column is a human judgement;
  `zaehle-pflichten.py` counts it and does not make it, and its own output says so.
* **The Isabelle side of §8's question.** Open question 3 stays open: this run measured the
  Lean channel against itself. `messung/LEAN-REICHWEITE.md` records that the two exporters'
  goal sets are disjoint — *no obligation in this tree has ever been stated by two provers* —
  and nothing here changes that.
* **The second corpus.** The 66 are the ten fragments, chosen for difficulty. A fragment set
  chosen for difficulty is the wrong denominator for "how often does this happen", and the
  right one for "can it be said at all", which is the question V1 asks.
