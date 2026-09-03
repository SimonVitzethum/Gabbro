# GabbroV — the checker for the logic obligations

Status: draft. Quotations from `SPRACHE.md` and `PFLICHTEN.md` are sourced; everything else
is a proposal.

> **V1 is no longer a proposal.** The first measurement this document asks for has been made
> — `messung/GABBROV-V1.md` and `programmlogik/gabbrov/V1.lean`, 2026-09-02. **56 of the 66
> stand as a Lean `Prop` and `lean` accepted them.** §7 and §12 carry the result at their own
> place, and the two sections it corrects say so in their own words.
>
> **What that run may NOT be quoted as is a verdict on `G1`, and the correction is dated
> 2026-09-03.** ~~`G1` does not fire.~~ `G1`'s condition is *"a noteworthy part"* — no number
> — so no count can clear it and no count can trip it. §11 carries the withdrawal; the two
> criteria that replace it stand in `AUFTRAG-GABBROV.md` §1, and they stand **before** the
> measurements they judge.

> **A note on language.** `CLAUDE.md` has set English for every `.md` document in the Gabbro
> tree since 2026-09-01. This document was German while it was conversation. It was translated
> when it landed here — **and the guardian patterns were held against it first, not
> afterwards**: `messung/GABBROV-V1.md` §2 has the measurement, and the answer was that the
> one guardian which reads a new `dokumente/*.md` for German text is already bilingual
> (24 of 24 probes, both languages), so this translation could take nothing away from it.

---

## 1. What Gabbro already does, and how we know

`SPRACHE.md` §0 says it itself:

> **Gabbro proves everything except logic.**

| | who | how |
|---|---|---|
| **Plumbing** — index, overflow, alias, frame, lock, race, **termination**, phase, leafness, publication | Gabbro | M1–M4, generated schemata. *No SMT, no solver, no heuristic* |
| **Logic** — *this* function does *the right thing* | the programmer | Gabbro **emits** every open logic obligation into the manifest |
| **Plumbing that rests on logic** (§8.3) | mixed | falls constructively, **but is booked as logic** |

Termination is in line one. `M4` demands a descent measure, `divergent fn` is the spoken
exception, `by unvisited` and `decreases expr` are the notation, and §5.4 records that at a
`walk` the depth is M1-bounded and the termination of the descent falls **constructively** —
no variant, no proof.

Invariants likewise: `table … invariant`, `group`, `maintains`. They are declared and carried
by the checker, not searched for by a solver.

**So GabbroV's cut is narrow and clear: logic and assumptions only.**

Order of magnitude, measured against `PFLICHTEN.md` over the ten fragments: ~~**164 K against
66 L**~~ **173 K against 66 L** (163 K anchored at a line + 10 lowering rows). About a quarter
of the obligations reach GabbroV at all. The number holds for this corpus, not in general.

> **BERICHTIGT 2026-09-03, and the old figure was never a measurement of this tree.**
> `./instrumente/zaehle-pflichten.py --spalten` reports `229 = 163 K + 66 L` anchored and
> `239 = 173 K + 66 L` in total. **`164` is neither** — and it is exactly what the counter's
> own speech probe produces when a row with an escaped pipe is miscounted
> (`Sprechprobe: … K 163 -> 164`). *A number reached by arithmetic instead of by the tool
> that owns it.* `messung/GABBROV-V2.md` §1.5

---

## 2. The interface already exists

`SPRACHE.md` §15 describes the obligation manifest the compiler emits per translation unit —
and names as its addressee expressly *"the programmer **or an external tool**"*.

```
obligation revoke.functional   "ensures !exists k in descendants of s: k.used"  open
assumption vtd_te_effective    falsified(probe_vtd_te)
closed     consuming.template  "order preservation descendants"                 site
```

**GabbroV does not read the Gabbro program. It reads the manifest.**

That is the most important difference from an ordinary verifier, and the reason the tool can
stay small: it need rebuild no program semantics, generate no verification conditions from
control flow, model no memory. GabbroC has already computed and named the obligations.

> **BUT — measured 2026-09-02, and it bears on the sentence above.** The manifest as the
> binary emits it **does not carry the obligation text.** It carries `aushaengen :: ensures #1`
> — a function name, a clause kind and an ORDINAL. Reconstructing the obligation from that
> means reading the source and counting conjuncts, which is exactly what the paragraph above
> promises GabbroV need not do. *Either the manifest grows the text, or this section is wrong
> about the tool it describes.* The material exists: `gabbro pflichten --lean` already carries
> it as a datum (`post_duty_2 : Expr`). `messung/GABBROV-V1.md` §4 has the five lines this was
> read off.

Three classes, three tasks:

| manifest class | GabbroV |
|---|---|
| `obligation` | check against the Lean specification — the actual work |
| `assumption` | satisfiability of the assumption set, vacuity, probe status (§5) |
| `closed` | nothing; only keep the site |

So the call is: **manifest + Lean specification → passed / refuted / undecided.**

---

## 3. The one exception, and it is real

§8.3 names the third class: *"if a plumbing obligation falls only via a logic invariant, it is
booked as logic."* Without that rule *"falls constructively"* would become a convenient
booking — the `depleted_count` dispute was decided on exactly this.

In practice: "Gabbro handles termination and invariants" holds, **except** where the descent
measure or the restoration rests on a logic invariant. A `breaking` block that does not close
with a generated operation produces an `obligation` — and that one lands at GabbroV.

That is not an objection to the cut but its sharpening: GabbroV gets exactly what the manifest
books as logic, and the booking rule already stands.

And §8.3.1 names what `D013` does **not** check: that the invariant really rests here, that
the block restores it, that `requires I` / `maintains I` are barred inside it. *A `breaking` on
the wrong but existing invariant still passes.* If GabbroV creates value anywhere beyond
convenience, it is here.

> **Measured 2026-09-02, and the answer is not the one this section hoped for.** The statement
> this site needs is *"the invariant does not hold BETWEEN the two assignments"* — `L34` of the
> 66 — and it is one of the four the fragment of §7 **cannot say**. Every means of §7 is a
> predicate over a state or over a pre/post pair; `Body.lean`'s `exec` is big-step and has no
> intermediate state to name. **The construct exists at both ends and the statement exists at
> neither.** `messung/GABBROV-V1.md` §3 carries it with its three siblings.

---

## 4. Three outcomes, never two

Automatic verification is undecidable in general. A tool with only passed and not-passed must
guess when in doubt.

| outcome | |
|---|---|
| **passed** | The obligation is met. Checked, not supposed. |
| **refuted** | It is not — with a counterexample as a concrete state. |
| **undecided** | GabbroV does not get through. With obligation name and reason. |

Undecided is the same grip as "stop rather than estimate". The outcome writes the obligation
back into the manifest as `open` — the state it was already in. The ratchet over names keeps
running, only with one more worker.

**Sound, not complete.** Passed must always hold; undecided may occur often. Every
optimisation that touches this asymmetry is a defect.

---

## 5. Assumptions — the silent failure path

The axiom layer already has a falsification discipline: `falsified(probe_…)` against real
hardware, `unfalsifiable("qemu64 has no x2APIC")` with a reason.

That checks the assumption against the world. It does **not** check it against itself, and
that is a different question:

**Contradiction.** If the assumptions are mutually incompatible, every obligation is provable.
Everything passes, nothing looks wrong, and it never reports itself. Remedy: have a model
sought for the assumption set. No model means rejection of the set, not use of it.

**Vacuity.** Even consistent assumptions can make a precondition unsatisfiable — then the
postcondition holds trivially and the check says nothing.

Both are cheap and only buildable early. They belong to the same class as `W16` and the
aborting measurement run: a tool that looks plausible and measures nothing.

> **And the V1 walk found three rows that are booked TWICE — here and under `obligation`.**
> The ten fragments carry exactly three `progress` clauses, and all three stand in the source
> as `assume` declarations already:
>
> | the `assume` | the same name as `progress` | ALSO booked in `PFLICHTEN.md` as |
> |---|---|---|
> | `F04.gab`:33 `device_completes_or_faults` | `FRAGMENTE.md`:887 | **L42**, logic obligation |
> | `F05.gab`:87 `client_calls_or_endpoint_revoked` | `FRAGMENTE.md`:981 | **L46**, logic obligation |
> | `F10.gab`:62 `token_verbraucht` | `FRAGMENTE.md`:1656 | **L66**, logic obligation |
>
> `SYNTAX.md`:1074 states the rule — *"`progress` names WHO ends it — an assumption about the
> environment, with a falsifier"* — and `F10.gab`:60 repeats it as the reason its own `assume`
> is there: *"without `assume` the name stands in no manifest."*
>
> **Two of the three (L42, L46) are among the ten V1 could not say — and the reason they cannot
> be said as obligations is precisely that they are not obligations.** Moving them is a
> correction to the manifest, not a construction. *What separates L66, which the fragment does
> hold, is not the construct but the referent of the named predicate: `token_verbraucht` is
> about the program, the other two are about the world.*
>
> **DONE 2026-09-03 — and the paragraph above was right about the fact and wrong about the
> place.** All three rows now carry the rebooking in `PFLICHTEN.md`'s fourth column
> (`S003`/`S004` + the declared `assume` and its `falsifier`). The verification found a
> stronger witness than the source reading: ***the emitted manifest never double-booked
> them.*** `gabbro annahmen` lists all three; `gabbro pflichten` emits **no** obligation from
> any `progress` clause — F04 emits one obligation and it is `reg QUEUE_SIZE requires`, F10
> emits two and neither is the loop. **So "here and under `obligation`" names one real place
> and one that does not exist**: the double booking was `PFLICHTEN.md`'s `L` column against the
> assumption manifest, and nothing GabbroV reads was ever wrong.
>
> **What the counts did — measured, not subtracted.** `PFLICHTEN.md` stays at
> `239 = 173 K + 66 L`, because its third column is machine-vs-subject and the tree's own rule
> is that *a discharged obligation still counts*. What moves is **GabbroV's** population:
> 66 − 3 = **63**, of which **8** are not sayable and **55** are. §11's `G1` note is updated at
> its own place. `messung/GABBROV-V2.md` §1

---

## 6. Who checks — the certificate question

Automatic checking runs over SMT. So the question arises at once: if Z3 delivers the verdict,
what is Lean for?

| | |
|---|---|
| **A** — Lean only notation, Z3 decides | simple; but Z3 sits in the trust base |
| **B** — Lean decides with tactics | clean base, weak automation |
| **C** — Z3 searches, Lean recomputes | A's automation, B's base |

**C.** The solver delivers a certificate, Lean's kernel recomputes it. No certificate means
undecided; a false one falls at the recomputation. Z3 is thereby not on the trust list.

That fits the house line: §0 says of the plumbing *"it compiles" is a function of the source,
not of solver luck*. For the logic, solver luck cannot be avoided entirely — but one can
prevent it from being **believed**.

Because the plumbing drops out completely, the formulas land in bitvector and linear
arithmetic instead of quantifier-heavy memory work. Those are exactly the theories with the
best certificate situation. The cut is what makes C realistic in the first place.

---

## 7. The specification language is a fragment of Lean 4

Arbitrary Lean 4 is higher-order dependent type theory; every SMT solver fails at it at once.
Specifications are therefore Lean terms of a particular type, with outlined means: predicates
over values, integer and bitvector arithmetic with overflow behaviour, aggregation over table
domains, pure helper functions in the translatable part.

A specification outside the fragment is **rejected**, not approximated. The commonest way such
tools become unsound is a translation that does not understand something and leaves it out.

**One demand already stands.** «B13» hangs on aggregation: `refcount == count(s in slots :
s.object == o)` is the core bookkeeping of the capability system and cannot be said in `pred`.
On the Lean side aggregation is a matter of course — the fragment must carry it, or the same
gap simply moves one level up.

> **Measured 2026-09-02: the demand is real, and it is one of THREE.** The walk over all 66
> found two more, and the largest is not the one written down here:
>
> | demand | rows | recorded above? |
> |---|---:|---|
> | aggregation — `count` over a table domain | 1 | **yes** |
> | folds that are not `count` — *the FIRST x with P* | 2 | no |
> | **bounded reachability — `place reaches place via field`** | **5** | **no** |
>
> **And the language already has the third.** `SYNTAX.md`:717 carries
> `reach = place "reaches" place "via" ident`, `parse.rs`:2117 builds `PredArt::Erreicht` from
> it, and a probe through the unchanged checker passes with 0 errors. The Lean channel refuses
> it by name (`LeanReason::Quantified`). ***The argument this section makes about aggregation
> applies to it word for word.***
>
> Two further corrections this section owes its next reader:
>
> * *"predicates over values"* reads as ONE state, and **20 of the 66 take two** — an
>   obligation's meaning is a relation between a pre and a post state.
> * The value domain is not wide enough for three rows: `Memory(Region)`, `Dma(DmaRef)` and
>   `Reply(ReplyRef)` carry RECORDS as payload, and `Value` has four forms of which `present`
>   carries one `Int`. The tree already books the price by name
>   (`LeanReason::ConstructedValue` — *"the price is a model extension"*). A `tagged` WITHOUT a
>   payload costs nothing; the price is the payload.

---

## 8. The one semantics

GabbroV checks obligations that GabbroC produced, against a meaning of Gabbro. GabbroC's
correctness proof uses one too. **It must be the same one.**

If they are two formalisations believed to be equal, then passed is valid in GabbroV's model
and the translation is correct in GabbroC's model, and a defect in the difference is invisible
to both.

Because the manifest is the interface, the question narrows agreeably: not the whole language
semantics must agree, but the **meaning of the obligation texts**. That is a smaller, more
sharply outlined object — and the first concrete step of work is to write it down for a
handful of real manifest lines.

> **Done 2026-09-02, and the carrier question that hung over it is answered.**
> `messung/LEAN-REICHWEITE.md` had measured that 101 of 119 place mentions name a carrier
> absent from the export's own dictionary — this section's hazard in the flesh. **Counted over
> one file, both channels, one binary: the split runs between the CHANNELS, not inside the one
> GabbroV reads.** `gabbro lean` says `wellFormed` over `"Kappenraum"` while its bodies address
> `"c"`; `gabbro pflichten --lean` says `"c"` in the hypotheses and `"c"` in the bodies, and
> `"Kappenraum"` does not occur in it at all.
>
> **So GabbroV can proceed on today's manifest — and the exemption is exactly as wide as the
> composition gap.** The obligation channel buys its consistency by dropping the table
> identity, which is harmless while each obligation is its own theorem over its own state.
> *The moment two obligations are linked — V4's whole point — the carrier becomes a
> cross-routine identity, and it is a PARAMETER NAME.* **The carrier question is not V0's
> blocker; it is V4's.**

---

## 9. Trust base

`SPRACHE.md` §0 names today's: *"The checker is unverified; the trust sits at three named
places: checker, syntax-directed lowering, one `iasm` emission site."*

GabbroV **adds** to that list, it does not replace it:

| # | element | note |
|---|---|---|
| 1–3 | checker, syntax-directed lowering, the one `iasm` site | today's state, from §0 |
| 4 | M1–M4 as carriers of the plumbing obligations | carries §1; without them GabbroV is silently unsound |
| 5 | meaning of the obligation texts in the manifest | small, reviewable, unprovable |
| 6 | translation Lean fragment → SMT | keep it small; rejection instead of approximation |
| 7 | Lean 4 kernel | external |
| 8 | the assumption set | probes against hardware, satisfiability against itself |

**Z3 is not on it** — that is the purpose of §6C.

Point 4 is the one easily overlooked. GabbroV may ignore alias, races and termination only
because M1–M4 carry them. As long as the checker is unverified, *passed* is a statement under
the assumption that it is right.

---

## 10. Stages and gates

| stage | content | gate |
|---|---|---|
| V0 | fix the meaning of the obligation texts for a handful of manifest lines | in writing, against real lines from `PFLICHTEN.md` |
| V1 | Lean fragment, translation, rejection outside it | the 66 L obligations of the ten fragments expressible — or named which are not |
| V2 | assumption check: satisfiability, vacuity | the assumption set of the ten fragments has a model |
| | *costed 2026-09-02; **the halves SPLIT 2026-09-03***| **the set is 8, and every one is a PROSE SENTENCE** — so `G5` can neither fire nor be cleared. The cost is not a solver call but the formalisation, and it is harder than V1's because the assumptions speak about the world. `messung/GABBROV-V1.md` §6 |
| **V2a** | **vacuity — BUILT 2026-09-03** | `programmlogik/gabbrov/V2.lean`, `lean` exit 0, no `sorry`. **Of the 55 sayable obligations, 31 carry a precondition and NONE is vacuous.** The check is not a search: `vacuous_sound` proves that a condemned precondition has no model at all. **And it fires** — driven against a deliberately vacuous `requires`, where an obligation whose postcondition is `False` passes. `messung/GABBROV-V2.md` §2 |
| **V2b** | **satisfiability — NOT started, and deliberately** | the eight assumptions are still eight German sentences. *A second V0, and the harder one.* |
| V3 | certificate checking in Lean | share with a recomputed certificate measured |
| V4 | write-back into the manifest, ratchet over ~~names~~ **the LINE** | one real `obligation` from `open` to `passed` |
| | *the key decided 2026-09-03, and it is NOT the name* | **`(name, class, text)`, the anchor only as a last resort.** A name is `aushaengen :: ensures #1` — an ordinal, and 79 of 113 lines carry one; swap two conjuncts and name, class, anchor and state are all unchanged. **A ratchet over names would carry `passed` from the old obligation onto the new one without a word.** The three reachability figures, the price of the key in edits, and why the anchor is out: `messung/BERICHT-O3-RATSCHE.md`, re-runnable with `./messung/gabbrov/ratschenschluessel.py` |

V1 before everything else, because it is the one stage that can fail without any tool being
built: if the existing 66 logic obligations cannot be said in the fragment, the cut is wrong,
and that before a line of code exists.

> **V1 is measured, 2026-09-02: 56 of 66 stand as a `Prop`.** ~~`G1` does not fire.~~
> `programmlogik/gabbrov/V1.lean` is the measurement — `lean` accepts it with exit 0, no
> `sorry` and no `native_decide`, and the count is read off the file rather than written
> beside it. **The stage's own gate is met** — the ten that do not stand are named one by one,
> which is what the gate column asks — **and the falsifier `G1` is a separate question this
> run cannot answer**; §11 says why. *What §12.1 said — "that is the first measurement and it
> needs no tool" — was half right: it needs no tool to be BUILT, and it needs one to be
> BELIEVED.*

---

## 11. Falsifiers

| ID | condition | consequence |
|---|---|---|
| G1 | A noteworthy part of the 66 L obligations is not sayable in the fragment | cut wrong; fragment or expectation anew — **but see below: "a noteworthy part" is no threshold, so this row cannot be evaluated in either direction** |
| G2 | Certificate coverage stays low | §6C does not carry; choice between Z3 in the base and weak automation |
| G3 | The share of *undecided* stays high | not a push-button tool but a pre-sorter |
| G4 | A passed obligation turns out to be false | soundness broken: obligation meaning, translation or M1–M4 |
| G5 | The assumption set has no model | every obligation passed so far is unchecked |

G4 is the one that does not show up by itself — the same class as the aborting measurement run
and as `W16`. It needs samples against real behaviour, not against the tool.

> **`G1` HAS NO THRESHOLD, and that is the finding — 2026-09-03.**
>
> ~~G1, measured: it does not fire.~~ The condition in the row above reads *"a noteworthy
> part"*. That is not a number, so **no count clears it and no count trips it**, and the
> sentence this paragraph used to carry was a judgement wearing a measurement's clothes.
>
> **The threshold is not being supplied now.** One chosen after 56 of 66 is on the table would
> be chosen to clear it — a rule pulled to fit a result, which the folder books as `R2`. The
> honest move is the cheaper one: *say what was counted, and drop the verdict.*
>
> **What was counted, and it is unaffected:** ten of the 66 do not stand as a `Prop`, and they
> fall into four classes of which **two are not an expressiveness gap at all** — two rows are
> assumptions booked as obligations (§5), and one is a statement about a second, mutated
> program. The genuine gap is four rows wide and is one missing means: ordering and atomicity.
> *That sentence needs no threshold, which is exactly why it survives the withdrawal.*
>
> **And since the rebooking of the same day the numbers are smaller and the gap is the same
> width.** GabbroV's population is **63**, of which **8** are not sayable: three that need a
> record payload in `Value`, one that quantifies over programs, and **the four ordering rows,
> untouched.** ~~`G1` fires less than before~~ — that phrasing is the withdrawn one in its
> smaller clothes; what is true without a threshold is the part after it: *the correction
> removed rows, not a gap.*
>
> **What replaces `G1` are `E1` and `E2` of `AUFTRAG-GABBROV.md` §1**, and the property that
> matters about them is not that they are stricter but that they were **written down before
> the runs they judge**. `E1` is a comparison of two line counts and admits no exception; `E2`
> counts decided against undecided against a **named** exception list in
> `dokumente/AUSNAHMEN.md`, so the list cannot grow quietly the way a percentage can.

---

## 12. Open questions

1. ~~How many of the 66 L obligations are sayable in the fragment?~~ **Answered 2026-09-02:
   56, and the ten that are not are named one by one** (`messung/GABBROV-V1.md`). *Restated
   2026-09-03 after the rebooking: **55 of 63**, because three of the 66 were never
   obligations* (§5). *The
   sentence that stood here — "that is the first measurement and it needs no tool, the
   obligation texts stand in `PFLICHTEN.md`, one can write them down in Lean one by one and
   count how far one gets" — was right about the method and wrong about the tool.* Writing
   them down one by one is exactly what was done; `lean` is what made the count a measurement
   instead of a reading, and it is what caught a `42` that had been written before it was
   counted.
2. ~~Does the fragment carry aggregation?~~ **It must, and it must carry two more means
   besides** — folds that are not `count`, and bounded reachability, which is the larger of
   the two and which the LANGUAGE already has. §7 carries the table.
3. How does the meaning of the obligation texts relate to what the Isabelle proofs assume?
   §8 decides. **Still open** — this run measured the LEAN channel against itself, not the two
   provers against each other, and `messung/LEAN-REICHWEITE.md` records that the two exporters'
   goal sets are disjoint: *no obligation in this tree has ever been stated by two provers.*
4. Which Caprock and Velve units get GabbroV, which do not? Product decision.
