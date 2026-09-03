# GabbroV — the audit of Gate 2, of design C, and of the manifest

*Started 2026-09-03 from tree `393d866`. This file is the report, written as the run
proceeds and committed with each finding. Every count names the command that produced it.
This lane BUILDS nothing except where it says so at the site.*

**Machine note.** `free -g` beside every local run. Solver directory on the server would be
`gabbro-vm`, but see §0 — the solver is not there.

---

## 0. Two premises of the mandate, measured before anything was used

**`z3` is on THIS workstation and is NOT on `ki-pc-fisch-101`.** The mandate states the
opposite and it is the wrong way round.

```
which z3                        # no z3 in $PATH
/opt/verus/z3 --version         # Z3 version 4.16.0 - 64 bit
ssh ki-pc-fisch-101 'which z3; ls /opt/verus/z3'
                                # z3: command not found
                                # ls: cannot access '/opt/verus/z3': No such file or directory
```

So every solver call in this report is local, and that is not a breach of `CLAUDE.md`: a
`check-sat` on a 2–140 KB file is not a build. `free -g` at the start of the run reported
**31 GB total, 19 available**. The one call class that could have grown — the 60 s
reachability timeouts of §2.5 — was re-run with the memory watched.

*Reported rather than worked around, because a lane that quietly runs locally against an
instruction to run remotely leaves no record of which of the two was wrong.*

**The worktree was three commits behind `master` at start** (`01d69b2`), and none of the
five files the mandate names existed in it. `git merge --ff-only master` before the first
measurement, as `CLAUDE.md` requires. *A lane that measures a tree without the subject in it
gets a clean, meaningless zero.*

---

## 1. Question 1 — what is actually wrong with GabbroV?

**The answer is the third of the three readings the mandate offers, and it is the good one:
the corpus is wrong, three times over.** Two of the three refutations were re-derived by a
hand that had not seen the first encoding, and both came back with the same verdict and a
sharper reason.

### 1.1 How the second encodings were kept independent, and where that discipline leaked

*The mandate asks for "a second encoding, written without looking at the first". I had
already read `messung/gabbrov/L01.smt2`, `L40.smt2` and `L05c.smt2` before that sentence
became actionable, so **my own second encoding could not have been blind.*** Rather than
write one and call it independent, the second encodings were given to three separate agents
that carry none of this conversation, each with:

* an explicit prohibition on `messung/gabbrov/`, every `*.smt2` in the tree, and the four
  GabbroV documents;
* a packet of SOURCE only — the fragment excerpt, `Body.lean`'s model, `V1.lean`'s helpers
  and the row's own `Prop`, copied into a scratch directory;
* the verdict convention (`unsat` = passed, `sat` = refuted, `unknown` = undecided) and the
  premise rule, but **no hint of what the first encoding found**.

Two of the three disclosed, unprompted, that the shared scratch directory listed files from
their siblings, and that they had opened none of them. *A disclosure nobody asked for is the
only evidence of isolation worth having.*

**The leak that remains, named:** the packets were assembled by me, and I chose what went
into them. A row's premise supply is exactly what the experiment is about, so the choice of
excerpt is itself an encoding decision. What the three did NOT get from me is any modelling
decision — representation, theory, bound, control — and that is where all three diverged.

### 1.2 `L40` — refuted twice, and the second encoding proves the stronger claim

| | first encoding (`messung/gabbrov/L40.smt2`) | second encoding (independent) |
|---|---|---|
| representation | `(_ BitVec 8)`, `schritt` as a 4-clause disjunction | `(_ BitVec 8)`, `step` as a 4-clause disjunction, **skolemised witness** |
| verdict | **sat**, 0.016 s | **sat**, 0.014 s |
| witness | `#x00` | `#x00` — DEVICE_STATUS = 0, the initial state |
| control | none | **`L39` = `unsat`, 0.015 s** |
| stronger claim | asserted in prose | **measured: `unsat`, 0.014 s** |

The two agree on the verdict and on the witness. **What the second encoding adds is the part
the first only asserted.** The first says in prose *"no declared transition reaches 0 from
anywhere"*; the second put that to the solver as its own file — `∃p q. step(p,q) ∧ q = 0` —
and got **`unsat` in 0.014 s**. The claim is now measured.

It also brought two instruments the first did not have, and both matter:

* **A control.** `L39` through the same encoding comes back `unsat` while `L40` comes back
  `sat`. Without it, a `sat` on `L40` is compatible with an encoding that says `sat` to
  everything. *`GABBROV.md` §11 calls `G4` the falsifier that does not show up by itself; a
  control is the cheapest thing that makes it show up.*
* **A named vacuity hazard in its own encoding.** `L40`'s antecedent is
  `DEVICE_STATUS = .int v`. If that place could hold `.absent`, the antecedent would be
  unsatisfiable and `L40` would pass **vacuously** — a `passed` that means nothing. The second
  encoder wrote the totality assumption down as an assumption rather than letting it sit
  inside the model. *That is `V2.lean`'s subject appearing inside a `V1` row, and neither
  document connects them.*
* **A liveness probe on the step relation**: all four declared pairs `sat`, an invented fifth
  `unsat`. A typo that dropped a clause would have handed `L40` a free refutation.

**Verdict: the refutation holds, and it is stronger than reported.** «B26» is not "the reset
is unverified" and not even "one state has no reset" — the four declared transitions are a
strictly ascending chain `0 → 1 → 3 → 11 → 15` with no edge back to `0` at all.

### 1.3 `L05` — refuted twice, and the second encoding measured the repair

The second encoding shares almost nothing with the first: `Value` as a four-constructor SMT
datatype rather than a two-form `Opt`; `World` as `(Array Place Value)` with array
extensionality carrying the frame; the body threaded through **seven** worlds `w0..w6` rather
than collapsed into one nest of `ite`s; `N` pinned to 4 to make the decisive files
quantifier-free.

| | first | second |
|---|---|---|
| `L05` verdict | **sat** | **sat**, 0.13 s |
| `cdt_wohlgeformt` ∧ one detached slot | **unsat**, 0.02 s (bound 6, N symbolic) | **unsat**, 0.03 s at N = 4 **and `unsat`, 0.01 s at symbolic N** |
| encoding-soundness control | none | **`s = WURZEL` → `unsat`, 0.10 s** |
| repair candidate | named in prose as an open question | **measured, and it FAILS** |

**The central finding is confirmed by two disjoint encodings:** `cdt_wohlgeformt` quantifies
over `slots of c` — the whole table — and `reachesIn` falls to its `| _ => false` arm the
moment it meets an absent parent on a non-root slot. One free slot anywhere falsifies the
invariant outright. `release_slot` sets `used = false` and never clears `parent`; `unlink`
clears `parent` and never clears `used`. **The invariant cannot hold over any table that is
not completely full and completely linked.**

**And the second encoding settled the question the first left open.** Gate 2's closing note
proposes the repair — *"`cdt_wohlgeformt` needs `forall s in used slots of c`"* — as an open
item. Measured:

* the `used`-guarded invariant IS satisfiable (`sat`, 0.07 s) — so the repair is livable;
* **but `L05` is STILL refuted under it** (`sat`, 0.14 s). `unlink` *requires* `used` and does
  not clear it, so it leaves a slot marked used with a cleared parent. ***`used` is not the
  right guard.***

The second encoder also found the sharpest form of the defect, and it needs no body at all:

> `unlink`'s `ensures c.slots[s].parent == None` **contradicts its own
> `maintains cdt_wohlgeformt`** for every `s != WURZEL`. The two clauses stand four lines
> apart in one signature.

*A defect visible in the signature was found by a solver and by nobody reading the file for
three weeks.* That is the best available answer to `GABBROV.md` §3's question about where
GabbroV would earn its keep.

### 1.4 `L01` — refuted twice, and the second encoding SPLITS the missing premise in two

This is the row where the two hands diverge most, and the second one is right.

| | first (`messung/gabbrov/L01*.smt2`) | second (independent) |
|---|---|---|
| `cdt_wohlgeformt` in the base | no — added in a third run (`L01c`) | **yes, in the base**, encoded as a rank function |
| degeneracies forbidden | none | **all** — no self-pointers, `t != s`, no post-state self-loop |
| base verdict | **sat**, 0.021 s | **sat**, 0.022 s |
| «B14» as a premise | one premise, flips to `unsat` (`L01b`) | **two directions, measured separately** |
| encoding-soundness control | none | **goal asserted POSITIVELY is also `sat`** |

**The verdicts agree. The reason does not, and the second is finer.**

*The first encoding treats «B14» as one thing.* The second put each direction to the solver
on its own:

| candidate premise | verdict | is it «B14»? |
|---|---|---|
| forward mutuality `slots[u].next == Some(n) => slots[n].prev == Some(u)` | **`unsat`**, 0.018 s | yes |
| **backward** mutuality `slots[u].prev == Some(p) => slots[p].next == Some(u)` | **`sat`** (ground at N=3, 0.021 s) | yes |
| siblings share a parent `slots[u].next == Some(n) => slots[n].parent == slots[u].parent` | **`unsat`**, 0.019 s | yes |

**Only ONE direction of the mutual sibling chain is load-bearing**, and a third, different
«B14» statement repairs the row by a shorter route. *The first encoding's `L01b` says "the
premise that repairs `L01` is exactly the one premise the language cannot express, and no
other". The second says: there are at least two such premises, they are not the same
statement, and one half of the one the first named does not repair it.* The conclusion
survives — every repair is «B14» — but the sentence "and no other" does not.

**And the second counterexample is better than the first.** The first encoding's model gave a
slot its own parent, which is why `L01c` exists at all. The second forbade every degeneracy
*and* carried `cdt_wohlgeformt` from the start, and is still `sat` at N = 3:

> Slot 0 is `WURZEL`. Slot 1 is being unlinked, with `prev = Some(2)` and `next = Some(0)`.
> The body's line `c.slots[n].prev_sibling = c.slots[s].prev_sibling` writes `Some(2)` into
> **slot 0's** `prev_sibling`. **The root has acquired a predecessor** — at a slot `unlink`
> never meant to touch as a root.

*A counterexample that survives `cdt_wohlgeformt` and every non-degeneracy constraint is a
different quality of evidence from one a reader can dismiss as nonsense.*

**One more thing this run produced without being asked for it, and it corroborates §2.3.**
Two of its files came back `unknown` at the 60 s cap — the quantified forms (c) and (e) — and
it settled them by **grounding at N = 3**, where they answer in 0.021 s. *A hand that had
never heard of the reachability wall hit it, diagnosed it as the quantified encoding, and
worked around it the same way.*

### 1.5 So which of the three readings is it?

**The corpus.** Not the obligations, not the specifications, not the encoding:

* **not the encoding** — two rows were re-derived by hands that had not seen the first, in
  representations that share no design decision, and both landed on the same verdict. Both
  second encodings carry a **control that comes back with the opposite answer**, which the
  first encodings did not have. An encoding that says `sat` to everything is ruled out by
  measurement rather than by care.
* **not the specifications** — `L40`'s and `L05`'s Lean `Prop`s were read straight out of
  `V1.lean` by both hands. The disagreement is not about what the obligation says.
* **the corpus** — «B26» is a transition table with no edge to `0`; `cdt_wohlgeformt` is an
  invariant no non-full table satisfies. Both are defects in `messung/fragmente/`, and both
  were found in under 30 ms.

**Said plainly, as the mandate asks: this is a good outcome.** A tool whose purpose is to
find exactly this found three of five drawn blind, and two independent hands confirm two of
them. *The Gate 2 number is not void; it is better witnessed than when it was reported.*

---

## 2. Question 2 — does design C hold as mathematics?

**It holds as an argument and it is not yet a thing.** Two of its three load-bearing steps
have no implementation at all, the one that does is better than the document claims, and the
wall the document treats as physics is an artefact that this run removed.

### 2.1 Trust-base points 5 and 6, measured in lines

§9 lists them as *"small, reviewable"*. Measured:

| # | element | §9's word | lines today |
|---|---|---|---:|
| 5 | meaning of the obligation texts in the manifest | *"small, reviewable, unprovable"* | **not code** |
| 6 | translation Lean fragment → SMT | *"keep it small; rejection instead of approximation"* | **0** |

```
grep -rniE '\bsmt\b|smtlib|\bz3\b' crates/ instrumente/ --include=*.rs --include=*.py --include=*.sh -l
crates/gabbro-check/src/emit.rs          -- unrelated
crates/gabbro-check/src/refinement.rs    -- ONE comment, about a format not chosen
instrumente/zaehle-theorien.py           -- Isabelle's `smt` TACTIC
instrumente/pruefe-zahlen.py             -- the same tactic
```

**There is no Lean-to-SMT translator in this tree.** Point 6 cannot be "kept small" because
it does not exist; §9 describes a component in the present tense that has never been written.
What stands in its place is `messung/gabbrov/*.smt2` — **393 lines of hand-written SMT-LIB
covering five obligations** (`wc -l messung/gabbrov/*.smt2`), plus the 21 files this run's
second hands added.

*And point 5 is worse placed than point 6, because point 6 at least has a shape.* Today the
manifest carries `aushaengen :: ensures #1`, so "the meaning of the obligation text" is: read
the source, find the function, count conjuncts. §3 of this report measures what that costs.

### 2.2 The translation that DOES exist is total, and the compiler enforces it

§7's demand — *"a specification outside the fragment is rejected, not approximated"* — is met,
mechanically, by the channel that exists. **This is the one place the document undersells
itself.**

```
crates/gabbro-check/src/lean.rs                      2 200 lines
programmlogik/Gabbro/Body.lean                         663 lines   (the meaning, hand-written once)
```

Every translation function returns `Result<String, LeanReason>`:

```
fn place_term(o: &Ort, c: &mut Ctx)   -> Result<String, LeanReason>      :605
fn expr_term (e: &Expr, c: &mut Ctx)  -> Result<String, LeanReason>      :643
fn pred_term (p: &Pred, c: &mut Ctx)  -> Result<String, LeanReason>      :739
fn block_term(b: &Block, c: &mut Ctx) -> Result<String, LeanReason>      :884
fn stmt_term (s: &Stmt, c: &mut Ctx)  -> Result<String, LeanReason>      :896
```

and `LeanReason` carries **33 named arms**, one per missing thing — the enum's own doc line
says why a single "not supported" would have been wrong: *"each arm names a different missing
thing -- a single 'not supported' would hide that they have different prices."*

**Totality is not a promise here, it is a type.** `expr_term` matches `ExprArt` with **no
wildcard arm** — the last arm is `ExprArt::FnWert(_) | ExprArt::Grund { .. }` — so `rustc`
refuses the file if a new expression form is added and left unhandled. `pred_term` likewise
ends at `PredArt::Quantor(_) | PredArt::Element(_, _) | PredArt::Erreicht { .. }`. Every
wildcard that does occur on a translation path resolves to a named refusal:

```
:709  _ => Err(LeanReason::CallInExpression)
:998  _ => return Err(LeanReason::CompoundAssign)
:1093 _ => return Err(LeanReason::MatchNotOption)
:1100 _ => Err(LeanReason::MatchNotOption)
:785  _ => false      -- `is_option_value`, a predicate, not a translation
:833  _ => {}         -- an item-collection loop
:946  _ => None       -- a local closure whose `None` becomes :998's Err
:1333 _ => {}         -- an item-collection loop
```

**So: it does not silently drop what it does not understand.** The document's fear is
well-founded and the code already answers it — *for the Gabbro-to-Lean direction.*

**And that is the sting.** The channel this measures is not point 6. Point 6 is
Lean → SMT; `lean.rs` is Gabbro → Lean. **§7's property is proved for the channel that
exists and unproved for the channel §9 names**, and the two are easy to confuse because the
document discusses them in one breath. *The `.smt2` files of this run and the last one ARE
the point-6 channel, and their refusal discipline is a person being careful.*

### 2.3 The round trip is not closed — and Gate 2 exercised the direction design C does not need

Design C: *"the solver delivers a certificate, Lean's kernel recomputes it."* Two measurements.

**First: Z3 does emit certificates for the two rows that came back `unsat`.**

```
sed 's/(set-option :produce-models true)/&\n(set-option :produce-proofs true)/;
     s/^(get-model)/(get-proof)/' messung/gabbrov/L23.smt2 > L23-proof.smt2
/opt/verus/z3 L23-proof.smt2
```

| row | verdict | certificate | distinct proof rules |
|---|---|---|---:|
| `L23` | unsat | **167 lines, 8 631 bytes** for a 39-line problem | **20** |
| `L39` | unsat | 23 lines, 1 273 bytes | 8 |

`L23`'s rule histogram: `unit-resolution` 16, **`rewrite` 16**, `mp` 15, `monotonicity` 8,
`def-axiom` 8, `proof-bind` 5, `hypothesis` 5, `trans` 4, `symm` 4, `quant-intro` 4,
`lemma` 3, `refl` 2, `not-or-elim` 2, `mp~` 2, `iff-true` 2, `iff-false` 2, `asserted` 2,
`and-elim` 2, `sk` 1, `nnf-pos` 1.

*`rewrite` is the joint most frequent rule and it is the one with no fixed inventory* — it
stands for a simplifier step, so a checker for it is a checker for the simplifier. **There is
no Lean checker for any of these twenty rules in this tree**, and `programmlogik` has no
mathlib by policy (`lakefile.toml` says why). So `G2` — *"certificate coverage stays low"* —
is not answered by "Z3 produces a proof": the proof exists and nothing can read it.

**Second, and it outranks the first: Gate 2 produced no `passed` that a certificate would have
protected.** Of the five rows, two came back `unsat` and three came back `sat`.

> **A `sat` is a MODEL, and a model needs no certificate and no kernel.** It is re-checked by
> substitution, which is decidable and cheap. Z3 sitting in the trust base does not matter for
> a refutation at all.

So the three refutations — the entire content of the Gate 2 finding — are **sound whatever one
thinks of design C**, and the two `unsat`s, the only place design C bites, were never
certificate-checked. *Gate 2 measured the direction in which the trust question is empty.*
That is not a criticism of the run; it is what a first sample of five is likely to produce.
But it means **`G2` is completely open after Gate 2**, not partly answered by it.

**The chain today, counted in mechanised steps:**

```
Gabbro source  --human-->  PFLICHTEN.md row  --human-->  V1.lean Prop  --human-->  .smt2  --> z3
```

Three human steps, zero mechanised. `GABBROV.md` §2's sentence — *"GabbroV does not read the
Gabbro program. It reads the manifest"* — describes none of them. §3 measures how far that is
from today.

### 2.4 The wall is an ARTEFACT, and this run removed it

**This is the finding of question 2**, and the mandate names the consequence itself: *"a fixed
encoding that makes 20 answer would change the whole project's outlook."*

First, reproduced exactly (`./messung/gabbrov/lauf-L05.sh 16 19 20 21 22`; `free -g`: 31 total,
19 available):

```
  bound=16    bytes=11393     answer=sat      time=  0.11s
  bound=19    bytes=15125     answer=sat      time=  0.35s
  bound=20    bytes=16497     answer=unknown  time= 60.05s
  bound=21    bytes=17933     answer=sat      time=  0.25s
  bound=22    bytes=19433     answer=unknown  time= 60.10s
```

**Then the same files, with nothing changed but the solver's random seed:**

```
./messung/gabbrov/ohne-schranke/lauf.sh          # PART 1
  bound=20  seed=0   answer=unknown   time= 60.08s     <- the default; what §2.5 measured
  bound=20  seed=1   answer=sat       time=  0.09s
  bound=20  seed=2   answer=sat       time=  0.20s
  bound=20  seed=7   answer=sat       time=  0.40s
  bound=22  seed=0   answer=unknown   time= 60.07s
  bound=22  seed=1   answer=sat       time=  0.14s
  bound=22  seed=2   answer=sat       time=  0.25s
  bound=22  seed=7   answer=sat       time=  1.13s
```

**Six of six non-default seeds answer, in 0.09 to 1.13 seconds.** The bound is not the
variable; the seed is. *A wall that moves when you change the random seed is not a wall — and
"non-monotone in the bound" was the visible half of "not a function of the bound at all".*

**And the second half removes the bound instead of the seed.** `cdt_wohlgeformt` is *"every
slot reaches WURZEL via parent"*, and `V1.lean` renders it as `reachesIn`, an `ite` chain
unrolled to the table's `count`. That unrolling is the only reason a bound appears in the file
at all. The same predicate has a bound-free characterisation as a **rank**:

> `rank(WURZEL) = 0`, and for `x != WURZEL`: `parent(x) = some p`, `rank(x) = rank(p) + 1`,
> `1 <= rank(x) < N`.

A rank witnesses reachability, so a model of the rank form is a model of the reaches form and
**a refutation transfers**. The negated goal needs no depth either: `unlink` sets
`parent[s] := None`, so for `s != WURZEL` the unrolling falls to its `| _ => false` arm at the
first level, at every depth. `messung/gabbrov/ohne-schranke/gen-rank.py` carries the argument
in its own docstring.

```
./messung/gabbrov/ohne-schranke/lauf.sh          # PART 2
  N=20       bytes=1365   answer=sat      time= 0.029s
  N=22       bytes=1365   answer=sat      time= 0.027s
  N=64       bytes=1365   answer=sat      time= 0.031s
  N=4096     bytes=1369   answer=sat      time= 0.037s
  N=80256    bytes=1371   answer=sat      time= 0.030s
```

**The corpus's own number — `F01.gab`:56, `const NSLOTS : u32 = 80256` — answers in 0.030 s,
and the file does not grow.** 1 371 bytes against 140 KB at bound 64 and 16 497 bytes at the
bound that timed out. *The four orders of magnitude §2.5 reports between where the solver
stops and where the obligation lives are four orders of magnitude of unrolling, not of
difficulty.*

Both controls hold, and without them the paragraph above would be worthless:

```
CONTROL A -- the same file with s = WURZEL. It MUST say `unsat`.
  N=20       answer=unsat    time= 0.016s
  N=80256    answer=unsat    time= 0.016s
CONTROL B -- is the PREMISE alone satisfiable? An `unsat` premise passes everything.
  N=20       answer=sat      time= 0.028s
  N=80256    answer=sat      time= 0.029s
```

**Independent corroboration, and it arrived without being asked for.** The blind second
encoder of `L01` — which had never heard of §2.5 — hit `unknown` at the 60 s cap on two of its
own quantified files, named the quantification as the cause, and settled both by grounding at
`N = 3`, where they answer in 0.021 s. *Two hands, two encodings, the same wall and the same
door out of it.*

**What this does and does not settle.** It settles that DEMAND 3 is not blocked by
tractability: `L05` is decidable at the corpus's own size, today, on this hardware. It does
**not** settle that every reachability obligation has a usable rank characterisation — a rank
is a *witness* for reachability, and the direction needing care is the one where reachability
must be **proved** rather than refuted, i.e. an `unsat`. *Four of the five reachability rows
(`L04`, `L09`, `L15`, `L16`) were not drawn and were not measured.* The Gate 2 closing note
asks whether these rows need "an axiomatised transitive closure instead of an unrolling"; for
the refutation direction the answer is **yes, and it costs 1 371 bytes.**

### 2.5 §6's missing sentence — WRITTEN, and its second half is the finding

The mandate permits this exception if the lemma is genuinely one theorem. **It is, and it is
one line.** `programmlogik/gabbrov/V2.lean` §1.1; `lean` accepts the file with exit 0 and
`grep -c sorry` is 0:

```lean
abbrev Assumptions := World → Prop

theorem vacuous_under_assumptions
    (pre : Pre) (h : vacuous pre = true) (A : Assumptions) :
    ∀ w : World, A w → holds w pre = false :=
  fun w _ => vacuous_sound pre h w
```

`A` is universally quantified over every assumption set there could ever be, so the theorem
needs none of the eight German sentences — **it does not touch §9's stop-list**, and it is a
stronger statement than one about the eight would have been. The axiom footprint matches the
existing `vacuous_sound`:

```
#print axioms GabbroV.V2.vacuous_under_assumptions   -- [propext, Quot.sound]
#print axioms GabbroV.V2.detection_is_incomplete     -- [propext]
```

**And the second half of §6's sentence is where the value is.** §6 also says the check is
*"sound in the detection direction and INCOMPLETE"*, and incompleteness is the claim that the
implication runs one way — a counterexample, not a caveat. It is now exhibited:

```lean
def preOpen : Pre := [.eq (.global "x") (.int 1)]     -- has a model; the check stays silent
def APins : Assumptions := fun w => w (.global "x") = .int 0

theorem detection_is_incomplete :
    ∃ (pre : Pre) (A : Assumptions),
      vacuous pre = false ∧ (∀ w : World, A w → holds w pre = false) := ...
```

> **The licence protects `vacuous` verdicts. V2a produced none.**
>
> ```
> LEAN_PATH=.lake/build/lib/lean lean programmlogik/gabbrov/V2.lean
> "register entries (L10 and L60 each contribute two arms): 30"
> "  vacuous:      0"
> "  not vacuous:  30"
> "  undecided:    0"
> ```
>
> All thirty verdicts are `notVacuous`, and `notVacuous` is exactly the side
> `vacuous_under_assumptions` does **not** carry. Every one of them can flip once the eight
> assumptions are formalised, and the run had no way to see it coming — the assumptions were
> not among its inputs.

*So `GABBROV.md` §10's V2a row — "of the 55 sayable obligations, 31 carry a precondition and
NONE is vacuous" — is true and provisional in a way the row does not say.* The theorem that
licenses running the check early is also the theorem that dates its result. **That is a
correction to the reading of a green run, not to the run**, and it is why the sentence
belonged in the file rather than in a report: a reader of `V2.lean` now meets it beside the
count it qualifies.

