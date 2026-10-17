# GabbroV — the user's logic against a Lean model of their program

*Consolidated 2026-10-17. It replaces the former `GABBROV.md`, `programmlogik/PLAN.md`,
`dokumente/GABBROV.md`, `passlogik/README.md` and `dokumente/GABBROV.md`, and
the measurement reports `messung/gabbrov/{GABBROV-ZERTIFIKAT,MANIFEST-COMPLETENESS,MANIFEST-TEXT}.md`
and the retired `messung/GABBROV-V2.txt`. History is in git. The data file [`programmlogik/gabbrov/KORRESPONDENZ.txt`](../programmlogik/gabbrov/KORRESPONDENZ.txt)
stays; the guardians that parsed the retired mapping table `PFLICHTEN-KORRESPONDENZ.txt` and the obligation
registers (`pruefe-manifest`, `zaehle-pflichten`) were retired on 2026-10-17 (see git history), so
no guardian reads those rows or the machine-read rows of this file (§5, §11) any more. GabbroV is
measured today by `instrumente/pruefe-gabbrov.py`.*

> **What GabbroV is, in one sentence.** The part of Gabbro that takes what a person must still
> say — the logic obligations of their program — states it as Lean, checks it against a model of
> the program computed from the **source text** by generic theorems, and names what stays open.
> It proves nothing about machine code; its proofs do not establish final-byte correspondence
> (that is the translation-validation route, `PLAN-UEBERSETZUNGSVALIDIERUNG.md`). Where it meets
> the goal theorem is the bridge of §14: it *derives* premise (b) of `BEWEIS.md` B1 for the
> programs the Lean front end elaborates.

**Section ids.** §1–§12 keep the numbering of the former `GabbroV` document (code comments cite
`GABBROV.md §2`, `§3`, `§5`, `§7.1`, `§11`). The former `programmlogik/PLAN.md` is §13; the id
map at the end lists which `PLAN.md` section lives where.

---

## 1. What Gabbro already does, and the cut

`SPRACHE.md` §0: *Gabbro proves everything except logic.* Plumbing — index, overflow, alias,
frame, lock, race, termination, phase, leafness, publication — is the checker's (M1–M4,
generated schemata, no SMT, no solver). **Logic** — *this function does the right thing* — is the
programmer's, and Gabbro **emits** every open logic obligation. Plumbing that rests on logic
(`SPRACHE.md` §8.3) falls constructively but is booked as logic. So the cut is narrow: **logic
and assumptions only**. Over the ten fragments of `FRAGMENTE.md`, the retired `PFLICHTEN` register
(counted by the retired `zaehle-pflichten`, booked 2026-09) books `239 = 173 K + 66 L`: about a quarter
of the obligations reach GabbroV.

**Components** (all in the tree):

| Component | Where | Role |
|---|---|---|
| the obligation manifest | `gabbro obligations` / `pflichten`, `crates/gabbro-check/src/pflichten.rs` | one line per open logic obligation (§2) |
| the manifest harness | `gabbro gabbrov pruefe --manifest M --spec S`, `gabbrov.rs` | each line against a specification: passed / refuted / undecided; E1 wired in |
| the Lean `Body` channel | `programmlogik/` (§13), `gabbro prove`, `lean.rs`, `beweis.rs` | the duties as Lean statements over a model of the body; GREEN / OWED / RED |
| the specification channel | `gabbro lean a.gab b.gab`, `programmlogik/gabbrov/V1.lean`, `V2.lean` | the program as a Lean datum; a specification written by hand (§7) |
| the Lean parser (T3) | `grammatik/Grammatik/Parser/` (§14) | source text → surface tree → `UProg` → G program, computed in Lean |
| the bridge | `bruecke/Bruecke/` (§14) | GabbroV's duties give premise (b) of the goal theorem |
| the proof-side census | `grammatik/Grammatik/GabbroV/` (17 files, ≈6 000 lines) | closing the person's linked-structure arguments, the shared-atomic rely, refusal census |
| the checker's own logic | `passlogik/` (§15) | the pass register's sentences as Lean theorems over models of the rules |

---

## 2. The interface: the manifest

`SPRACHE.md` §15 describes the obligation manifest the compiler emits per translation unit and
names its addressee as *"the programmer or an external tool"*.

**GabbroV does not read the Gabbro program. It reads the manifest.** (This is the sentence that
`pflichten.rs` cites.) It needs no program semantics and no verification-condition generator:
the checker has already computed and named the obligations. Three classes, three tasks:

| manifest class | GabbroV does |
|---|---|
| `obligation` | check against the Lean specification — the actual work |
| `assumption` | satisfiability of the set, vacuity, probe status (§5) |
| `closed` | nothing; keep the site |

**Format, version 2** (`pflichten::MANIFESTFASSUNG`, line one is `-- manifest-version 2`):

```
obligation<TAB>name<TAB>class<TAB>anchor<TAB>state<TAB>obligation text
```

`name` is `function :: subject`; `class` is the kind letter; `anchor` is `file:line` where the
obligation **arises** (for `V` the call site, while the text is the callee's clause); `state` is
`open` (GabbroV writes `passed`/`refuted` back); `text` is the predicate wording, cut by
`zeremonie::schnitt_bis` (whitespace folded, hard stop at 400 characters). Per kind:

| class | kind | name shape | text comes from |
|---|---|---|---|
| `R` | refinement | `f :: refines g` | the body of the `spec fn` named |
| `E` | preservation | `f :: <invariant>` | the `spec fn`, else the `table`/`group` invariant named |
| `N` / `F` | postcondition / foreign duty | `f :: ensures #n` | the `ensures` clause |
| `V` | precondition at a call site | `caller :: callee requires #n` | the callee's `requires` |
| `D` | device promise | `dev :: reg r requires`, `transition t [requires]` | the clause, or the `transset` move |
| `S` | loop invariant | `f :: loop invariant #n` | the predicate |
| `W` | unowned invariant | `w :: down` / `leaf` / `invariant n` | node type through guard, the leaf predicate, the predicate |

**Why the text field is in the line.** The name is `aushaengen :: ensures #1` — a function, a
kind and an ordinal. Swap two conjuncts and name, class, anchor and state are all unchanged; a
ratchet over names would carry `passed` from the old obligation onto the new one. The key is
`(name, class, text)`; the anchor is a last resort (`messung/gabbrov/ratschenschluessel.py`
measures the three reachability figures). The text is self-contained down to the identifiers,
not below them.

**E1, the completeness check, is wired into the tool**, not hung beside it: `zeige` counts the
records it wrote against `sammle` and the run ends with `E1 FAILED` on a divergence (a ninth kind
added to `Art` and forgotten in the print loop would otherwise be counted in the header and
printed in no line). The outer comparison — manifest lines against the GabbroV population — was
the retired `pruefe-manifest` (2026-10-17; not guarded today), which derived the split from the mapping table
the retired `PFLICHTEN-KORRESPONDENZ.txt` (states `CARRIED`, `BLOCKED`, `DROPPED`, `NO CLAUSE`), refused a
`BLOCKED` row whose fragment emits a register, and printed the 16-odd `K` lines it must not spend
as logic. **It was red by design**: when last run (2026-10-17) `43 of 63` obligations reached no
manifest line, with 20 lines carried, 13 blocked on one fragment's repair, 5 dropped and 25 with
no clause; two mapping rows (F01 `cdt_wohlgeformt`) name a line the run no longer produces and
need re-derivation. The honest ceiling without a language change is 24–25 of 63: a `claim`
with a `can_fail` block is an assumption with a falsifier, and a `format … where` is already
discharged by the decoder (a line for it would read `open` and be false).

**The order of a format change** (the rule that cost nothing and saved a silent failure): count
the readers first — three parse the plain text (`tests/beispiele.rs` red loudly; `messung/gabbrov/manifest-lage.sh`
(and the former `pruefe-zahlen`) would go *silently* wrong, the sum becoming `0`), seven tools
read the same register through `--lean`/`--isabelle` and are untouched, two registries know the
flags; then widen every reader to both formats **while the emitter still writes the old one**;
only then move the writer. A reader taught the new format after the writer moved has a window in
which it reports a number out of a format it cannot read.

---

## 3. The one exception, and it is real

§8.3 books a plumbing obligation that falls only via a logic invariant as logic. In practice
"Gabbro handles termination and invariants" holds *except* where the descent measure or the
restoration rests on a logic invariant: a `breaking` block that does not close with a generated
operation produces an `obligation` that lands at GabbroV. `D013` does not check that the
invariant really rests here, that the block restores it, or that `requires I` / `maintains I`
are barred inside it. The statement this site needs — *the invariant does not hold between the
two assignments* (`L34`) — cannot be said in the fragment of §7: `Body.lean`'s `exec` is big-step
and has no intermediate state to name. The goal theorem's machine G is small-step and carries the
order leg `folge` and the lock legs instead (`BEWEIS.md` B2; OFFEN O1-Rest).

## 4. Three outcomes, never two

**passed** (checked, not supposed), **refuted** (with a counterexample as a concrete state),
**undecided** (name and reason). Undecided is "stop rather than estimate"; it writes the
obligation back as `open`. **Sound, not complete**: any optimisation that touches the asymmetry
is a defect.

## 5. Assumptions — the silent failure path

The axiom layer already checks assumptions against the world (`falsified(probe_…)`). GabbroV
also checks them against *themselves*: **contradiction** (mutually incompatible assumptions make
every obligation provable — a model must be sought, and none means rejection) and **vacuity**
(consistent assumptions can still make a precondition unsatisfiable, so the postcondition holds
for free).

**The three `progress` rebookings (verified 2026-09-03).** The ten fragments carry exactly three
`progress` clauses (`F04` `device_completes_or_faults`, `F05` `client_calls_or_endpoint_revoked`,
`F10` `token_verbraucht`); a `progress` name must resolve to a declared falsifiable `assume`
(`S003`/`S004`), and the retired `PFLICHTEN` register had booked each also as a logic obligation (`L42`, `L46`,
`L66`). The emitted manifest never double-booked them: `gabbro annahmen` lists all three,
`gabbro pflichten` emits no obligation from any `progress` clause. The `K`/`L` column stays
(it is machine-versus-subject, and a discharged obligation still counts); what moves is
GabbroV's population, and the figure is derived by command, not by subtraction:

| | | source |
|---|---:|---|
| `L` rows of the ten fragments | 66 | retired `zaehle-pflichten` (booked 2026-09; historical) |
| of these, discharged by the assumption layer | 3 | same (historical) |
| **GabbroV's obligation population** | **63** | same (historical) |
| of the 63, not sayable in the fragment | 8 | `L11 L12 L13 · L24 L34 L50 L52 · L57` |
| of the 63, sayable | 55 | |

| | before | after | |
|---|---:|---:|---|
| `PFLICHTEN` register total (retired) | 239 | 239 | unchanged |
| GabbroV's obligation population | 66 | **63** | the three are discharged by the assumption layer |

(An older figure of "164 K" was never a measurement of the tree: it is what the counter's own
speech probe produces when an escaped pipe is miscounted; the tree measures 163 K anchored and
173 K in total.)

**Vacuity is built** (`programmlogik/gabbrov/V2.lean`, no `sorry`, no `native_decide`): a
precondition in the atom fragment (`eq p v`, `ne p v`) is *vacuous* iff two atoms clash, and the
verdict is **proved sound for every world** (`vacuous_sound`), not found by a search; a
satisfiable precondition gets a constructed witness. Of the 55 sayable obligations, 31 carry a
precondition and **none is vacuous**; the check can fire (driven against a deliberately vacuous
`requires`, an obligation whose postcondition is `False` passes — the reason a `passed` without
the check is worth nothing). The four invariant-shaped preconditions are answered by exhibited
worlds. **One neighbouring pathology the run found and left to the owner:** `L44` and `L53` are
tautologies (`absent ≠ int 0` is a fact about the datatype, `L44_is_a_tautology`); they say
nothing about any program. Satisfiability of the set of eight assumptions is **not started**: they
are eight prose sentences, and formalising them is a second V0, harder than the first.

---

## 6. Who checks: the certificate question

If a solver delivers the verdict, what is Lean for? Three routes: (A) Lean as notation, Z3
decides — Z3 in the trust base; (B) Lean decides by tactics — clean base, weak automation;
(**C**) Z3 searches, Lean's kernel recomputes the certificate — no certificate means undecided,
a false one falls at the recomputation, and Z3 is not on the trust list. The cut makes C
realistic (bitvector and linear arithmetic land in the theories with certificates).

**The ceiling, measured** (`python3 messung/gabbrov/cert-theorien.py`, 2026-09-09): of the 55
sayable obligations, **26** are quantifier-free in linear-integer/bitvector shape (rows `L10 L18
L19 L20 L21 L22 L26 L28 L30–L32 L35–L39 L44 L45 L47 L48 L51 L53 L55 L58 L63 L65`), 29 need
quantifiers (24 over a table domain), bounded reachability (5; unrolling is finite but not
tractable at the corpus bounds, answers at 21, silence at 20) or folds (3). 26 of 55 is the
**ceiling** for route C, not its yield — and two of the 26 (`L44`, `L53`) are tautologies. Whether
the certificate-checking build (V3) is worth that half is the owner's decision; it has not been
taken.

---

## 7. The specification language is a fragment of Lean 4

Specifications are Lean terms of a particular type, with outlined means: predicates over values,
integer and bitvector arithmetic with overflow behaviour, aggregation over table domains, pure
helpers. A specification outside the fragment is **rejected, not approximated** — the commonest
way such tools become unsound is a translation that leaves out what it does not understand.

**§7.1 — corrections measured.** "Predicates over values" reads as one state, and **20 of the 66
take two** (an obligation is a relation between pre and post state); the fragment holds all
twenty. The value domain was too narrow for three rows (`Memory`, `Dma`, `Reply` carry records;
`Value` has four forms of which `present` carries one `Int`) — the price is a model extension
(`LeanReason::ConstructedValue`); a `tagged` without a payload costs nothing.

**§7.2 — the demands the fragment must carry.** Aggregation (`count` over a table domain, `B13`:
`refcount == count(s in slots : s.object == o)`), folds that are not `count` (the *first* x with
P; 2 rows), and **bounded reachability** `a reaches b via field` (5 rows) — which the *language*
already has (`PredArt::Erreicht`) and the Lean channel now carries
(`(.reaches tab from to via count)`; `F01`: `total 17 goals 17 refused 0`). A fourth demand, **G1**
(2026-09-26, OFFEN O5), is of a second kind — premise supply: resolving an `option index into`
inside `pred` (`B14`, the `L02` mutual sibling chain). It is the difference between *refuted* and
*passed* on `L01`; today only `== Some(k)` comparisons check in `pred`, indexing *through* the
option stays blocked.

**The correspondence table** (`programmlogik/gabbrov/KORRESPONDENZ.txt`; the retired `zaehle-pflichten --korrespondenz`
held it): one row per Lean construct with its named
Gabbro counterpart, every name resolving where its side lives. Rows are `GREEN` (the nine
constructs `∧∨¬→`, `=≠`, quantifiers over table domains, `World`, `State`, `wrapTo`, `.int`,
`SpecShape`, `reachesIn`, `Atom`), `YELLOW` (Gabbro can, Lean cannot: ends undecided and needs a
`TODO.md` entry named in the row) or `RED` (Lean can, Gabbro cannot: a failure — the fragment is
taken back or the Gabbro side is built first). **RED is empty and must stay empty**; what keeps it
empty is the order: a demand gets a table row only when its Gabbro side lands first (`count`
and the `traverse` fold are `DEMAND` rows today).

**What the hand-written channel shows** (`programmlogik/beispiel/`): two `.gab` files are one
program (`lager.gab` declares the table, `betrieb.gab` writes into it through `use`).
`gabbro lean lager.gab betrieb.gab` exports every body as a `Stmt` datum, every precondition
it can say and the shape of every declared place — and **no specification**. A person writes
`Spec.lean` (for example `nur_dieses_fach`, a frame property with a quantifier no `spec fn` can
express). Three poisoned specifications each fall: one demands a value the body does not write, one demands
the cleared compartment stay untouched, one names a field no table declares. The third falls
with "unsolved goals", which reads like a fault in the program; `gabbro prove` (run by
`instrumente/pruefe-gabbrov.py`) holds every place a specification names against the program's place list and says the true thing.
What no dictionary catches: a typo from one real field to another proves a true statement about
the wrong place — the check bounds the hazard, it does not remove it.

## 8. The one semantics

The obligations GabbroC produced and GabbroC's own correctness proof must use **one** meaning of
Gabbro, or a defect in the difference is invisible to both. Because the manifest is the
interface, only the meaning of the *obligation texts* must agree. Measured 2026-09-02: the
split ran between the two *channels* (`gabbro lean` names tables by type, `pflichten --lean` by
parameter) and not inside the one GabbroV reads; the exemption is exactly as wide as the
composition gap — the moment two obligations are linked, the carrier becomes a cross-routine
identity and is a parameter name. **It is V4's blocker, not V0's.** Still open: whether the
meaning of the texts matches what the Isabelle-era proofs assumed; no obligation in the tree has
ever been stated by two provers.

## 9. Trust base

GabbroV *adds* to the list of `BEWEIS.md` E1: (4) M1–M4 as carriers of the plumbing (without
them GabbroV is silently unsound), (5) the meaning of the obligation texts (small, reviewable,
unprovable), (6) the translation Lean fragment → SMT (keep small; reject, do not approximate),
(7) the Lean kernel, (8) the assumption set. **Z3 is not on it** (§6, route C). Written down
for the *Body* channel: the parser (`crates/gabbro-syntax`), the export (`lean.rs`, 7 200 lines), the semantics (`programmlogik/Gabbro/Body.lean`, 3 245 lines) and the Lean kernel — and
explicitly **not** the passes. That the exported datum *is* the program stands in no theorem;
the answer to it is the Lean parser and the bridge (§14), which compute the duties from the source
text so that a wrong Rust print is a failed per-unit check and not a wrong theorem.

## 10. Stages and gates

| Stage | Content | State |
|---|---|---|
| V0 | fix the meaning of the obligation texts for real manifest lines | done in writing (§8) |
| V1 | the Lean fragment; rejection outside it | **built 2026-09-02**: 56 of 66 stand as a `Prop` (55 of 63 after the rebooking); the ten that do not are named in four classes, two of which are not an expressiveness gap at all (assumptions booked as obligations; a statement about a second, mutated program); the genuine gap is the four ordering rows (`L24 L34 L50 L52`) |
| V2a | vacuity | **built** (§5) |
| V2b | satisfiability of the assumption set | not started, deliberately |
| V3 | certificate checking in Lean | not built; ceiling 26 of 55 (§6) |
| V4 | write-back into the manifest; ratchet over **the line** `(name, class, text)` | not built |

## 11. Falsifiers

| ID | Condition | Consequence |
|---|---|---|
| G1 | a noteworthy part of the L obligations is not sayable | **withdrawn, 2026-09-03**: "noteworthy" is no threshold, so the row can be evaluated in neither direction, and a threshold chosen after 56 of 66 would be chosen to clear it. Replaced by `E1` and `E2` of the mandate, which were written down before the runs they judge: E1 compares two line counts and admits no exception; E2 counts decided against undecided against a **named** exception list (`dokumente/PRUEFER.md`) |
| G2 | certificate coverage stays low | the choice between Z3 in the base and weak automation |
| G3 | the share of *undecided* stays high | not a push-button tool but a pre-sorter |
| G4 | a passed obligation turns out false | soundness broken: texts, translation or M1–M4 |
| G5 | the assumption set has no model | every obligation passed so far is unchecked |

What is true without a threshold: GabbroV's population is **63**, of which 8 are not sayable —
three that need a record payload in `Value`, one that quantifies over programs, and the four
ordering rows. *The correction removed rows, not a gap.* G4 does not show up by itself (the same
class as an aborting measurement run); it needs samples against real behaviour, not against the tool.

| | | |
|---|---|---|
| **GabbroV's obligation population** | **63** | retired `zaehle-pflichten` (historical) |
| of these, discharged by the assumption layer | 3 | |

## 12. Open questions

1. *(closed)* How many of the 66 are sayable: 55 of the 63 (§10).
2. *(closed)* The fragment carries aggregation and two further means (§7.2).
3. How the meaning of the obligation texts relates to the Isabelle-era assumptions (§8). Open.
4. Which Caprock and Velve units get GabbroV, which do not — a product decision.

---

## 13. The Lean channel for the user's own logic (the former `programmlogik/PLAN.md`)

**The sentence it serves:** a person who wants to verify a Gabbro program formally proves **their
own logic and nothing else.** What is not their logic is carried by the model, the emitter or the
automation; where it is not carried it is either **named as an assumption** (a name a proof can
point at) or **refused** (a tag that says why) — never left in the person's lap silently.

### 13.1 What "own logic" means (former PLAN §1)

Own logic is what the person wrote and only they can know: an `ensures` that follows from what
the body does; an `invariant` that survives a pass because of what the pass changes; a `requires`
strong enough for the body; a `reaches`-chain still intact after a relink because of which
fields the relink touched. **Plumbing** is everything a person would write by hand in Lean before
their argument, the same for every program, and each item is carried by a named part of the model:

| Plumbing | Carried by |
|---|---|
| a call, a call in an expression, a call chain | `Contract`, `Frame`, `gabbro_calls` (rounds, answers rewritten into the goal); the emitter hoists calls out of expressions |
| a loop | `looprule_of_body`, `looprule_of_body_in`, `RunsLoopIn` |
| recursion, mutual recursion | `contract_of_duty_rec`, `contracts_of_duties_rec` (one induction over the shared measure; the emitter finds cycles) |
| the well-typed world, a read of the world, a declared range | `WF_store`, `gabbro_wf`, `Shape.intIn`, the `WF_*` witnesses, `gabbro_shape` |
| a `tagged` value and its payload ranges | `Shape.sum`, `Shape.caseOk`, `Shape.payloadOk` |
| an answer's shape and existence | `result_clause` in every `_post`; `gabbro_values` for shapeless answers |
| control flow | `gabbro_cases` |
| a store beside a read or a chain | `gabbro_split`, `store_here/elsewhere`, `chase_store_*` frame lemmas |
| arithmetic the checker did | `gabbro_bits`, `gabbro_mul`, `gabbro_divmod`, `omega` |
| quantified premises, hypotheses in shapes, the budget | `gabbro_instantiate`, `gabbro_forall`, `gabbro_open_hyps`, `gabbro_try` |

**Not own logic and not plumbing: the named assumptions** (§13.8). **Out of scope:** verifying
Gabbro itself (checker, emitter, model against emitted code).

### 13.2 Architecture (former PLAN §2)

```
unit.gab ──► gabbro pflichten --lean ──► Duty/<Unit>.lean ──► lean ──► GREEN / OWED / RED
                (crates/gabbro-check/src/lean.rs)      ▲                (gabbro prove)
                                       programmlogik/Gabbro/Body.lean (model + tactics)
                                       programmlogik/Proofs/<Unit>.lean (the person's file)
```

* **The model** — `programmlogik/Gabbro/Body.lean` (3 245 lines): `World`, `State`, `Value`,
  `Shape`, `Expr`, `Stmt`, `exec`/`step`/`eval`, the contract algebra, the typing, `chase`, the
  tactics of §13.4; it builds without `sorry` at every commit. `Coverage.lean` (§13.12),
  `KompositionBeweis.lean` (the composition: the environment-runs hypotheses `U1`/`U2` discharged:
  `umgebung_ok_of_runs`, `schleifen_ok_of_runsloop`), `Sicherheit/` (the S4 checker-parity range
  arithmetic; today only `Sicherheit/Ausdruck.lean` imports Mathlib — `Body.lean` imports `Lean` alone;
  Mathlib is allowed everywhere since 2026-10-08, pinned to the toolchain, precompiled via
  `lake exe cache get`).
* **The emitter** — `lean.rs` writes, per unit, `shapeOf`, every routine's body as a `Stmt` list,
  `_pre`/`_post`/`_writes`/`_requires`, every loop's `_inv`/`_body`, every foreign contract as an
  assumption, one theorem per duty (`_meets` for a routine, `_keeps` for a loop pass) with generated
  openings and `gabbro_auto2`, and the wiring `unit_closed`. What it cannot say it **refuses by tag**
  (`LeanReason`), and `pflichten.rs` prints the tag next to the duty.
* **The checker and CLI** — `beweis.rs`: `Stand {Gruen, Geschuldet, Rot, Aufbau}`;
  `gabbro prove|beweise [--template|--vorlage] [--model|--modell <dir>] <unit.gab>…` writes
  `Duty/<Unit>.lean`, builds the model with `lake`, holds `Proofs/<Unit>.lean` against it: GREEN
  (all proved, no `sorry`), OWED (which statements), RED (a Lean error), SETUP (no Lean / model);
  exit 0/1/3. `gabbro emit --proved` refuses C for a unit that still owes a proof;
  `--template --source` prints the file *pinned to the source text*, its duties computed by the
  Lean front end (§14).
* **The measurement** — `programmlogik/_pruefung/` (scratch, untracked): `lauf.sh` runs every
  generated module through `lean` and counts (it never stops at an error); `probe.sh <module>`
  shows what `gabbro_auto?` leaves; the retired `pruefe-lean-pflichten`
  ran the channel tree-wide (`gabbro prove` over the proof units is run by `instrumente/pruefe-gabbrov.py`).

### 13.3 The model (former PLAN §3.1)

A call reads its answer through `(ρ f t).1/.2`; `Frame ρ f writes` says a place outside the frame
is untouched. A loop over `slots of T` gets `0 ≤ k < count`; `RunsLoopN` adds a bound on the
**number** of passes (`by unvisited`: each slot at most once), the sentence the pass counter of
§13.11 rests on. `Shape` is `int | bool | opt | intIn lo hi | sum cases`; a `match` over a `tagged`
value never gets stuck on a case the type excludes (a soundness point of the obligation, not a
convenience). `chase` is the `reaches` chain with exact fuel and frame lemmas for a store into
another field, carrier, global or record field.

### 13.4 The tactics (former PLAN §3.2)

`gabbro_auto [lemmas] using Γ` runs a pipeline of about fifty steps, each under its own heartbeat
budget (`gabbro_try`, ≈11.3 M heartbeats in total; generated files carry
`set_option maxHeartbeats 11300000`): the model's simp set, `gabbro_cases` (at most 4 deep, the
decision written as `decide p = true/false`), `gabbro_calls` (every call against every contract
hypothesis, innermost first, 12 rounds, marks per goal), `gabbro_values`, hypothesis opening,
`gabbro_wf`/`gabbro_shape` witnesses, `gabbro_split`, `gabbro_instantiate`, late rounds *without*
the caller's list (`simp_all` clears a hypothesis it used up), arithmetic closers. The generated
closer is `gabbro_auto2` (the pipeline, run again on what it left). Lessons booked: `set_option
maxHeartbeats` inside a tactic block does not change the limit the check reads; a nested `by`
in a `have` *logs* its failure; a hole goal opened early never sees hypotheses added later
(hence innermost-first, and a hole phase that instantiates the round's calls a second time inside
each hole); the four `simp_all` steps are 33–70 % of a costly module's time, memoised once per goal,
one dropped (measured: the corpus without it, same `sorry`s, 417 s → 396 s). 43 % of a corpus run is
startup (0.88 s per module for `import Gabbro.Body`), and that, not the pipeline, is the next
speed step.

### 13.5 The emitter (former PLAN §3.3)

Contracts before duties (mutual recursion references forward); `ContractBelow`/`ContractBelowM`
with SCC wiring; parameter ranges in `_pre` and a `let` of a ranged type carrying its range in
every invariant in scope; arrays as pseudo-tables (`Rec.field`, static arrays, `elems of`,
`queue`, `lenof`); `aligned(e, n)` as `e % n == 0`; device carriers as the tag `DevicePromise`
(an assumption); calls hoisted out of expressions (not under `&&`/`||`); the result clause in every
`_post` (`∃ x, r = some (.int x) ∧ lo ≤ x ∧ x ≤ hi`, the bool, a sum with `caseOk`,
`∃ v, r = some v` for a shapeless answer, `none ∨ reason` for an error channel, `False` for
`-> never`). **The lock invariant** (2026-09-29): `locks L { … }` on a lock with an invariant is
`.call lock_acquire_L` (an assumed contract), the body, `.call lock_release_L` (precondition = the
invariant); probes: the retired `pruefe-sperre-beweis` (not guarded today).

### 13.6 The register of what the emitter decides (former PLAN §16, run 30)

`LeanCarried` in `lean.rs` has **54 variants, one per place the emitter writes a term**, with
`CarriedForm` saying which `Coverage.lean` form covers it (`Subterm` for a literal). The forcing
is a fact about the type: `place_term`, `expr_term`, `pred_term`, `domain_of`, `stmt_term`,
`block_term` return `Carried`, whose only constructor is `LeanCarried::term` in a module of its
own — an `Ok(s)` with a bare `String` does not compile. Seven forms are decided in the wiring
and stand in `CARRIED_BY_WIRING` (`callChain`, `callFrame`, `contractFromDuty`, `recursionSelf`,
`recursionCycle`, `recursionInLoop`, `declaredRange`). The first run of the correspondence found
**eight forms the emitter carried and `Form` never named**, six of them the carried half of a form
whose refused half was in the register all along ("the refusal was in the register because refusals
have an enum; the carry was not because carries had none"); all eight are now theorems.

### 13.7 What is left, and whose it is (former PLAN §5)

**§5.1 Own logic** — the person's argument: a `reaches`-invariant preserved across a relink (the
frame lemmas peel every store beside the chain; what stands is the store *into* the chain field
and the argument that the chain still reaches every node: `01-tabelle`, `F01`, `kapraum`, `55`);
a counter whose invariant does not bound the next step (closed since by the pass counter for five
of six units, §13.11); invariants that cannot survive their own routine (`09-ohne-zeiger`: a
specification problem of the example); empty bodies with an `ensures` (the syntax probe's, not
the model's). At the 2026-09-08 merged measurement **not one `sorry` in the corpus was plumbing**
(192 modules, 0 Lean errors, 25 `sorry` on nine files, each classified); on 2026-09-29, with the
lock invariant, 192 GREEN against 12 OWED. These counts are dated; the command is §16.

**§5.2 Gaps — plumbing still owed:** (1) counters in loops — built (§13.11); (2) refused forms —
§13.9; (3) recursion inside a loop — wired (§13.10); (4) hole goals — built and measured (§13.4).
New gaps from 2026-09-29, each needing a decision and not a tactic: the visited-set of a
`by unvisited` traversal (`57`: `RunsLoopN` bounds the passes and says nothing about covering the
domain), whether `tree { … }` implies parent consistency (`09`), disjunctive callee posts that
multiply the pipeline's splits (`126`: 94 goals, five minutes a compile), and the 64-call chain of
`tick_runde`.

**What a person does:**

```
gabbro prove --template unit.gab > programmlogik/Proofs/Unit.lean   # the file to start from
gabbro prove unit.gab                                                # GREEN / OWED / RED
gabbro emit --proved unit.gab                                        # C only when green
```

### 13.8 The assumptions, by name (former PLAN §6)

`Assumed ρ` per unit: every foreign contract (`extern fn … ensures`), every device promise (a
register read or write behind `transition`), every `walk` clause; `Initially s0`: a well-typed
world in which every invariant holds; two carrier names are two places (no aliasing between
declared carriers) and a record type is one object of the model; the checker and the emitter are
trusted, not verified. An environment-runs assumption (`Runs`, `RunsLoop`, `RunsLoopIn`,
`RunsLoopN`) is *assumed* and named wherever it is used.

### 13.9 The refused forms (former PLAN §9.1, §9.2)

One tag once stood over forms whose grounds differ; they are now separate tags. `fields of <format>`
is **carried** (the list is finite; where the body does not read the binder it collapses to the
body). `quantified-threads`: every other domain hangs on a declaration (`count N`, `tree`, `walk …
levels`), `threads` hangs on nothing — and **the language change that looks obvious is a synonym**:
`forall t in threads over T` and a mark at the table both emit `.forallSlots "t" 128 …`
byte-identically to `slots of T`, which a quantifier whose domain is an integer cannot tell apart.
The surface that would *mean* something has to say which slots are **live**, and Gabbro has no
liveness declaration; the refusal stays, with a measured ground, and `D024` refuses the one shape
that stated nothing (the binder as a plain number, `t < N`, true over the empty set and false over
the naturals; gift 690). `quantified-mappings` (hardware); `record-value` and `slot-record-array`
(refused for soundness: a record type is one object, so two slots' copies would be one place);
`layout-buffer-length` and `sizeof(T)` stay refused, because a number there would be a layout claim
Gabbro itself declines to make. A refusal that is **inherited** now says so: a clause refused
because the routine's body or `requires` has no term, a table invariant refused because one
routine that writes its carrier has none (one untranslatable invariant refused five duties).

### 13.10 Recursion inside a loop (former PLAN §9.3, §12.3)

`contract_of_duty_rec_loop_in` runs the induction over `decreases` *outside* the loop rule, so the
pass may assume the contract at the routine's entry state and owes in return that the measure has not
moved (`eval t' e = eval s0 e`). Wired shapes: one ranged loop; several loops, the call in one of them
(every loop then carries the measure — a probe found a real obligation that refusal had hidden);
a `retry`/`forever` pass (`contract_of_duty_rec_loop`: the induction is over the `decreases`, never
over the index). **A stack of nested loops stays refused**, and the ground is real: the inner loop's
rule would be a hypothesis of the outer pass, stated against the *routine's* entry state; the model
would need a theorem over a list of nested passes.

### 13.11 The pass counter (former PLAN §10)

`n <= passes` over a `traverse`: `passes` is a plain identifier (no keyword, no grammar-table row),
declared by a `traverse` for its `invariant` and by nothing else; a declared name of that spelling
wins. The model adds the ghost local `#pass` (bound to `0` before the loop, incremented as the
pass's first statement, nothing of it in the emitted C) and `RunsLoopN … np` (`ks.length ≤ np`);
`LoopRuleP` has the same conclusion as `LoopRule` from a state whose counter is zero. Where a loop
cannot count the emitter refuses with the tag `pass-counter`. Five of six counter units closed; the
sixth (`F06`) keeps two `sorry`: `w_i * 8 ≤ s.len` is the person's. A loop that may `return`
carries `(#returned ∧ post) ∨ (¬#returned ∧ inv)` and gets an `if #returned { leave }` guard
**only where the loop counts its passes** (applied everywhere it closed one unit and opened another).

### 13.12 The coverage theorem (former PLAN §13, and the lesson of §11.1)

The slogan is a theorem in `programmlogik/Gabbro/Coverage.lean`: `Form` enumerates the language's
forms (53 constructors, 40 carried by a general lemma at the 2026-09-08 count), `classify : Form →
Verdict` is total, and
`the_sentence : ∀ f, ¬ IsOwnLogic f → classify f = carried ∨ carriedByTactic ∨ assumed ∨ refused`,
with `ownLogic_is_the_persons` and `nothing_of_the_language_is_left_to_the_person` (no form whose
statement the grammar fixes is handed over). "The tactic closes it" is **not** a theorem — tactic
success is a property of a run, so `carriedByTactic` is a verdict whose `Discharges` is `False`.
Two general lemmas are false without a side condition, and the negations are proved
(`store_without_the_shape_can_break_WF`, `a_contract_says_nothing_where_its_precondition_fails`);
that is a statement about the emitter. **The guard** (the retired `pruefe-deckung`, now `cargo test -p gabbro-check --lib lean::deckung_tests`) holds the
hand-written mirrors `Form`/`Reason` against `lean.rs` (the population both ways, the order, every
tag and kind, an arm in `classify` for every form and no catch-all) and
`lean::deckung_tests` reads `Coverage.lean` at compile time. **Lesson (§11.1):** a register can be
one step behind its sibling (`PassCounter` stood in neither `LeanReason::ALL` nor
the retired `zaehle-lean`'s reasons: a refusal would have been counted in a balance line and named in no
reason line — smaller, the direction that flatters); *a test over a register must not take that
register as its own population.* **What no guard covers:** that `Form` is the whole grammar
(`parse.rs` against `Form` is a third register with no guard), and that the mapping names the
*right* lemma for a site.

### 13.13 The decision on `threads` and what was built instead (former PLAN §15)

Measured before designing: a context is an `entry` (a static entry point) and a thread is a runtime
object; seven contexts in five files in the corpus; `accumulates … per cpu` is cores, not threads.
The class "six duties" is two clauses once inheritance is counted. The design (surfaces A–D,
§13.9) found the obvious surface a synonym, and the register did not move — recorded as a result,
not a wasted run.

---

## 14. The bridge to the goal theorem, and the Lean parser

**T3, the Lean front end** (`grammatik/Grammatik/Parser/`, 19 files, ≈22 700 lines): a total lexer over a
closed vocabulary of 243 words (`Lexer.lean`; the Rust table prints 239 because five words stand in
two rows) behind a source-trust gate (`LexerVertrauen.lean`, `P060`–`P063`: bidi controls,
out-of-set identifiers, mixed scripts, invisible characters); fuel-indexed readers for expressions,
statements and items (`Ausdruck`, `Anweisung`, `Element`, `ElementTief`) with the reserved/contextual
split pinned (`WortStellung`: seventeen reserved words); a printer and round trip
(`Rundlauf*.lean`: every printable expression and statement parses back from its printed tokens;
the premise `gut` books the shapes that have no spelling); and the elaboration
`uebersetzeAllg`/`lowerAllg` — surface tree → `UProg` (plain data) → `declOf` and a G
`Programm`, for **the fragment `lean_g.rs` exports**: tables, locks with `Held`, `impl fn` with
pointer/index/range parameters, comparison contracts over slot reads, `old` and `result`, straight-line
bodies of slot writes, direct calls, a trailing return. Everything else is an explicit
`.error` (no new diagnostic codes).

**The bridge** (`bruecke/Bruecke/`, a Lake project over `grammatik` and the original `programmlogik`
sources, Mathlib-free, toolchain v4.33.1; ≈5 000 lines, 16 files plus the instances `Instanz104/108/130/69/73`):

* `Pflichten.lean` — computes, from the parser's `UProg`, the duty statements and the `Body` datum
  (`zuBody`, `meetsU`), so a wrong Rust print is a failed per-unit check (`Instanz*.lean`), never
  a wrong theorem; the Rust printer is checked against them.
* `Simulation.lean` (`bruecke_nutzer`) — **the simulation theorem**: for every unit the Lean parser
  lowers (`lowerAllg u = .ok …`) whose call graph has a rank and which passes the per-unit name
  checks, if every GabbroV duty `meetsU` is proved then every function meets `KoerperGutR`, the body
  obligation of premise (b), at every budget. The proof is the run simulation (`Lauf.lean`,
  `Realisierung.lean`): a G run under a contract- and frame-respecting handler and the Body run in an
  environment that answers every call as the run did end in related states with the same answer.
* `Atomar.lean` (`bruecke_nutzerA`) — with the atomic rely, on the parser fragment (no atomic global
  there, so the rely is empty); `grammatik/.../GabbroV/GvAtomRely.lean` adds the generic rely duty and
  the exact obstruction (`gv_rely_braucht_atomfreiheit`: without atomic-freedom the transfer fails).
* `Quelle.lean` (`nutzer_aus_quelle`) and `Vorlage.lean` — **the principle of 2026-09-30**:
  nothing in the compiler or checker is there for particular programs; GabbroV is proved right by
  **generic theorems over every source text**. `Pflichten src` is a `Prop` computed from the text; if
  the front end accepts `src` and it is proved, premise (b) holds for the unit built from what the
  front end produced. What a person supplies for a concrete text is an untrusted *witness*
  (`decide +kernel` against the pinned text) — a hint like a proof term; the statement stays the
  computed one. `gabbro prove --template --source` prints it.

**Coverage, honestly.** The bridge covers the parser's fragment only: instances 104, 108, 130, 69
and 73 are built (`bruecke/lakefile.toml`), a gift program exhibits the refusal of a call cycle
(`GiftZyklus`), and `GvZensus` (continue-on-refusal) ranks the first blockers over the corpus. Every
unit outside that fragment still carries (b) as an assumption; a unit *with* a shared atomic is not
bridged. **Open:** duties for atomic-bearing units from `Pflichten src`, the per-access
TSO-to-W/GX refinement, payload hand-off, whole-`World` stores to edge maps and the `chain`-domain
bridge (`GvBruecke.lean`: the single-chain case is `kette_gleicht`), the Rust exporter's remaining
form gaps (OFFEN O27). The Rust back end of the duty printer remains untrusted and checked against
the Lean computation.

**The person's linked-structure argument** (`GvVerkettung`, `GvTreeParent`, `GvKetten`,
`GvTraversal`, …): the declaration does *not* give a `reaches`-invariant (`deklaration_schliesst_eltern_nicht`);
the walk bound every `traverse` domain needs and pop-preserves-acyclicity for free lists are proved
once, generically.

## 15. `passlogik` — the checker's logic, in Lean

A formalisation of the **specification** of the passes, not of `crates/**/*.rs` — no line of Rust was
read when it was written, so the model can *contradict* the Rust. A proved sentence over a model is
not a statement about the checker; **the seam between the model and `gabbro-check` has not been
checked by anyone**, and the descent from statement to effect (what a body does, statement by
statement) is in no file — it is booked as an assumption in four (`B1`, `L1`, `P2`, `R1`): theorems
about a model whose carrying assumption is unmodelled, on exactly the surface where most findings
fell historically.

Measured now: 7 files (`Passlogik/{Bereich,Wirkung,Kosten,Rang,Terminierung,Linear,Phasen}.lean`,
3 033 lines), **137 theorems** (46 / 21 / 22 / 13 / 14 / 10 / 11), `grep '^axiom'` finds none,
`grep sorry` finds none, no Mathlib (`passlogik/lakefile.toml` has no `require`; the project builds in
seconds), toolchain v4.33.1. `Abnahme.lean` calls `#print axioms` for every theorem — the axiom table
is derived, not kept. It is the formal basis of the passes' sentence register and does not replace
`gabbro paesse` (0 of 216 sentences are PROVED there).

| File | Carries |
|---|---|
| `Bereich` (M1) | interval soundness (`add/sub/neg/mul_korrekt`: the product over the four corners, the open item of `Intervall_Aussen.thy`), meet and hull as infimum and upper bound, termination of narrowing, the overflow criterion `passt_dann_kein_ueberlauf` (`M104`), V1/V2/V3 narrowing, facts die at a write |
| `Wirkung` (`E005`/`E008`) | `huelle_deckt`: two **local** conditions (callee ⊆ caller, list covers own body) carry the **global** statement; a cycle does not disturb it; the hull is a *lower* bound (`absage_haelt_unter_unvollstaendigkeit`: a refusal over the partial view holds over the full one — what is lost is completeness, not refutation); the 2026-08-24 fail-open error as a theorem; the theorem holds over the *kind*, not the effect (`writes a` covers `writes b`) |
| `Kosten` (`K001`) | `L1_obere_schranke`: the computed cost bounds every run; recursion breaks the premise (why `K001` fell at every recursive function: a self-call counts the declared bound, so the rest of the body must cost zero); the measured factor-3 undercount of the old rule |
| `Rang` (`H006`) | rank strictly rises, so no circular wait; `>=` not `>` (equal ranks admit the classic deadlock); an unknown rank is not a rank (`U005`); the rank rule is sufficient, not necessary |
| `Terminierung` (M4) | the descent theorem; `by unvisited` by counting; `S005` and `S008` check that a measure is *named*, not that it *falls* (two counter-runs); `retry` ends through `bounded` only if a pass costs something; `forever` ends explicitly not |
| `Linear` (M2) | every path consumes exactly as often as the pass counts; linear is not affine (the gap is the leak); a base-name comparison blurs `p.a`/`p.b` in the *unsafe* direction |
| `Phasen` (`O001`–`O006`) | the flow never goes back; a step in a loop is refused because of `O003`; the order is finite so the chain is finite |

**Findings where the specification gave way while formalising** (each pinned by a theorem): V2 says
"has type" and not "is intersected with" — read literally it is sound but not always a narrowing;
`E008` compares the *kind*, so `huelle_deckt` holds over kinds; **no text says a `retry` pass costs
at least one operation**, so "ends through `bounded`" does not follow without it (a decision for
`SPRACHE.md`/`SYNTAX.md`); "every program terminates" is false (`forever`), and there are five
loop forms with or without a measure; recursion is a second source of non-termination
(`K008`/`K009` with `decreases`, necessary and not sufficient). **Explicitly not proved:** the seam
to the Rust, the instruction-level descent, the emitter (`K1`: `Ĉ(constant expression) = 0` is a
claim about the generator), alias, progress (`keine_verklemmung` does not say every thread gets
its turn), completeness anywhere (every theorem has the shape "whoever passes satisfies X"),
the memory-model half (`A10`), IEEE, and the sharpness of interval multiplication and the
division interval. The assumptions `A1–A3`, `B1–B3`, `K1–K4`, `R1–R3`, `T1–T3`, `L1–L3`, `P1–P3` are
premises of theorems or choices stated in file headers; there is no global axiom list.

**Build.** `cd passlogik && lake build` (the project, seconds, peak memory dominated by `lean`'s
~500 MB base load per process); a single file: `lean Passlogik/Bereich.lean`. Two concurrent first-time
`lean` invocations against a fresh `elan` toolchain block on its lock with 0 % CPU (not a hang).
The first `lean` call downloads the toolchain (minutes). Next most valuable (from the former
README): a differential test between `kostenK` here and what `gabbro pruefe` computes on a file
(the seam), deciding the `retry` cost rule, deciding V2's reading, and the three domain theorems of
`K001` §6 that would turn `kosten.domaenenschranke` from `CONJECTURED` to `PROVED`.

---

## 16. Re-measuring, and what could not be re-measured

| Figure | Command |
|---|---|
| population, rebooking | retired `zaehle-pflichten` (63 / 3, measured 2026-10-17; historical, not guarded today) |
| correspondence table | retired `zaehle-pflichten --korrespondenz` (not guarded today) |
| manifest completeness | retired `pruefe-manifest` (red by design, §2; not guarded today) |
| manifest, per fragment | `bash messung/gabbrov/manifest-lage.sh` |
| the Lean channel over the corpus | `programmlogik/_pruefung/lauf.sh` (local scratch; **not** concurrently with `cargo test` in one tree: `gabbro prove` rebuilds the model and replaces the `.olean` the running `lean` reads — 52 phantom errors on 2026-09-08), retired `pruefe-lean-pflichten` |
| the specification channel | `gabbro prove`, run by `instrumente/pruefe-gabbrov.py` |
| the coverage register | `cargo test -p gabbro-check --lib lean::deckung_tests` |
| the bridge | `cd bruecke && lake build` |
| `passlogik` | `cd passlogik && lake build Abnahme` |
| certificate ceiling | `python3 messung/gabbrov/cert-theorien.py` |

**Not re-measured here** (no `lake`/`cargo` run was allowed): the corpus counts of §13.7 (192 modules,
25 / 12 `sorry`/OWED, dated 2026-09-08 and 2026-09-29), the 31-of-55 vacuity result, the 26-of-55
ceiling, the build state of `bruecke/` and `programmlogik/`, and every axiom set. The reports the
`Spec.lean` header cites for the bridge (`messung/GABBROV-BRUECKE-REPORT.md`,
`GABBROV-SERVER-REPORT.md`, `GABBROV-V1.md`, the mandate `AUFTRAG-GABBROV.md`) are not in the tree.

## Appendix — old → new ids

| Cited as | Now |
|---|---|
| `GABBROV.md` §1, §2 (the manifest sentence), §3, §5, §7, §7.1, §11 | unchanged |
| `programmlogik/PLAN.md` §1 (what own logic means) | §13.1 |
| `PLAN.md` §3.1 (the model, the result clause of `-> never` = `False`), §3.3 (the emitter, the budget) | §13.3, §13.5 (and §13.4 for the budget) |
| `PLAN.md` §5.1, §5.2 (own logic, gaps; items 1–4) | §13.7 |
| `PLAN.md` §6 (assumptions by name) | §13.8 |
| `PLAN.md` §9.1 (refused forms; "a language change, not a model change"), §9.2, §9.3 | §13.9, §13.10 |
| `PLAN.md` §10, §12.3, §13, §16 (run 30) | §13.11, §13.10, §13.12, §13.6 |
| `PLAN.md` §11.1 (a register one step behind) | §13.12 (the lesson) |
| `PLAN.md` §15 (`threads`) | §13.9 and §13.13 |
| `PLAN.md` §12.4 (two measurement collisions) | §16 |
| `dokumente/GABBROV.md` | §7 |
| `passlogik/README.md`, `dokumente/GABBROV.md` | §15 |
| `messung/gabbrov/MANIFEST-*`, `dokumente/GABBROV.md`, the retired `messung/GABBROV-V2.txt` | §2, §5, §6 |
