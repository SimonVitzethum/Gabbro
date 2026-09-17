# Plan — the user's logic, stated in Gabbro, checked by Lean

**[PROPOSED]** A route by which a person states their logic in the `.gab` source, GabbroV
discharges what it can, **Lean 4 checks every discharge**, and the report names what is carried
and what is open. No percentage appears anywhere in it.

The point is not to remove Lean. It is to remove Lean *from the user's desk*: the prover stays
under the floor as the checker of every verdict, and a person who never opens a `.lean` file
still gets a machine-checked answer.

> **The sentence the whole plan rests on:** every verdict other than `open` cites a
> Lean-checked artefact. Nothing is believed because GabbroV said so.

---

## 1. Why this shape and not another

Whatever decides a logic claim **is a prover**. There are two ways to have one:

| | Trust base |
|---|---|
| GabbroV decides and is believed | a hand-written Rust prover, unverified, carrying the user's logic |
| GabbroV decides and shows its work | Lean, as everywhere else in this tree |

The first is the thing Strategy A exists to prevent, and it would be worse here than at the
checker: at the checker a mistake can only reject good programs, while a believed logic verdict
lets a wrong program through with a green stamp.

So this is Strategy A a fourth time — after the checker, the binary rewriter and the solver.
That is not a coincidence; it is the building principle.

## 2. What the user writes

**[PROPOSED]** Design rule for every new form: *it must be decidable by construction on bounded
domains, or reducible to something a pass already carries.* A form that always lands in `open`
makes the tool less useful, not more — it adds ceremony and returns nothing.

Ordered by how cheaply a claim of that shape discharges:

| Form | What it says | How it discharges |
|---|---|---|
| `changes only <places>` | a frame tighter than the declared effects | the effects pass already computes the hull; the claim is a narrowing, checked against it |
| `never <pred>` / `always <pred>` | a state predicate over a bounded domain | evaluate over the domain; a decision procedure whose certificate Lean checks |
| `preserves <pred>` | the predicate survives this body | the existing `maintains` machinery, attempted rather than assumed |
| `after <f> never <g>` | an ordering claim over the call graph | the same shape as the phase and pairing passes |
| `case` table | for inputs in these classes, results in those classes | finite case analysis on bounded types |
| `ensures` | anything else | handed over, as today |

The first five are shapes the checker can attack. The sixth is the general escape, and it stays.

**[OPEN]** Which of the five earns its place. Each new form costs grammar, a pass, poison probes
and a register entry — so each must be justified by sites in the corpus, not by elegance. The
measurement that decides it: how many claim sites in real programs would use the form.

## 3. Four verdicts, not two

**[PROPOSED]** Every claim gets exactly one:

| Verdict | Means | Cites |
|---|---|---|
| `CARRIED` | a pass already establishes it; the claim is redundant and true | the pass sentence |
| `DECIDED` | evaluated over a bounded domain | the decision certificate, Lean-checked |
| `ORACLE` | closed by a solver as an untrusted oracle | the proof certificate, Lean-checked |
| `OPEN` | handed to the person as a Lean obligation | the obligation, as today |

`CARRIED` is worth having on its own: it tells a person that the sentence they just wrote was
already free, which is how ceremony gets removed from real code rather than from the teaching
corpus.

## 4. The report, without a percentage

The register keeps the rule that already governs GabbroV: **named, not as a share.** A percentage
lets the denominator move with whatever is convenient, and here the denominator is the user's own
choices, which makes it worse than elsewhere: *saying nothing would score best.*

So the report is three lists and their counts:

1. **Claims by verdict** — four counts, and every `OPEN` named with its reason.
2. **Unclaimed slots** — every place the program could carry a claim and does not. The denominator
   comes from the **program**, not from the user: a body that writes state has a slot whether or
   not anyone filled it. This is the blind-spot table one level up, and it is what stops silence
   from looking like success.
3. **Inert claims** — see below.

## 5. The honesty instrument: mutation over the user's claims

**[PROPOSED]** *A rule with no mutation against it is not covered, it is undamageable.* The same
sentence applies to a user's claim, and it is the reason this tool can be trusted at all.

`mutiere-nutzerlogik.py`: generate semantic mutations of a body, re-run the claims against each.

- a claim that **no** mutation falsifies is **inert** — decoration, and it is named as such;
- a mutation that **no** claim catches is **unseen** — a way the body can be wrong that nothing
  the person wrote would notice, and it is named too.

The report line is of the shape *«N mutations · M caught · K unseen; C claims · I inert»*.

**This is the coverage figure that cannot be improved by omission**, because the mutations come
from the body and not from the claims. It is `mutiere-pruefer.py` turned around: there it damages
the checker to measure the corpus, here it damages the body to measure the specification.

Nothing else in this plan is novel. This part is: specification coverage as a measurement rather
than a feeling. Test coverage everyone knows; *how much of what I promised is load-bearing* nobody
reports.

## 6. The criteria

**[PROPOSED]** In the shape of GabbroV's own E1 to E3, and subject to the same guardians.

**N1 — completeness of treatment.** Every claim in the source gets exactly one verdict. None is
skipped, none falls through a parse error, none disappears because a form could not be handled —
it gets `OPEN` with a reason. Checkable with one command, claim count in against verdict count
out, in **every** run. A deviation is a failure, not a hint.

**N2 — named openness.** Every `OPEN` is listed with its reason. **No percentage appears in the
output of this tool**, and a guardian fails if one does.

**N3 — no inert claim unreported.** Every claim that survives all mutations is named. A claim that
cannot break must say so, or the report flatters.

**N4 — no unseen mutation unreported.** Every mutation that no claim catches is named, with the
line it changed.

**N5 — every non-`OPEN` verdict cites a Lean-checked artefact.** The sentence from the head of
this document, as a mechanical check: a verdict whose citation does not resolve is a failure.

## 7. Lanes

**[PROPOSED]** Sized so that each lands on its own and leaves the tree green.

| | What | Gate |
|---|---|---|
| **182** | the verdict pipeline: four verdicts, the report shape, N1 and N2 with their guardian | claim count in equals verdict count out on the whole corpus; no percentage in any output |
| **183** | the first two claim forms — `changes only` and `never`/`always` — grammar, pass, poison probes, register | the forms are used by corpus sites that exist; each refusal has a probe |
| **184** | mutation over user claims, N3 and N4 | the run names at least one inert claim or one unseen mutation somewhere in the corpus, or the mutation catalogue is too weak and says so |
| **185** | decide-with-certificate over bounded domains, Lean-checked | one `DECIDED` verdict whose certificate a third party can recheck |

Lane **181** (the solver as an oracle with a certificate) supplies `ORACLE` and is already under
way. The four above do not wait for it: without 181 the pipeline simply produces no `ORACLE`
verdicts, which is a smaller report and not a broken one.

**[PROPOSED]** Order: 182, then 184, then 183, then 185. The honesty instrument comes **before**
the new claim forms deliberately — otherwise the first thing the tool does is invite people to
write claims it cannot yet tell them are decoration.

## 8. What this does not do

**[DECIDED]** Stated here so that nobody has to find it out.

- **It does not remove Lean from the chain.** It removes it from the user's desk. The distinction
  is the whole plan, and it must survive into the documentation and into anything said about the
  tool outside this tree.
- **It does not infer `ensures`.** What a function is *supposed* to do cannot be derived; a tool
  that guesses the postcondition guesses the specification, and the proof afterwards proves
  nothing. This is the one clause that stays hand-written.
- **It does not make an unproved claim safe.** `OPEN` is a debt, listed, and the count of debts is
  the number that matters — not the count of claims.
