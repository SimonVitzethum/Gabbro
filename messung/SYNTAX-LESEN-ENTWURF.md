# SYNTAX section draft: stable reads — read-only shared data (design only)

Status: DESIGN ONLY, no implementation. Worktree lane-102, base 58d6b83,
2026-09-11. Sources: `crates/gabbro-check/src/nebeneinander.rs` (shared
reads may overlap freely; only shared writes need a common lock),
`grammatik/Grammatik/Interferenz.lean` (frame dependence `HaengtAb`,
preservation `stabil`, cuts S1–S6),
`grammatik/Grammatik/InterferenzAllgemein.lean` (`StabilSchritt`,
`StabilKette`), and the section 11 `concurrent` row of
`dokumente/SYNTAX.md` at this base. No new measurements were taken in this
lane and none were needed: the checker rule and the Lean shapes already
exist; this note owns the prose `dokumente/SYNTAX.md` will carry. Do NOT
edit `SYNTAX.md` itself from this lane; a later lane moves the text over.

Cross-reference warning, read first: the Lean names in section 3 below are
INTENDED names for `LesenStabil.lean`, a file owned by lane-101 on a
diverged branch. They were NOT copied from that file — the branches
diverged, so a read would coordinate against a stale text — and every one
of them is marked UNVERIFIED below. The integrator reconciles each
intended name against the file as merged, and drops the mark only there.

## 1. Where the text goes

Primary landing: a new subsection at the end of SYNTAX section 11
(Concurrency), after the per-form atomicity subsection and before the
`concurrent, effects, shared` subsection. Reason: atomicity answers the
write half of the shared-data question — which emitted forms lower to one
machine access — and this subsection answers the read half — which shared
reads survive a concurrent step without a lock, and why the contract
language may read them. The two subsections share one bounds paragraph
(x86_64, both optimisation levels, re-measure on port); the integrator
merges the duplicates when moving the text.

Two cross-references, both one sentence:

- The section 11 `concurrent` row appends the read exemption beside the
  write rule: shared reads overlap freely already today (W001 refuses
  writes, never reads), and the new subsection names the shape that makes
  them stable.
- Section 16.1 gains one row for `interferenz_erhaelt_vertraege` (and its
  requires-side twin) beside `kein_wettlauf`: the race theorems order
  conflicting accesses, the stability theorems preserve frame-bound
  assertions across disjoint steps — ordered writes stay writes, preserved
  reads stay reads.

No grammar production moves with this draft: no spelling changes, no new
attribute, no new checker pass. The draft documents the class; the rule it
names (reads are free, writes need the lock) already runs.

## 2. Draft prose for the new subsection

> Stable reads. A carrier that no declared-concurrent body writes is
> read-only shared data, and every concurrent read of it is stable: the
> foreign frame never touches it, so disjointness holds by absence of
> writes, not by lock. The checker already treats reads this way — the
> pair check refuses overlapping shared writes and lets shared reads
> overlap freely — and the stability theorems say why the prose may rely
> on it: a foreign step in a disjoint frame preserves every assertion
> that reads only its own frame. The config-table shape is the standing
> instance: a table filled before the concurrent set starts and written
> by nobody inside it (dispatch tables, capability tables, calibration
> constants) needs no guard for readers, because there is nothing to
> exclude them from. What the shape costs is stated beside it: the
> read-only claim is a whole-set claim, so adding a writer anywhere in
> the set moves the carrier out of this subsection and under a lock, an
> atomic, or a pairing rule.
>
> Contract reads stay inside the frame. A `requires` or `ensures`
> predicate reads only its frame: the tables predicate (hT) names which
> tables the contract reads, the globals predicate (hG) names which
> globals, and the predicate answers alike on any two worlds that agree
> on both (`HaengtAb`). A foreign step whose frame is disjoint from
> (hT, hG) therefore preserves the contract verdict — that is `stabil`,
> applied once per side: the ensures side survives the step after it,
> the requires side survives the step before it. The footprint direction
> is assumed, not derived: that contract evaluation reads only its frame
> is a premise (hQ), booked as cut S1, and whoever proves the evaluation
> footprint substitutes it for the premise while the stability step
> stays unchanged. Local bindings need no frame entry — no thread shares
> them (cut S6) — and lock-shared carriers are excluded here by
> construction (cut S3): a pair writing one carrier under one lock is
> ordered by happens-before, not preserved by stability.

## 3. Per-form mapping to LesenStabil.lean (intended names, ALL UNVERIFIED)

Each row names the Gabbro read form, the stability claim this subsection
makes for it, and the intended Lean definition that carries the claim.
Intended means proposed by this lane, not taken from lane-101: the
integrator checks each name against `LesenStabil.lean` as merged and
reconciles or renames before moving the text into SYNTAX.md.

| Gabbro read form | stability claim | intended def (UNVERIFIED, reconcile on merge) |
|---|---|---|
| read of a table no declared-concurrent body writes (config-table shape: dispatch, capability, calibration tables) | stable without a guard; the foreign frame never covers the table, so frame agreement on it is automatic | `NurLesenTabelle` — the read-only table predicate over the concurrent set |
| read of a global no declared-concurrent body writes (frozen flags, published-once constants) | stable without a guard, same reason as the table row, on the globals side of the frame | `NurLesenGlobal` — the read-only global predicate over the concurrent set |
| read of a lock-shared carrier under the held lock (invariant-guarded read) | stable while the lock is held; excluded from the free rows above and carried by the carrier invariant, not by this subsection | `LesenUnterSperre` — the held-lock read shape, pointing at the `TraegerInv` discipline |
| atomic load and awaits load of a published payload | ordered by the memory model and the pairing rules, not preserved by stability; named here so no reader mistakes pairing for frame preservation | `LesenPaarung` — the exemption pointer, no stability claim of its own |
| read of an unshared carrier (`per cpu` cell, stack, boot-only table) | no stability question arises: one thread, one frame, nothing foreign | no def; the row documents the absence |
| contract read: `requires`/`ensures` evaluation over (hT, hG) | reads only its frame by premise (hQ); preserved across any disjoint foreign step on both sides | `VertragLiestRahmen` — the frame-read premise shape over the tables predicate hT and the globals predicate hG |
| whole-set read-only claim for one carrier across N declared bodies | the config-table claim folded over the chain: every step preserves every frame-bound reader assertion to the last world | `LesenStabilKette` — the N-thread fold, `StabilKette` specialised to reads |

Why each def is exactly the one named: the two `NurLesen` defs split the
frame the way the Lean frame is split — tables predicate and globals
predicate are already separate arguments of `HaengtAb`, so a read-only
claim that merged them would fit no premise. `LesenUnterSperre` is a
pointer, not a proof, because the lock-shared discipline lives with the
carrier invariant and cut S3 keeps it out of the stability induction.
`LesenPaarung` is an exemption row for the same reason the pair check
exempts payload places: pairing orders, stability preserves, and one
table row must say which rows belong to which theorem. The chain def is
last because it is the only one that quantifies over bodies: everything
above it is per-carrier or per-contract, and the fold is where the
whole-set cost (one new writer moves the carrier out) is discharged.

## 4. Open remainder (rides with the text, not against it)

The evaluation-footprint premise (hQ) is assumed per cut S1 and stays
assumed in this subsection; the text says so where the premise is used,
not in a footnote the reader finds later. Lock-shared writes stay
excluded per cut S3 — the happens-before order covers them, and the
subsection must count that openly: the mapping above covers read-only
and guarded reads and names pairing as the ordered remainder. The
two-thread step model (cut S4) bounds the prose the same way it bounds
the theorem: the N-thread fold is the chain def's business, and any
later lane that cites a three-body shape names the fold. Row-level
disjointness inside one table (the interim same-table write rule) needs
no row here at all: reads are free at every granularity the checker
distinguishes, so a finer index analysis would only ever move writes.

## 5. Self-check (this lane)

`dokumente/SYNTAX.md` untouched (this file is the draft, placement
proposed in section 1). `crates/` untouched; `grammatik/` untouched; no
build was run in this lane, full or otherwise; no emitter, checker,
probe, or test change. English prose throughout; table cells carry no
bold numbers; no ebnf fences. The Lean names in section 3 are intended
names with UNVERIFIED marks, not cross-branch copies; the integrator
owns the reconciliation.

(End of file - total 140 lines)
