# MUSE-REPORT-1018: Exact review of author 868 (bound-check elimination rule)

Lane 1018, clone `/home/simon/Dokumente/gabbro-muse/a1018`, branch `muse/1018`.
Report-only exact review. I own only this file; no source was touched.

Identity check: `git rev-parse HEAD` = `b040b155159f47629542b0083e2f0a8a607f2b4c`,
branch `muse/1018`, tree clean. HEAD equals the SNAPSHOT base. Proceeded.

CANDIDATE: 868 b161382e70525c34e7013213253308c6c7b91eb2
VERDICT: ACCEPT

Acceptance is bounded as stated in scope §6 below; the bound does not change
the verdict.

## 1. What was reviewed

The pinned snapshot (`.tmp/review/SNAPSHOT.json`) contains exactly three files:

- `MUSE-REPORT-868.md`
- `grammatik/Grammatik.lean` (one appended import line)
- `grammatik/Grammatik/X86/OptBoundElim.lean` (new, 252 lines)

I inspected the exact `PATCH.diff`, the full candidate file copy
(`.tmp/review/author-868/grammatik/Grammatik/X86/OptBoundElim.lean`),
`OWNER-TASK.md`, `MUSE-REPORT-868.md`, `BUILD-EVIDENCE.json`, and checked
every load-bearing claim against the canonical sources in my own tree at the
snapshot base (`Semantik.lean`, `Typen.lean`, `ReferenzB.lean`,
`DIRECT-COMPILER-DESIGN.md`, `grammatik/Grammatik/X86/OptFoldConst.lean`).

## 2. Scope hygiene — clean

- The `Grammatik.lean` diff appends `import Grammatik.X86.OptBoundElim` after
  `ComposeImageFetch`, at the end, per rule 5. Nothing else in that file moves.
- No friend-reserved file touched (`X86/OptimizationRules.lean`,
  `X86/OptimizationWitnesses.lean` — a different filename is added).
- No source/checker/Spec/goal/emitter edits, no new diagnostic/gift/example/CLI
  numbers, no MARKE changes. The PATCH file list confirms it.
- Banned tokens: `grep` over the candidate file finds no `sorry`, `admit`,
  `axiom`, `native_decide` or `unsafe` (only benign substrings such as
  "admitted"). Every proof is a real term proof.
- DESIGN §7 row (`DIRECT-COMPILER-DESIGN.md:516`) matches the file header 1:1:
  local premise "source extent proof AT the site (N571/N463/N506 …)",
  certificate "B+C", both failure cases, phase M. The §7 proof requirements
  (pp. 526–538: bind only site-available facts, never derive `ensures`, never
  turn a refusal into a warning) are honoured (§3 below).

## 3. Proof mechanics — verified against canonical definitions

- `OptBoundElim_verbindung` states the rewrite at a `Block.narrow` window with
  arbitrary `sonst`/`rest` and concludes (1) value preservation and (2)
  `execBlock` outcome equality with the unchecked continuation.
- Against `Semantik.lean:852-856`, the narrow arm reads `σ.lese Λ e.orte`,
  evaluates `v`, and on `lo' ≤ v.n ∧ v.n ≤ hi'` continues with
  `execBlock rest σ (.cons ⟨v.n, _, _⟩ ρ)` plus `.schrumpf`, else `sonst`.
  The proof derives exactly that hypothesis `hv` from `hB := hLink hz` plus
  `eval`'s `lo_le`/`le_hi` (i.e. static type containment + type soundness,
  closed by `omega`), then `simp only [execBlock, Zahl.weiter, dif_pos hv]`.
  The remaining goal closes because `Zahl.weiter` (`Typen.lean:135-136`) only
  re-carries range proofs, so both `cons` values agree by proof irrelevance.
  This is the correct use of the semantics, not a restatement of a premise.
- Premise-use audit: `hz` feeds `hLink`; `hB`, `hlo`, `hhi` all feed the
  `omega` that builds `hv`; `sonst`/`rest`/`σ`/`ρ`/`e`/`cert` all occur in the
  concluded equality. No `intro _`, no `have _ :=`, no unused premise.
- No `ensures` is derived anywhere; refusals prove `boundZulassen c = false`
  (fallback keeps the check, never a warning); `sonst` is dead only under the
  admitted `hv`, so no faulting form is speculated above its guard.
- Memory order: both sides perform the single `lese` of `e.orte`; no access is
  added, removed or reordered. Budget: the narrow arm threads but never
  decrements `passes`, so "removed check is pure and unbudgeted" is accurate
  at `execBlock` level. The wider IEEE/contract/call-log/concurrency claims
  rest on outcome equality over the same `rest` with the same environment and
  world — valid, and the report honestly records no formal level-(c)
  machine-work bound (OPEN per lane 278).

## 4. Refusals and probes — both DESIGN failure cases covered

- `boundVerweigert_schreiber`, `boundVerweigert_ruf`, `boundVerweigert_umfang`
  each prove admission `= false` from the corresponding bit, by `simp`.
- Decide-probes exist for admit-all, writer-loop refusal, cross-call refusal,
  and the `7 : 7..7 → 0..10` widening. Negative shape missing only as a
  one-line probe: `⟨false, true, true⟩` (missing extent) has the refusal
  theorem but no `decide` probe. Trivial and optional — not blocking.
- One design observation (not a defect): `keinSchreiber`/`keinRufSchreiber`
  have no recomputed-proof obligation of the `hLink` kind; that is sound here
  because the proved conclusion rests solely on static type containment, which
  no writer or call can invalidate. The bits make admission conservative for
  value-based extents the lemma does not attempt (documented in CUTS: extent
  proof required AT the site). Precision limitation, honestly cut.

## 5. Witness — joint and non-degenerate

`OptBoundElim_verbindung_zeuge` instantiates ALL premises jointly
(`Expr.lit 7 : .int 7 7` vs `0..10`, `leave` else, `nil` rest,
`⟨true,true,true⟩`, recomputed `hLink`, `refSp0.welt []`, `Env.nil`) and proves
both conjuncts via the connection lemma, plus the non-degeneracy conjuncts.
I verified each name in `ReferenzB.lean` at the snapshot base: `refD` has one
table (`Unit`, `typ .int 0 100`); `refEin_schreibt` proves `einzahlen` writes
it; `refB_erreicht` proves `MB` reached from `RufStartF`; `refB_schreibt`
proves slot `0` moved `0 → 100`. The pattern follows the accepted
`OptFoldConst` (lane 860) witness exactly. Rule 13 satisfied.

## 6. Bounded acceptance — hardware byte scope is N/A by construction

The lane-task checklist (byte forms, REX/register/width/flag semantics,
implicit operands, pre-fault effects, TSO/atomicity, feature/MXCSR/interrupt
gates) is vacuous for this candidate: the file contains no decoder, no byte
fetch, no register or flag model — it is a source-level `narrow` rule over
reused canonical vocabulary (`X86.Typen`/`X86.Wort` are imported but unused;
harmless, suggest dropping).
Acceptance therefore grants NO byte correspondence, no silicon claim, no
TSO/GX bridge, no ABI/loader claim — the in-file CUTS already withholds all
of these explicitly, and I hold the author to exactly that boundary.
Undefined hardware state: none introduced; no invented determinism.

Axioms per the candidate's `#print` log: `boundZulassen` none; refusals
`[propext]`; value lemmas `[propext, Quot.sound]`; connection + witness the
standard `[propext, Classical.choice, Quot.sound]`. Within the goal set.

## 7. Build evidence — credible, no rebuild in this lane

`BUILD-EVIDENCE.json` shows genuine queued-wrapper history: three green
`lean-probe` runs, two red runs with real elaboration errors (unknown
`vertrag` identifier, `Ausgang` universe mismatch; then `le_trans` import and
unsolved goals), then green, then axiom prints, then `./lean-bau`
`== exit 0; 0 error line(s)`, 511 jobs, `Built Grammatik`. The red→green
trail reads as real work, not a staged log.
This lane ran no build: it owns no source file and must not materialise the
candidate in-tree, so there is no new `./lean-bau` result line from lane 1018
itself. The merge gate rebuilds anyway. Last relevant measured line (pinned
candidate): `== exit 0; 0 error line(s) in the COMPLETE output … [510/511]
Built Grammatik … Build completed successfully (511 jobs).`

No new definitions/theorems were added by lane 1018 (report-only review).
Candidate theorems reviewed: `boundZulassen`, `boundVerweigert_schreiber`,
`boundVerweigert_ruf`, `boundVerweigert_umfang`, `probe_boundZulassen_ok`,
`probe_boundZulassen_schreiber`, `probe_boundZulassen_ruf`,
`boundWeiter_wert`, `probe_boundWeiter`, `OptBoundElim_verbindung`,
`OptBoundElim_verbindung_zeuge`.

## 8. Open / remains

- Integration of 868 plus the merge-gate rebuild and axiom re-check.
- Per CUTS (accepted as honest): no hoisted entry facts, no overflow-check
  rule, no level-(c) machine-work bound, no silicon/TSO-GX correspondence.
- Optional polish for the author (not conditions): drop the two unused X86
  imports; add the `⟨false, true, true⟩` decide-probe.

## 9. Believed-wrong in the task: nothing blocking

One scope note: the review checklist's byte/hardware items cannot apply to a
source-level optimiser rule; I treated them as N/A-with-evidence (§6) rather
than as a gap. The `hLink`-conditional premise shape follows the accepted
lane-860 precedent and is not an added premise weakening the target — it is
the target's stated certificate shape.
