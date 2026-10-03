# MUSE-REPORT-874: Bounded unroll rule (lane 874)

## What was done

New file `grammatik/Grammatik/X86/OptUnrollBound.lean` (namespace
`Gabbro.Grammatik.X86`, `open Gabbro.Grammatik`), registered in
`grammatik/Grammatik.lean` as `import Grammatik.X86.OptUnrollBound`.
It proves the DESIGN section 7 "Loop unroll (bounded)" row as a generic
rule lemma over arbitrary token values: a trip of `n` iterations with
per-iteration token list `b` rewrites to full groups of `k` plus a
remainder of `r`, duplicating (never fusing) the token ops.

Read before writing: `DIRECT-COMPILER-DESIGN.md` §7 row (premises,
certificate "B", failure case), sibling rule `X86/OptFoldConst.lean`
(structure/proof/witness pattern), `X86/CostSummary.lean`
(`targetWork_add` reuse), `Typen`/`Semantik` (`bruch`, `gleitPasst`),
`ReferenzB.lean` (witness fixtures). No accepted IR exists (IR287 draft
uncommitted), so the rule is proved over the per-iteration token
fragment, stated honestly in CUTS. No diagnostic/gift/example/CLI
numbers, no MARKE_EMIT changes, no source/checker/Spec/goal/emitter
edits, no friend-reserved optimiser files touched.

## Exact new definitions

- `UnrollCert` (structure: `k`, `tripBekannt`, `restPfad`, `keineFusion`)
- `unrollZulassen` (admission Bool, includes `decide (0 < c.k)`)
- `koerperSpur` (loop trace: `b` duplicated `n` times)
- `entrollt` (unrolled shape: full groups `q * k` plus remainder `r`)
- `entrolltOpt` (admitted rewrite: `some` trace iff admitted, else `none`)
- `UnrollNachweis` (exact certificate: `regel` + `blockAbbild` + `analyseNeu`)
- `nachweisOk` (certificate admission Bool)

## Exact new theorems

Refusal: `unrollVerweigert_fusion` (DESIGN failure case), 
`unrollVerweigert_trip`, `unrollVerweigert_rest`, `unrollVerweigert_kNull`,
probes `probe_unrollZulassen_ok`, `probe_unrollZulassen_fusion`.
Core: `koerperSpur_append`, `spur_gleich`, `entrolltOpt_gilt`,
`entrolltOpt_verweigert`, probe `probe_koerperSpur`.
Certificate: `nachweisOk_regel`, probes `probe_nachweisOk`,
`probe_nachweisOk_analyse`.
Preservation: `unrollBeob_gleich` (generic observation: values, faults,
log order), `unrollGleit_behält` (IEEE: kernel `bruch` + `gleitPasst`
per token), `koerperSpur_länge`, `unrollBudget_gleich`,
`unrollKosten_gleich` (budget), `koerperSpur_mem`, `unrollKeineNeuen`
(concurrency: no added/merged token), `unrollArbeit_additiv` (machine
work via reused `targetWork_add`).
Connection: `OptUnrollBound_verbindung` (4-way conjunction) with joint
companion `OptUnrollBound_verbindung_zeuge` (factor 2, `q = 3`, `r = 1`,
`n = 7`, on `refD` with `refEin_schreibt`, `refB_erreicht`,
`refB_schreibt`).

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (511 jobs)`.
`./lean-probe grammatik/Grammatik/X86/OptUnrollBound.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`, no warnings.
Axioms: at most `[propext, Classical.choice, Quot.sound]` (witness only,
via referenced fixtures); all else `[propext, Quot.sound]` or fewer.
No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

## What remains open (see CUTS in the file)

No source-syntax loop rewrite (no `Syntax` loop form, no `execStmt`
correspondence); no budget-simulation claim; no silicon/TSO-GX/ABI
correspondence; remainder bound `r < k` left to validator + block map;
no checker change. The `while`/`traverse` lowering with trip evidence
belongs to the lowering lane.

## Task remarks

Nothing in the task is wrong. One scoping note: "prove ...
preservation including IEEE, contracts, call logs, concurrency and
budget" is discharged at the token-list level (any per-token
observation function is preserved by list equality; IEEE concretely via
`bruch`/`gleitPasst`; contracts/logs/concurrency/budget as documented
corollaries) — full `execEnd`/duty-level preservation needs the
lowering lane's token-list production, which does not exist yet.
