# MUSE-REPORT-785: Hardware completion — CAS divergence record

## Task
Lane 785: define the per-program DIVERGENCE record for unbounded CAS loops
vs one source step; cost-bound claims without it are refused.
ZEUGE: `CasDivergenceRec_verbindung` + companion
`CasDivergenceRec_verbindung_zeuge` (jointly inhabited, non-degenerate,
memory-changing reached run).

## What was done
New file `grammatik/Grammatik/X86/CasDivergenceRec.lean` (registered in
`grammatik/Grammatik.lean`), reusing canonical vocabulary only:
`LockedOps.casKosten` / `cas_schleife_unbeschraenkt` / `lockSchritt` /
`locked_add_zwei_kerne` / `lockAddr`, the `CostSummary` schema
(`kostenSummeOk`, `expandBound`, `alleMax`, `blattSummary`,
`kostenSummeOk_verweigert_unbegrenzt`, `expandBound_keinVerlust`),
and the source fixture `ZielOrtEinfadenZeuge`
(`eD/eP/eO/eSp/eInit/eSetze/ePruefe`, `ziel_ort_einfaden_zeuge`).
No new decoder, evaluator, encoding, fault class or timing claim.

Definitions:
- `CasDivergenzRec` — per-program record: `versuche` (this program's
  CAS-loop attempt count for one source step) and `schranke`
  (`none` = honestly unbounded).
- `divergenzBetrag` — one source step costs `casKosten versuche`
  (the one cost model, reused).
- `divergenzZulaessig` — transfer admission Bool: record bound covers
  attempts AND summary retry bound covers the record bound; else false.

Theorems:
- `CasDivergenceRec_verbindung` (TARGET): with record bound `K`
  covering attempts, summary retry bound `B` covering `K`, uniform
  maximum `m` covering `B+1`, and `expandBound s 1 = some k`, concludes
  `divergenzZulaessig s r = true ∧ divergenzBetrag r ≤ k`.
  Every premise is used; the bound is derived arithmetically, not assumed.
- `ohneDivergenz_keinKostenAnspruch`: unbounded record + summary with
  `retryBound = none` pricing `retryTry` refuses both
  `kostenSummeOk` and `divergenzZulaessig` (via the accepted
  `kostenSummeOk_verweigert_unbegrenzt`).
- `CasDivergenceRec_verbindung_zeuge`: joint witness — reached `eP` run
  (table `konto` written, slot 0→5) + reached two-core locked-add run
  (word observably changed) + covered record `⟨2, some 3⟩` against
  `blattSummary` (admission true, amount 2+1 ≤ 5).

Read (not duplicated): Typen, Wort, Speicher, Ausfuehrung, Codec, TSO,
NarrowOps, MulDiv, ShiftLogic, ControlFlow, LockedOps, ScalarFloat,
Ganzzahl, Gleitprofil, Vektor, Relokation, DecodeFault, HardwareFaults,
ExtendedExecution, LockedInstructionExecution, BudgetExecution,
CostSummary, HardwareAssumptions, TimeTransfer. Fetched-byte execution
stays with the ExtendedExecution/LockedInstructionExecution owners;
fault classes stay with HardwareFaults; per-form timing stays with
HardwareAssumptions — stated in CUTS.

## Verification
- `./lean-probe grammatik/Grammatik/X86/CasDivergenceRec.lean`:
  `== 0 error(s)`, axioms `[propext, Quot.sound]` /
  `[propext]` / `[propext, Classical.choice, Quot.sound]` — within the
  standard `gabbro_ziel` set, no new axiom.
- `./lean-bau`: `Build completed successfully (485 jobs)`,
  `== exit 0; 0 error line(s)`. Whole project green.

## What remains open (see file CUTS)
Which source step lowers to which CAS loop (lowering/IR producer;
no `IR.lean` exists); no progress/fairness/retry-success promise
(a covered bound counts attempts, never promises one succeeds);
no silicon correspondence; no new byte/fault/timing claims.

## Task assessment
Nothing in the task was found wrong. The INHABITATION bar is met:
the witness carries a table-writing program and two memory-changing
reached runs (source slot 0→5, target word changed across two cores).
No diagnostic/gift/example/CLI numbers taken, no MARKE_EMIT changes,
no source/checker/Spec/goal/emitter or friend-reserved files touched.
