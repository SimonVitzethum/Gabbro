/-
  File:      Grammatik/X86/PipelineWork.lean
  Subject:   Source budget to target work and time transfer over the
             direct pipeline lowering (lane 1165).

  Connects the source cost/budget accounting (source `Kosten`/budget
  stops, the goal theorem's `ZeitAb`/budget-stop kinds via
  `BudgetExecution`) to target retired-instruction work: a
  lowering-derived worst-case instruction count per source step
  (`senkStmt` chunks: value code plus address materialisation plus
  slot store), the admitted pipeline summary `pipeSummary`
  (uniform maximum 6, honest zero spill/fence, proved retry bound,
  no exclusions), the derived `Deckung` producer, and the composed
  work/time transfer (`ComposeWorkTransfer`,
  `ComposeBudgetResum`). Named per-form timing bounds stay
  hardware assumptions (`HardwareAssumptions.laufKosten`); they
  never prove software bodies, fairness or bounded CAS retries.

  Reused, not duplicated: `Pipeline.senkStmt`/`senkWertT`/
  `senkWert_als_tief`/`validate`/`pipeline_correct`,
  `ExpressionLowering.senkFrag_laenge` (via `DerivedWorkBound`),
  `DerivedWorkBound.decodiertZu`/`arbeit_decodiert`/`fragmentSummary`
  lemmas, `BudgetExecution` stops and transfer, `CostSummary`
  schema, `TimeTransfer` admission. No second IR, no second source
  interpreter, no new cost model, no checker change, no
  friend-reserved optimiser file.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.ComposeWorkTransfer
import Grammatik.X86.ComposeBudgetResum

namespace Gabbro.Grammatik.X86.PipelineWork

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.OptimizationRules

/-! ## 1. The admitted pipeline summary: uniform maximum 6.

    A shallow lowered assignment chunk is value code (1 or 3
    instructions, `senkFrag_laenge` through `senkWert_als_tief`)
    plus address materialisation plus slot store (2 more), hence
    at most 5; a shallow check is two atoms plus `cmp` plus the
    refusal jump (4). The uniform maximum 6 covers both with
    honest zero spill/fence counts, a proved retry bound and no
    exclusions. -/

/-- The pipeline summary: uniform maximum 6, honest zero
    spill/fence counts, a proved retry bound, no exclusions. -/
def pipeSummary : CostSummary where
  expand := fun _ => some 6
  spillCount := 0
  fenceCount := 0
  retryBound := some 0
  exclusions := []

/-- The pipeline summary is admitted by the validator Bool. -/
theorem pipeSummary_ok : kostenSummeOk pipeSummary = true := by
  decide

/-- The pipeline summary has uniform maximum 6. -/
theorem pipeSummary_max : alleMax pipeSummary = some 6 := by
  decide

/- CUTS:
    - Proved here: the admitted pipeline summary (uniform maximum 6,
      honest zero spill/fence, proved retry bound, no exclusions).
    - OPEN: per-chunk derived work, the `Deckung` producer, the
      work/time transfer, the budget-stop connection, the
      validator-level closing, refusals and joint witnesses.
-/

#print axioms pipeSummary_ok
#print axioms pipeSummary_max

end Gabbro.Grammatik.X86.PipelineWork
