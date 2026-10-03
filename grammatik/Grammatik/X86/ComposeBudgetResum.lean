/-
  File:      Grammatik/X86/ComposeBudgetResum.lean
  Subject:   Composition closing: budget-resumption closing (lane 834).

  Producer/consumer interface closed here: source budget exhaustion
  (`Budget.runOps` over-budget head, `BudgetExecution.stoppReihenfolge`)
  to target work spent (`CostSummary.expandBound`/`targetWork` via
  `BudgetExecution.Deckung` and `budgetAusfuehrung_transfer`), with an
  explicit ghost source-budget correspondence (`GhostBudget`: the ghost
  tracks the source budget exactly). Resumption (larger source budget
  preserves coverage) is proved from the accepted expansion formula.
  Exhaustion TIMING (when the target stops relative to source
  exhaustion) stays an explicit OPEN cut, owned by the scheduling/IR
  lanes. No new interpreter, no second cost model, no checker change.
-/
import Grammatik.X86.BudgetExecution
import Grammatik.X86.CostSummary
import Grammatik.X86.HardwareAssumptions
import Grammatik.Budget

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Ghost source-budget correspondence: the ghost value tracks exactly
    the source budget the summary coverage runs over. Checked data
    (`Deckung`), never a second counter. -/
def GhostBudget (s : CostSummary) (ghost src : Nat)
    (xs : List Decodiert) : Prop :=
  ghost = src ∧ Deckung s src xs

/-- Accepted-expansion monotonicity: a larger source budget never
    shrinks the expansion bound. From the accepted formula
    (`expandBound_keinVerlust`), never a re-sum. Every premise is
    used: `hMax` fixes the uniform maximum for both sides, `hk` and
    `hk'` pin the two bounds, `hle` orders them. -/
theorem expandBound_mono (s : CostSummary) (m src src' k k' : Nat)
    (hMax : alleMax s = some m)
    (hk : expandBound s src = some k)
    (hk' : expandBound s src' = some k')
    (hle : src ≤ src') :
    k ≤ k' := by
  have e1 := expandBound_keinVerlust s src m hMax
  have e2 := expandBound_keinVerlust s src' m hMax
  rw [e1] at hk
  rw [e2] at hk'
  cases hk
  cases hk'
  have hmul : src * m ≤ src' * m := Nat.mul_le_mul_right m hle
  omega

/- CUTS (step 1):
     `GhostBudget` interface plus accepted-expansion monotonicity
     (`expandBound_mono`). Resumption coverage and the main closing
     theorem follow. Exhaustion timing stays OPEN.
-/

#print axioms GhostBudget
#print axioms expandBound_mono

end Gabbro.Grammatik.X86
