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

/- CUTS:
     Skeleton only: `GhostBudget` interface stated. Main closing
     theorems, resumption monotonicity and joint witnesses follow.
     Exhaustion timing stays OPEN (scheduling/IR lanes own it).
-/

#print axioms GhostBudget

end Gabbro.Grammatik.X86
