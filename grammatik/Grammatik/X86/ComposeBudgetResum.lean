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

/-- Resumption preserves coverage: the summary coverage over `src`
    covers the same segment over any larger `src'`. The ghost keeps
    tracking the OLD budget; the proof replays the accepted expansion
    on both sides. Every premise is used. -/
theorem deckung_resum (s : CostSummary) (m src src' : Nat)
    (xs : List Decodiert)
    (hMax : alleMax s = some m)
    (hDeck : Deckung s src xs)
    (hle : src ≤ src') :
    Deckung s src' xs := by
  intro k' hk'
  have e1 := expandBound_keinVerlust s src m hMax
  have e2 := expandBound_keinVerlust s src' m hMax
  have hwork := hDeck _ e1
  rw [e2] at hk'
  cases hk'
  have hmul : src * m ≤ src' * m := Nat.mul_le_mul_right m hle
  omega

/-- CLOSING: source budget exhaustion meets target work spent, with
    ghost correspondence and resumption. The four conjuncts compose
    accepted modules only: ghost tracking (rewrite of `hGhost`),
    transfer at `src` (`budgetAusfuehrung_transfer`), transfer at the
    resumed `src'` (`deckung_resum` + `budgetAusfuehrung_transfer`),
    and joint stopping order (`stoppReihenfolge`: the over-budget head
    op names the source budget breach AND the refused head form
    refuses the target aggregation). Every premise is used. -/
theorem ComposeBudgetResum_verbindung
    (s : CostSummary) (p : HardwareProfil)
    (xs : List Decodiert) (src src' B t ghost : Nat)
    (bound left : Nat) (op : Op) (rest : List Op)
    (d : Decodiert) (tl : List Decodiert)
    (m : Nat)
    (hGhost : ghost = src)
    (hMax : alleMax s = some m)
    (hDeck : Deckung s src xs)
    (hCost : laufKosten p xs = some t)
    (hb : ∀ d ∈ xs, ∃ c, schrittKosten p d = some c ∧ c ≤ B)
    (hSrcOver : ¬ op.cost ≤ left)
    (hTgtRef : schrittKosten p d = none)
    (hResum : src ≤ src') :
    Deckung s ghost xs ∧
    (∀ k, expandBound s src = some k → t ≤ B * k) ∧
    (∀ k', expandBound s src' = some k' → t ≤ B * k') ∧
    ((∃ needed, runOps bound left (op :: rest)
      = .budget "per_pass.ops" needed bound) ∧
    laufKosten p (d :: tl) = none) := by
  have hGhostDeck : Deckung s ghost xs := by
    rw [hGhost]
    exact hDeck
  have hTransfer := budgetAusfuehrung_transfer s p xs src B t hCost hb hDeck
  have hDeck' := deckung_resum s m src src' xs hMax hDeck hResum
  have hTransfer' :=
    budgetAusfuehrung_transfer s p xs src' B t hCost hb hDeck'
  have hStop := stoppReihenfolge bound left op rest p d tl hSrcOver hTgtRef
  exact ⟨hGhostDeck, hTransfer, hTransfer', hStop⟩

/- CUTS (step 1):
     `GhostBudget` interface plus accepted-expansion monotonicity
     (`expandBound_mono`). Resumption coverage and the main closing
     theorem follow. Exhaustion timing stays OPEN.
-/

#print axioms GhostBudget
#print axioms expandBound_mono
#print axioms deckung_resum
#print axioms ComposeBudgetResum_verbindung

end Gabbro.Grammatik.X86
