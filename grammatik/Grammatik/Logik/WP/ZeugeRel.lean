import Grammatik.Logik.WP.Relational
import Grammatik.Logik.WP.Zeuge

/-!
# GabbroV over machine G: a relational witness

The loop of `Zeuge.lean` (`traverse k over slots of T { T.slots[k].x = 7; }`) run twice from the same world, under
two DIFFERENT oracles, budgets and call meanings: `fuellen_unabhaengig` -- both runs end normally and agree on every
slot. Proved through `traverse2_regel` with the relational invariant "the slots no longer to visit agree".
-/

namespace Gabbro.Grammatik.WP.Zeuge

open Gabbro.Grammatik Gabbro.Grammatik.WP

variable (N : Nat) (O₁ O₂ : Orakel (fD N)) (p₁ p₂ : Nat)
  (R₁ R₂ : ∀ f : (fD N).Fn, World (fD N) → Env (fD N) ((fD N).params f) → RufAusgang f)

/-- The relational invariant: every slot no longer to visit agrees between the two runs. -/
def Inv2 (ks : List (Wert (fD N) (.index ((fD N).count ())))) (σ₁ : World (fD N)) (_ : Env (fD N) [])
    (σ₂ : World (fD N)) (_ : Env (fD N) []) : Prop :=
  ∀ j : Int, (∀ k ∈ ks, k.n ≠ j) → σ₁.slots () j () = σ₂.slots () j ()

/-- The relational postcondition: both end normally and agree on every slot. -/
def Nach2 (o₁ o₂ : Ausgang (fV N) false []) : Prop :=
  ∃ σ₁ σ₂, o₁ = .ok σ₁ .nil ∧ o₂ = .ok σ₂ .nil ∧ ∀ j : Int, 0 ≤ j → j < N → σ₁.slots () j () = σ₂.slots () j ()

/-- **The result does not depend on the oracle, the budget or the call meaning.** -/
theorem fuellen_unabhaengig (σ : World (fD N)) :
    Nach2 N (execStmt O₁ p₁ R₁ (.traverse (V := fV N) (l := false) () .tru (koerper N)) σ .nil)
      (execStmt O₂ p₂ R₂ (.traverse (V := fV N) (l := false) () .tru (koerper N)) σ .nil) := by
  show Nach2 N (traverseLauf (fun σ ρ => execBlock O₁ p₁ R₁ (koerper N) σ ρ) _ (alleIndizes ((fD N).count ())) σ .nil)
    (traverseLauf (fun σ ρ => execBlock O₂ p₂ R₂ (koerper N) σ ρ) _ (alleIndizes ((fD N).count ())) σ .nil)
  refine traverse2_regel _ _ _ _ (Nach2 N) (Inv2 N) ?ende ?inv ?schritt _ σ .nil σ .nil ?start
  case start =>
    intro j _; rfl
  case ende =>
    intro σ₁ ρ₁ σ₂ ρ₂ h
    cases ρ₁; cases ρ₂
    exact ⟨_, _, rfl, rfl, fun j _ _ => h j (fun k hk => by cases hk)⟩
  case inv =>
    intro k ks σ₁ ρ₁ σ₂ ρ₂ _
    exact ⟨by simp only [wahr?, eval], by simp only [wahr?, eval]⟩
  case schritt =>
    intro k ks σ₁ ρ₁ σ₂ ρ₂ h
    cases ρ₁; cases ρ₂
    simp only [TraverseSchritt2, koerper, execBlock, execStmt]
    intro j hnot
    by_cases hj : j = k.n
    · subst hj
      erw [schreibSlot_slots_same, schreibSlot_slots_same]
      rfl
    · erw [schreibSlot_slots_other _ _ _ _ _ _ _ hj, schreibSlot_slots_other _ _ _ _ _ _ _ hj]
      refine h j (fun k' hk' => ?_)
      rcases List.mem_cons.1 hk' with rfl | hk''
      · exact fun he => hj he.symm
      · exact hnot k' hk''

#print axioms fuellen_unabhaengig

end Gabbro.Grammatik.WP.Zeuge
