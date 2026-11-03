/- Packed and span string operations meet in the actual expression theorem. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.CatOk
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.OrderOk
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat} {currentOld : Bool}
variable {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ} {W : Runner.Mem → Prop}
variable {σ₀ σ : World D} {fp : Runner.W} {K d top : Nat} {c : List II} {m : Runner.Mem} {pc : Runner.W}

theorem strCatExpr_ok {n q : Nat} (s : Expr D Γ Λ (.str n)) (t : Expr D Γ Λ (.str q))
    (ihs : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) s d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) (eval σ₀ s σ ρ))
    (iht : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) t d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str q) (eval σ₀ t σ ρ))
    (ihsa : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) s (d + (n + q + 1)) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + (n + q + 1)) ca ρ W reserved →
        ValueOk L m pc fp K (d + (n + q + 1)) ca (.str n) (eval σ₀ s σ ρ))
    (ihtb : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) t
        (d + (n + q + 1) + (stringCapacity n + 1)) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + (n + q + 1) + (stringCapacity n + 1)) ca ρ W reserved →
        ValueOk L m pc fp K (d + (n + q + 1) + (stringCapacity n + 1)) ca (.str q) (eval σ₀ t σ ρ))
    (h : lowE (currentOld := currentOld) L (reserved := reserved) (.strCat s t) d = some (c, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.str (n + q)) (eval σ₀ (.strCat s t) σ ρ) := by
  rw [lowE_strCat] at h
  split at h
  · next short => exact strCat_ok s t ihs iht (by rw [if_pos short]; exact h) fits pre
  · unfold strCatSpanL at h
    split at h
    · next bounds =>
      let a := d + (n + q + 1)
      let b := a + (stringCapacity n + 1)
      let ptr := b + (stringCapacity q + 1)
      let need := max (ptr + 2) (constWords (List.replicate q 0) (d + 1 + n)).2
      refine stringPair_ok (eval σ₀ s σ ρ) (eval σ₀ t σ ρ)
        (fun m' => ValueAt L m' fp d (.str (n + q)) (eval σ₀ (.strCat s t) σ ρ))
        (by omega : d ≤ a) rfl (by dsimp [need, ptr]; omega) ihsa ihtb h fits pre ?_
      intro m pc hp needFits spanA spanB
      exact stringCatC_ok (eval σ₀ s σ ρ) (eval σ₀ t σ ρ) bounds.1 rfl rfl rfl
        (Nat.le_refl need) needFits spanA spanB hp
    · cases h

theorem strLtExpr_ok {n q : Nat} (s : Expr D Γ Λ (.str n)) (t : Expr D Γ Λ (.str q))
    (ihs : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) s d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) (eval σ₀ s σ ρ))
    (iht : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) t (d + 1) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) ca ρ W reserved → ValueOk L m pc fp K (d + 1) ca (.str q) (eval σ₀ t σ ρ))
    (ihsa : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) s (d + 1) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) ca ρ W reserved → ValueOk L m pc fp K (d + 1) ca (.str n) (eval σ₀ s σ ρ))
    (ihtb : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) t
        (d + 1 + (stringCapacity n + 1)) = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1 + (stringCapacity n + 1)) ca ρ W reserved →
        ValueOk L m pc fp K (d + 1 + (stringCapacity n + 1)) ca (.str q) (eval σ₀ t σ ρ))
    (h : lowE (currentOld := currentOld) L (reserved := reserved) (.strLt s t) d = some (c, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c .bool (eval σ₀ (.strLt s t) σ ρ) := by
  rw [lowE_strLt] at h
  split at h
  · next short => exact strCompare_ok true s t ihs iht (by rw [if_pos short]; exact h) fits pre
  · exact strLtSpan_ok (eval σ₀ s σ ρ) (eval σ₀ t σ ρ) _ _ ihsa ihtb h fits pre

end Gabbro.Stage0.Senke
