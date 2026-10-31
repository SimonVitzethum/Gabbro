/- Subject: Empty and singleton arrays reuse the element word, including nested singleton arrays.
   Larger arrays are refused: frame slots and the generic call ABI remain one word per value.
   G expressions are pure, so an empty tail and the unique well-typed index need no code. -/
import Stage0.Senke.Ausdruck.Lesen

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {Λ : List (Res D)} {Γ : Ctx} {τ : Ty}
variable {σ₀ σ : World D} {fp : Runner.W} {K d top reserved : Nat} {W : Runner.Mem → Prop}
variable {ρ : Env D Γ} {c : List II} {m : Runner.Mem} {pc : Runner.W}

theorem singleton_index (i : Zahl 0 ((1 : Int) - 1)) : i.fin (n := 1) = ⟨0, by decide⟩ := by
  apply Fin.ext
  have := i.lo_le
  have := i.le_hi
  simp only [Zahl.fin]
  omega

theorem arrNil_ok (h : lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.arrNil (τ := τ)) d = some (c, top))
    (hK : top ≤ K) (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (Enc L (.arr τ 0) (eval σ₀ (Expr.arrNil (Λ := Λ)) σ ρ)) := by
  simp only [lowE_eqs, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact (const_ok hp (by decide) (by omega)).mono fun w hw => by simpa [Enc] using hw

theorem arrCons_ok {n : Nat} (a : Expr D Γ Λ τ) (rest : Expr D Γ Λ (.arr τ n))
    (ih : ∀ ca ta, lowE L (reserved := reserved) a d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca (Enc L τ (eval σ₀ a σ ρ)))
    (h : lowE L (reserved := reserved) (.arrCons a rest) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (Enc L (.arr τ (n + 1)) (eval σ₀ (.arrCons a rest) σ ρ)) := by
  simp only [lowE_eqs] at h
  split at h
  · next hn =>
    subst n
    exact (ih c top h hK m pc hp).mono fun w hw => by
      change Enc L τ (eval σ₀ a σ ρ) w
      exact hw
  · cases h

theorem arrGet_ok {n : Nat} (a : Expr D Γ Λ (.arr τ n)) (i : Expr D Γ Λ (.index n))
    (ih : ∀ ca ta, lowE L (reserved := reserved) a d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca (Enc L (.arr τ n) (eval σ₀ a σ ρ)))
    (h : lowE L (reserved := reserved) (.arrGet a i) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (Enc L τ (eval σ₀ (.arrGet a i) σ ρ)) := by
  simp only [lowE_eqs] at h
  split at h
  · next hn =>
    subst n
    exact (ih c top h hK m pc hp).mono fun w hw => by
      change Enc L τ ((eval σ₀ a σ ρ) (eval σ₀ i σ ρ).fin) w
      rw [show (eval σ₀ i σ ρ).fin = (⟨0, by decide⟩ : Fin 1) from Subsingleton.elim _ _]
      exact hw
  · cases h

theorem arrSet_ok {n : Nat} (a : Expr D Γ Λ (.arr τ n)) (i : Expr D Γ Λ (.index n)) (v : Expr D Γ Λ τ)
    (ih : ∀ ca ta, lowE L (reserved := reserved) v d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca (Enc L τ (eval σ₀ v σ ρ)))
    (h : lowE L (reserved := reserved) (.arrSet a i v) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (Enc L (.arr τ n) (eval σ₀ (.arrSet a i v) σ ρ)) := by
  simp only [lowE_eqs] at h
  split at h
  · next hn =>
    subst n
    exact (ih c top h hK m pc hp).mono fun w hw => by
      change Enc L τ (arrSetW (eval σ₀ a σ ρ) (eval σ₀ i σ ρ).fin (eval σ₀ v σ ρ) ⟨0, by decide⟩) w
      rw [show (eval σ₀ i σ ρ).fin = (⟨0, by decide⟩ : Fin 1) from Subsingleton.elim _ _]
      simpa only [arrSetW, ↓reduceIte] using hw
  · cases h
end Gabbro.Stage0.Senke
