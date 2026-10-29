/-
  File:      stage0/Stage0/Senke/Umgebung.lean
  Subject:   The environment in the frame: setting a variable, binding a new one, leaving its scope.
-/
import Stage0.Senke.Ausdruck.Satz
import Stage0.Senke.Ausdruck.Quant.Frame

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration}

theorem get_set_same : {Γ : Ctx} → {τ : Ty} → (ρ : Env D Γ) → (x : Var Γ τ) → (v : Wert D τ) →
    (ρ.set x v).get x = v
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ ρ, .there x, v => get_set_same ρ x v

theorem get_set_ne : {Γ : Ctx} → {τ τ' : Ty} → (ρ : Env D Γ) → (x : Var Γ τ) → (y : Var Γ τ') → (v : Wert D τ) →
    Var.idx y ≠ Var.idx x → (ρ.set x v).get y = ρ.get y
  | _, _, _, .cons _ _, .here, .here, _, h => absurd rfl h
  | _, _, _, .cons _ _, .here, .there _, _, _ => rfl
  | _, _, _, .cons _ _, .there _, .here, _, _ => rfl
  | _, _, _, .cons _ ρ, .there x, .there y, v, h => get_set_ne ρ x y v (by simp [Var.idx] at h; exact h)

/-- Two variables at the same position are the same variable. -/
theorem idx_eq : {Γ : Ctx} → {τ τ' : Ty} → (x : Var Γ τ) → (y : Var Γ τ') → Var.idx y = Var.idx x →
    τ' = τ ∧ HEq y x
  | _, _, _, .here, .here, _ => ⟨rfl, HEq.rfl⟩
  | _, _, _, .here, .there _, h => by simp [Var.idx] at h
  | _, _, _, .there _, .here, h => by simp [Var.idx] at h
  | _, _, _, .there x, .there y, h => by
    obtain ⟨rfl, hh⟩ := idx_eq x y (by simp [Var.idx] at h; exact h)
    exact ⟨rfl, by cases hh; rfl⟩

theorem vslot_ne {Γ : Ctx} {τ τ' : Ty} {x : Var Γ τ} {y : Var Γ τ'} (h : Var.idx y ≠ Var.idx x) :
    vslot y ≠ vslot x := by
  have := idx_lt x; have := idx_lt y
  unfold vslot; omega

/-- Different slots of a frame are apart. -/
theorem slot_far {fp : Runner.W} {K i j : Nat} (hr : fp.toNat + 8 * K ≤ 2 ^ 64) (hi : i < K) (hj : j < K)
    (hne : i ≠ j) : Far (slot fp (BitVec.ofNat 64 i)) 8 (slot fp (BitVec.ofNat 64 j)) 8 := by
  rw [Far, slot_toNat hr hi, slot_toNat hr hj]; omega

theorem envAt_set {m m' : Runner.Mem} {fp : Runner.W} {Γ : Ctx} {ρ : Env D Γ} {τ : Ty} {x : Var Γ τ}
    {v : Wert D τ} {w : Runner.W} (h : EnvAt m fp ρ) (hx : m'.rd64 (slot fp (BitVec.ofNat 64 (vslot x))) = some w)
    (he : Enc τ v w) (hothers : ∀ (τ' : Ty) (y : Var Γ τ'), Var.idx y ≠ Var.idx x →
      m'.rd64 (slot fp (BitVec.ofNat 64 (vslot y))) = m.rd64 (slot fp (BitVec.ofNat 64 (vslot y)))) :
    EnvAt m' fp (ρ.set x v) := by
  intro τ' y
  by_cases hy : Var.idx y = Var.idx x
  · obtain ⟨rfl, hh⟩ := idx_eq x y hy
    cases hh
    exact ⟨w, hx, by rw [get_set_same]; exact he⟩
  · obtain ⟨w', hw', he'⟩ := h τ' y
    exact ⟨w', by rw [hothers τ' y hy]; exact hw', by rw [get_set_ne ρ x y v hy]; exact he'⟩


end Gabbro.Stage0.Senke
