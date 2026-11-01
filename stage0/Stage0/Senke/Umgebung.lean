/-
  File:      stage0/Stage0/Senke/Umgebung.lean
  Subject:   The environment in the frame: setting a variable, binding a new one, leaving its scope.
-/
module
public import Stage0.Senke.Ausdruck.Satz
public import Stage0.Senke.Ausdruck.Quant.Frame
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration} {L : Lay D}
variable {reserved : Nat}

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
    vslot y reserved ≠ vslot x reserved := by
  suffices variableOffset y ≠ variableOffset x by unfold vslot; omega
  induction x generalizing τ' with
  | here =>
    cases y with
    | here => exact False.elim (h rfl)
    | there y =>
      have := variableOffset_bound y
      have := valueWords_pos τ'
      simp only [variableOffset]; omega
  | @there Γ₁ τ₁ σ₁ x ih =>
    cases y with
    | here =>
      have hb := variableOffset_bound x
      have pos := valueWords_pos τ₁
      simp only [variableOffset]
      omega
    | there y => exact ih (by intro heq; apply h; simpa only [Var.idx, heq])


/-- Updating a variable preserves complete values of all other variables, rather
    than only their first words. The writer supplies the new canonical span. -/
theorem envAt_set {m m' : Runner.Mem} {fp : Runner.W} {Γ : Ctx} {ρ : Env D Γ} {τ : Ty} {x : Var Γ τ}
    {v : Wert D τ} (h : EnvAt L m fp ρ reserved)
    (hx : ValueAt L m' fp (vslot x reserved) τ v)
    (hothers : ∀ (τ' : Ty) (y : Var Γ τ'), Var.idx y ≠ Var.idx x →
      ∀ i, i < valueWords τ' →
      m'.rd64 (slot fp (BitVec.ofNat 64 (vslot y reserved + i))) =
        m.rd64 (slot fp (BitVec.ofNat 64 (vslot y reserved + i)))) :
    EnvAt L m' fp (ρ.set x v) reserved := by
  intro τ' y
  by_cases hy : Var.idx y = Var.idx x
  · obtain ⟨rfl, hh⟩ := idx_eq x y hy
    cases hh
    rw [get_set_same]
    exact hx
  · rw [get_set_ne ρ x y v hy]
    obtain ⟨valid, words⟩ := h τ' y
    refine ⟨valid, ?_⟩
    intro i hi
    rw [hothers τ' y hy i (by simpa only [encodeWords_length] using hi)]
    exact words i hi


end Gabbro.Stage0.Senke
