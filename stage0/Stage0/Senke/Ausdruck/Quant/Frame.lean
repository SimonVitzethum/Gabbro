/- Frame facts for expression binders. -/
import Stage0.Senke.Ausdruck.Lesen

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable {D : Deklaration}

theorem idx_lt : {Γ : Ctx} → {τ : Ty} → (x : Var Γ τ) → Var.idx x < Γ.length
  | _, _, .here => by simp [Var.idx]
  | _, _, .there x => by have := idx_lt x; simp [Var.idx]; omega

theorem vslot_here {Γ : Ctx} {τ : Ty} : vslot (Var.here : Var (τ :: Γ) τ) = frei Γ := by
  simp [vslot, frei, Var.idx]

theorem vslot_there {Γ : Ctx} {τ σ : Ty} (y : Var Γ τ) : vslot (Var.there y : Var (σ :: Γ) τ) = vslot y := by
  have := idx_lt y
  simp [vslot, Var.idx]; omega

theorem envAt_cons {m : Runner.Mem} {fp : Runner.W} {Γ : Ctx} {ρ : Env D Γ} {τ : Ty} {v : Wert D τ}
    {w : Runner.W} (h : EnvAt m fp ρ) (hw : m.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some w)
    (he : Enc τ v w) : EnvAt m fp (Env.cons v ρ : Env D (τ :: Γ)) := by
  intro τ' y
  cases y with
  | here => exact ⟨w, by rw [vslot_here]; exact hw, he⟩
  | there y =>
    obtain ⟨w', hw', he'⟩ := h τ' y
    exact ⟨w', by rw [vslot_there]; exact hw', he'⟩

theorem envAt_tail {m : Runner.Mem} {fp : Runner.W} {Γ : Ctx} {τ : Ty} {ρ : Env D (τ :: Γ)} (h : EnvAt m fp ρ) :
    EnvAt m fp ρ.tail := by
  intro τ' y
  obtain ⟨w, hw, he⟩ := h τ' (.there y)
  rw [vslot_there] at hw
  cases ρ with
  | cons _ ρ => exact ⟨w, hw, he⟩

end Gabbro.Stage0.Senke
