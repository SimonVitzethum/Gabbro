/- The start environment of `main`: every parameter is the one pointer to the table its type names (G's value `()`,
   encoded as the zero word). A parameter of another type has no start-argument form in the source and is refused. -/
import Stage0.Senke.Ausdruck.Aggregat.Encoding

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik

/-- The environment `main` starts with, or none when a parameter is not a table pointer. -/
def mainEnv {D : Deklaration} : (Γ : Ctx) → Option (Env D Γ)
  | [] => some .nil
  | .ptr t rw :: Γ => (mainEnv Γ).map fun ρ => Env.cons (τ := .ptr t rw) () ρ
  | _ :: _ => none

/-- Pointer values are not representation-constrained: the environment is valid under every layout. -/
theorem mainEnv_valid {D : Deklaration} (L : Lay D) (Γ : Ctx) :
    ∀ (ρ : Env D Γ), mainEnv Γ = some ρ → ∀ τ (x : Var Γ τ), ValueValid L τ (ρ.get x) := by
  induction Γ with
  | nil => intro ρ _ τ x; nomatch x
  | cons σ Γ ih =>
    intro ρ h τ x
    cases σ with
    | ptr t rw =>
      simp only [mainEnv, Option.map_eq_some_iff] at h
      obtain ⟨ρ', hρ', rfl⟩ := h
      cases x with
      | here => trivial
      | there x => exact ih ρ' hρ' τ x
    | _ => all_goals (exfalso; simp [mainEnv] at h)

end Gabbro.Stage0.Senke
