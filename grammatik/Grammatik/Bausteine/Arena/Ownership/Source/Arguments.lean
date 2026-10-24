import Grammatik.Bausteine.Arena.Ownership.Source.Transfer

namespace Gabbro.Grammatik.ArenaOwnership.Source

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}

/-- Substitute the actual source expression at a typed parameter position.
No numeric argument position or caller-supplied alias summary is trusted. -/
def argument {params : Ctx} (args : Args D Γ Λ params) {τ : Ty}
    (x : Var params τ) : Expr D Γ Λ τ :=
  match args, x with
  | .cons e _, .here => e
  | .cons _ rest, .there x => argument rest x

theorem eval_argument {params : Ctx} (args : Args D Γ Λ params) {τ : Ty}
    (x : Var params τ) (σ0 σ : World D) (ρ : Env D Γ) :
    eval σ0 (argument args x) σ ρ = (evalArgs σ0 args σ ρ).get x := by
  induction x with
  | here => cases args; rfl
  | there x ih => cases args with | cons e rest => exact ih rest

def checkArguments (A : FreiForm D) (c : Context) {params : Ctx} : Args D Γ Λ params → Bool
  | .nil => true
  | .cons e rest => checkExpression A c e && checkArguments A c rest

theorem checkArguments_at (A : FreiForm D) (c : Context) {params : Ctx}
    (args : Args D Γ Λ params) (hc : checkArguments A c args = true)
    {τ : Ty} (x : Var params τ) : checkExpression A c (argument args x) = true := by
  induction x with
  | here => cases args; exact (Bool.and_eq_true_iff.mp hc).1
  | there x ih => cases args with | cons e rest => exact ih rest (Bool.and_eq_true_iff.mp hc).2

end Gabbro.Grammatik.ArenaOwnership.Source
