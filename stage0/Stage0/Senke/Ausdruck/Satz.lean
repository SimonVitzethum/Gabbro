/- The expression theorem specialized to a complete typed world. -/
module
public import Stage0.Senke.Ausdruck.Satz.Scoped
import Grammatik.Kern.Syntax.Satz.T2.Teil1a
@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat} {currentOld : Bool}

/-- The full-world premise supplies each read authorized by the expression. -/
theorem lowE_ok {Λ : List (Res D)} {fp : Runner.W} {K : Nat} {W : Runner.Mem → Prop} (σ₀ σ : World D)
    (hWL : ∀ m, W m → WeltAt m L σ requireWrites) (hLay : LayIn L) {same : currentOld = true → σ₀ = σ}
    {Γ : Ctx} {τ : Ty} (e : Expr D Γ Λ τ) (d : Nat) (c : List II) (top : Nat)
    (lowered : lowE (currentOld := currentOld) L (reserved := reserved) e d = some (c, top))
    (fits : top ≤ K) (m : Runner.Mem) (pc : Runner.W) (ρ : Env D Γ)
    (pre : Pre L m pc fp K d c ρ W reserved) : ValueOk L m pc fp K d c τ (eval σ₀ e σ ρ) :=
  lowE_ok_scoped (same := same) σ₀ σ (fun m stored => (hWL m stored).reads Λ) hLay
    e (fun carrier present => by cases carrier <;> exact e.orte_darf _ present) d c top lowered fits m pc ρ pre

end Gabbro.Stage0.Senke
