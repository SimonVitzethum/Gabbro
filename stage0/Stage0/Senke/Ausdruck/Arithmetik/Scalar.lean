/- Complete canonical value results for scalar integer expression lowering. -/
module
public import Stage0.Senke.Ausdruck.Satz
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- An accepted integer expression certifies its entire shared encoding; the generic
    expression theorem already returns the complete value relation for every width. -/
theorem lowE_int_value_ok {Λ : List (Res D)} {Γ : Ctx} {lo hi : Int}
    {fp pc : Runner.W} {K d top : Nat} {code : List II} {W : Runner.Mem → Prop}
    (σ₀ σ : World D) {same : σ₀ = σ} (world : ∀ m, W m → WeltAt m L σ) (layout : LayIn L)
    (e : Expr D Γ Λ (.int lo hi))
    (_width : integerWords lo hi = 1)
    (lower : lowE L (reserved := reserved) e d = some (code, top)) (fits : top ≤ K)
    (m : Runner.Mem) (ρ : Env D Γ) (pre : Pre L m pc fp K d code ρ W reserved) :
    ValueOk L m pc fp K d code (.int lo hi) (eval σ₀ e σ ρ) :=
  lowE_ok (same := by intro _; exact same) σ₀ σ world layout e d code top lower fits m pc ρ pre

end Gabbro.Stage0.Senke
