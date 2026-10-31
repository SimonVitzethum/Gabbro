/- Complete canonical value results for scalar integer expression lowering. -/
import Stage0.Senke.Ausdruck.Satz

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- A one-word integer result certifies its entire shared encoding. The width
    premise excludes every genuinely multiword type, including mixed intervals. -/
theorem lowE_int_value_ok {Λ : List (Res D)} {Γ : Ctx} {lo hi : Int}
    {fp pc : Runner.W} {K d top : Nat} {code : List II} {W : Runner.Mem → Prop}
    (σ₀ σ : World D) (world : ∀ m, W m → WeltAt m L σ)
    (e : Expr D Γ Λ (.int lo hi))
    (width : integerWords lo hi = 1)
    (lower : lowE L (reserved := reserved) e d = some (code, top)) (fits : top ≤ K)
    (m : Runner.Mem) (ρ : Env D Γ) (pre : Pre L m pc fp K d code ρ W reserved) :
    ValueOk L m pc fp K d code (.int lo hi) (eval σ₀ e σ ρ) := by
  obtain ⟨m', steps, frame, word, read, value⟩ := lowE_ok σ₀ σ world e d code top lower fits m pc ρ pre
  refine ⟨m', steps, frame, trivial, ?_⟩
  change WordsAt m' fp d (integerEncoding (integerWords lo hi) (eval σ₀ e σ ρ).n)
  rw [width]
  intro i bound
  have zero : i = 0 := by
    simp only [integerEncoding, List.length_cons, List.length_nil] at bound
    omega
  subst i
  simp only [integerEncoding, List.getElem_cons_zero, Nat.add_zero]
  simp only [Enc] at value
  simpa only [value] using read

end Gabbro.Stage0.Senke
