module
public import Stage0.Senke.Ausdruck.Tops.TopAusdruck
@[expose] public section

variable {currentOld : Bool}


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}
theorem Ok.mono {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {c : List II} {P Q : Runner.W → Prop}
    (h : Ok m pc fp K d c P) (hq : ∀ w, P w → Q w) : Ok m pc fp K d c Q := by
  obtain ⟨m', s, a, w, r, p⟩ := h
  exact ⟨m', s, a, w, r, hq w p⟩

/-- Destructure the code of a binary operation. -/
theorem bin_some {reserved : Nat} {Λ : List (Res D)} {Γ : Ctx} {τa τb : Ty} {a : Expr D Γ Λ τa} {b : Expr D Γ Λ τb} {o d : Nat}
    {c : List II} {top : Nat}
    (h : (do let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a d; let cb ← lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1); pure (bin2 o d ca cb)) = some (c, top)) :
    ∃ ca ta cb tb, lowE (currentOld := currentOld) L (reserved := reserved) a d = some (ca, ta) ∧ lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1) = some (cb, tb) ∧
      c = ca ++ cb ++ [ci o d d (d + 1)] ∧ top = max ta tb := by
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
  simp only [bin2, pure, Option.some.injEq, Prod.mk.injEq] at he
  exact ⟨ca, ta, cb, tb, ha, hb, he.1.symm, he.2.symm⟩


/-- A binary operation whose operands the lowering accepts: `a` into `d`, `b` into `d+1`, the instruction `o`. -/
theorem binE_ok {reserved : Nat} {Λ : List (Res D)} {Γ : Ctx} {τa τb : Ty} {a : Expr D Γ Λ τa} {b : Expr D Γ Λ τb} {o d : Nat}
    {c : List II} {top K : Nat} {fp : Runner.W} {W : Runner.Mem → Prop} {ρ : Env D Γ} {m : Runner.Mem}
    {pc : Runner.W} {Pa Pb P : Runner.W → Prop} {g : Runner.W → Runner.W → Option Runner.W}
    (h : (do let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a d; let cb ← lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1); pure (bin2 o d ca cb)) = some (c, top))
    (hK : top ≤ K)
    (iha : ∀ ca ta, lowE (currentOld := currentOld) L (reserved := reserved) a d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca Pa)
    (ihb : ∀ cb tb, lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1) = some (cb, tb) → tb ≤ K → ∀ m pc, Pre L m pc fp K (d + 1) cb ρ W reserved →
      Ok m pc fp K (d + 1) cb Pb)
    (hg : ∀ wa wb, Pa wa → Pb wb → ∃ r, g wa wb = some r ∧ P r) (hop : op o = bin g) (ho : o < 256)
    (hp : Pre L m pc fp K d c ρ W reserved) : Ok m pc fp K d c P := by
  obtain ⟨ca, ta, cb, tb, ha, hb, rfl, rfl⟩ := bin_some h
  have := lowE_top b (d + 1) cb tb hb
  exact bin_ok (iha ca ta ha (by omega)) (ihb cb tb hb (by omega)) hg hop ho (by omega) hp

end Gabbro.Stage0.Senke

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
/-- A real variable read and temporary computation with a nonzero reservation. -/
theorem lowE_reserved_top_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    ∃ c top, lowE (currentOld := currentOld) L (reserved := 3)
      (.and (.var .here) .tru : Expr D [.bool] [] .bool) 10 = some (c, top) ∧ 10 < top := by
  refine ⟨_, _, rfl, ?_⟩
  decide
end Gabbro.Stage0.Senke
