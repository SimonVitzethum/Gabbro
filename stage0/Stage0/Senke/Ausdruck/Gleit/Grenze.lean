/- Scratch bounds of the float templates, independent of expression induction. -/
import Stage0.Senke.Ausdruck
namespace Gabbro.Stage0.Senke
open Runner.IR

theorem floatExprL_top {le : Bool} {d top : Nat} {a b : Nat → Option (List II × Nat)} {c : List II}
    (h : floatExprL le d a b = some (c, top)) : d < top := by
  simp only [floatExprL, floatCmpL, floatKeyL, bind, Option.bind_eq_some_iff, pure] at h
  obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, hc⟩ := h
  obtain ⟨⟨aa, na⟩, _, ⟨ab, bt⟩, _, ha⟩ := ha
  obtain ⟨⟨ba, ct⟩, _, ⟨bb, dt⟩, _, hb⟩ := hb
  cases le <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, bin2] at ha hb hc <;> omega

end Gabbro.Stage0.Senke
