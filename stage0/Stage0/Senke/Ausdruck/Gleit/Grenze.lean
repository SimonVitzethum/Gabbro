/- Scratch bounds of the float templates, independent of expression induction. -/
import Stage0.Senke.Ausdruck
namespace Gabbro.Stage0.Senke
open Runner.IR

theorem floatKeyL_top {d ta tb top : Nat} {a b c : List II}
    (h : floatKeyL d (some (a, ta)) (some (b, tb)) = some (c, top)) :
    d + 5 ≤ top ∧ ta ≤ top ∧ tb ≤ top := by
  simp only [floatKeyL, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq, bin2] at h
  omega

theorem floatKeyL_room {d top : Nat} {a b : Option (List II × Nat)} {c : List II}
    (h : floatKeyL d a b = some (c, top)) : d + 5 ≤ top := by
  cases a with
  | none => cases h
  | some a => cases b with
    | none => cases h
    | some b => exact (floatKeyL_top h).1

theorem floatCmpL_bounds {le : Bool} {d ta tb top : Nat} {a b c : List II}
    (h : floatCmpL le d (some (a, ta)) (some (b, tb)) = some (c, top)) : ta ≤ top ∧ tb ≤ top := by
  cases le <;> simp only [floatCmpL, bind, Option.bind_some, pure, Bool.false_eq_true,
    ↓reduceIte, Option.some.injEq, Prod.mk.injEq, bin2] at h <;> omega

theorem floatExprL_top {le : Bool} {d top : Nat} {a b : Nat → Option (List II × Nat)} {c : List II}
    (h : floatExprL le d a b = some (c, top)) : d < top := by
  simp only [floatExprL, floatCmpL, floatKeyL, bind, Option.bind_eq_some_iff, pure] at h
  obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, hc⟩ := h
  obtain ⟨⟨aa, na⟩, _, ⟨ab, bt⟩, _, ha⟩ := ha
  obtain ⟨⟨ba, ct⟩, _, ⟨bb, dt⟩, _, hb⟩ := hb
  cases le <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, bin2] at ha hb hc <;> omega

end Gabbro.Stage0.Senke
