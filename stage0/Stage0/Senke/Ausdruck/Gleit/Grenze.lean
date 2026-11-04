/- Native float comparisons reserve both actually read operand slots. -/
module
public import Stage0.Senke.Gleit.Native.Code
@[expose] public section

namespace Gabbro.Stage0.Senke
open Runner.IR

theorem nativeFPWordL_bounds {kind : Runner.NativeFPOp} {d top : Nat}
    {a b : Option (List II × Nat)} {c : List II}
    (h : nativeFPWordL kind d a b = some (c, top)) : d + 2 ≤ top := by
  simp only [nativeFPWordL, wordL, bind, Option.bind_eq_some_iff,
    pure, Option.some.injEq] at h
  obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, hc⟩ := h
  have ceiling := congrArg Prod.snd hc
  dsimp only at ceiling
  omega

theorem floatExprL_top {le : Bool} {d top : Nat}
    {a b : Nat → Option (List II × Nat)} {c : List II}
    (h : floatExprL le d a b = some (c, top)) : d < top := by
  cases le <;> simp only [floatExprL, Bool.false_eq_true, ↓reduceIte] at h
  all_goals have := nativeFPWordL_bounds h; omega

end Gabbro.Stage0.Senke
