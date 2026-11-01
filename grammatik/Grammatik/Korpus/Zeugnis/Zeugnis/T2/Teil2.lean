module

public import Grammatik.Korpus.Zeugnis.Zeugnis.T1
public import Grammatik.Korpus.Zeugnis.Zeugnis.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- `6 band 3` printed as `(0, 6)`: both operands nonneg (M137). -/
example : GueltigAbleitung TestD [] [] (.band (.lit 6) (.lit 3)) 0 6 := by decide

/-- FORGED proof: a negative operand under `band` -- no range at all. -/
example : ¬ GueltigAbleitung TestD [] [] (.band (.sub (.lit 0) (.lit 1)) (.lit 3)) 0 0 := by decide

/-- `6 bor 3` in width 3 printed as `(0, 7)`: both bounds fit under `2 ^ 3`. -/
example : GueltigAbleitung TestD [] [] (.bor 3 (.lit 6) (.lit 3)) 0 7 := by decide

/-- FORGED proof: width 2 does not hold `6` -- the width side condition fails. -/
example : ¬ GueltigAbleitung TestD [] [] (.bor 2 (.lit 6) (.lit 3)) 0 3 := by decide

/-- `6 bxor 3` in width 3 printed as `(0, 7)`: same width rule as `bor`. -/
example : GueltigAbleitung TestD [] [] (.bxor 3 (.lit 6) (.lit 3)) 0 7 := by decide

/-- FORGED proof: width 2 does not hold `6` under `bxor` either. -/
example : ¬ GueltigAbleitung TestD [] [] (.bxor 2 (.lit 6) (.lit 3)) 0 3 := by decide

/-- `3 shl 2` printed as `(0, 12)`: `3 * 2 ^ 2`, both operands nonneg,
    operand bound `3 < 2^32`, amount `2 < 32` (PLAN-BITS.md section 2). -/
example : GueltigAbleitung TestD [] [] (.shl 32 (.lit 3) (.lit 2)) 0 12 := by decide

/-- FORGED proof: a negative value shifted -- no range at all. -/
example : ¬ GueltigAbleitung TestD [] [] (.shl 32 (.sub (.lit 0) (.lit 1)) (.lit 2)) 0 0 := by decide

/-- FORGED proof: the amount `32` reaches the width -- the C UB row. -/
example : ¬ GueltigAbleitung TestD [] [] (.shl 32 (.lit 3) (.lit 32)) 0 0 := by decide

/-- `12 shr 2` printed as `(0, 12)`: a right shift never widens (M137). -/
example : GueltigAbleitung TestD [] [] (.shr 32 (.lit 12) (.lit 2)) 0 12 := by decide

/-- FORGED proof: a negative value shifted right -- no range at all. -/
example : ¬ GueltigAbleitung TestD [] [] (.shr 32 (.sub (.lit 0) (.lit 1)) (.lit 2)) 0 0 := by decide

/-- FORGED proof: the amount `40` is past the width -- undefined in C. -/
example : ¬ GueltigAbleitung TestD [] [] (.shr 32 (.lit 12) (.lit 40)) 0 0 := by decide

/-! ### CUT-4 probes: variables and carrier accesses -/

/-- Variable `0` in `[3 .. 3]` printed as `(3, 3)`: the context lookup hits. -/
example : GueltigAbleitung TestD [.int 3 3] [] (.var 0) 3 3 := by decide

/-- MISMATCHED print: variable `0` claimed as `(0, 0)` -- the lookup says
    `(3, 3)`, so the claim is provably not valid. -/
example : ¬ GueltigAbleitung TestD [.int 3 3] [] (.var 0) 0 0 := by decide

/-- DANGLING print: variable `5` in a one-entry context -- no lookup, no range. -/
example : ¬ GueltigAbleitung TestD [.int 3 3] [] (.var 5) 3 3 := by decide

/-- MISTYPED print: variable `0` of type `bool` claimed as an int range --
    the lookup says `none` for non-int types. -/
example : ¬ GueltigAbleitung TestD [.bool] [] (.var 0) 0 0 := by decide

/-- The global printed as `(0, 7)`: its declared type, under the held guard. -/
example : GueltigAbleitung TestD [] [Res.held ()] (.glob ()) 0 7 := by decide

/-- FORGED guard: the same global with empty hands -- the guard fails, so the
    table yields no range at all. -/
example : ¬ GueltigAbleitung TestD [] [] (.glob ()) 0 7 := by decide

/-- A variable under arithmetic: `x + 1` with `x : 3 .. 3` is `(4, 4)` --
    reads lift through the closed shapes. -/
example : GueltigAbleitung TestD [.int 3 3] [Res.held ()] (.add (.var 0) (.lit 1)) 4 4 := by decide


end Gabbro.Grammatik
