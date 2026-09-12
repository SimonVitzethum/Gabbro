/-
  File:      Grammatik/Bits.lean
  Subject:   BIT INTRINSICS (lane 68) -- PLAN-BITS.md section 3, model half.

  Parametric in the width from the start: the width is carried as `w + 1`,
  so no `Nat` truncation can hide a wrong bound. All bit access goes through
  `Nat.testBit` on the value seen as a `Nat`; results are packed back with
  `Nat` arithmetic. The argument type excludes zero for `clz` / `ctz` /
  `log2`, so the C lowering never reaches the undefined `__builtin_clz(0)`
  case.
-/
import Grammatik.Typen

namespace Gabbro.Grammatik

/-- Bit list of `x` over `w` positions, LSB first. -/
def natBits (w x : Nat) : List Bool :=
  List.ofFn (fun i : Fin w => Nat.testBit x i.val)

end Gabbro.Grammatik
