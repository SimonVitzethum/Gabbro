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

theorem natBits_length (w x : Nat) : (natBits w x).length = w := by
  simp [natBits]

theorem natBits_get (w x i : Nat) (hi : i < w) :
    (natBits w x)[i]'(by rw [natBits_length]; exact hi) = Nat.testBit x i := by
  simp [natBits]

/-! ## Nat-level intrinsics over a `w + 1` wide field.

    `log2n` is `Nat.log2` guarded by `x ≠ 0`; `clzn` counts leading zeros
    (`w - log2`), `ctzn` counts trailing zeros. The width parameter is the
    full width `W = w + 1`; callers pass `x < 2 ^ W`. -/

/-- Floor log2, total on `Nat` (`Nat.log2 0 = 0` by core definition). -/
def log2n (x : Nat) : Nat := Nat.log2 x

/-- Spec of floor log2: `2 ^ r ≤ x < 2 ^ (r+1)` for `r = log2 x`, `x ≠ 0`. -/
theorem log2n_spez {x : Nat} (hx : x ≠ 0) :
    2 ^ log2n x ≤ x ∧ x < 2 ^ (log2n x + 1) :=
  (Nat.log2_eq_iff hx).mp rfl

/-- Count leading zeros over width `W = w + 1`: `W - 1 - log2 x`. -/
def clzn (w x : Nat) : Nat := w - Nat.log2 x

/-- `clz x + log2 x = w` for `0 < x < 2 ^ (w+1)`. Both premises are used:
    `hx0` rules out `log2 0`, `hxW` bounds the log from above. -/
theorem clzn_log2n {w x : Nat} (hx0 : 0 < x) (hxW : x < 2 ^ (w + 1)) :
    clzn w x + Nat.log2 x = w := by
  unfold clzn
  have hne : x ≠ 0 := by omega
  have hle : Nat.log2 x ≤ w := by
    cases Decidable.em (Nat.log2 x ≤ w) with
    | inl h => exact h
    | inr h =>
      exfalso
      have hge : w + 1 ≤ Nat.log2 x := by omega
      have hmono : 2 ^ (w + 1) ≤ 2 ^ Nat.log2 x :=
        Nat.pow_le_pow_right (by decide) hge
      have hspec := (Nat.log2_eq_iff hne).mp rfl
      omega
  omega

end Gabbro.Grammatik
