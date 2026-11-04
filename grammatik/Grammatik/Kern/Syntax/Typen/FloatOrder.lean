/- Order facts used by the existing native-float answer-class decision. -/
module
public import Init.Data.Float
@[expose] public section

namespace Gabbro.Grammatik.NativeFloat
open Float.Model
open Float.Model.UnpackedFloat

private theorem lexLE (a b : Int) (m n : Nat) :
    ((compare a b).then (compare m n)).isLE = true ↔ a < b ∨ a = b ∧ m ≤ n := by
  rw [Ordering.isLE_then_iff_or, Int.compare_eq_lt, Int.compare_eq_eq,
    Ordering.isLE_iff_ne_gt]
  change (a < b ∨ a = b ∧ compare m n ≠ Ordering.gt) ↔ a < b ∨ a = b ∧ m ≤ n
  rw [Nat.compare_ne_gt]

private theorem unpacked_cases {P : UnpackedFloat → Prop}
    (negativeInfinity : P (.infinity .negative))
    (positiveInfinity : P (.infinity .positive))
    (notANumber : P .notANumber)
    (negativeZero : P (.zero .negative))
    (positiveZero : P (.zero .positive))
    (negativeFinite : ∀ m e h, P (.finite .negative m e h))
    (positiveFinite : ∀ m e h, P (.finite .positive m e h))
    (a : UnpackedFloat) : P a := by
  cases a with
  | infinity s => cases s <;> assumption
  | notANumber => exact notANumber
  | zero s => cases s <;> assumption
  | finite s m e h =>
      cases s
      · exact negativeFinite m e h
      · exact positiveFinite m e h

private theorem unpacked_le_trans (a b c : UnpackedFloat)
    (ab : a.le b = true) (bc : b.le c = true) : a.le c = true := by
  have nn : compare Sign.negative Sign.negative = Ordering.eq := rfl
  have np : compare Sign.negative Sign.positive = Ordering.lt := rfl
  have pn : compare Sign.positive Sign.negative = Ordering.gt := rfl
  have pp : compare Sign.positive Sign.positive = Ordering.eq := rfl
  induction a using unpacked_cases <;> induction b using unpacked_cases <;>
    induction c using unpacked_cases
  all_goals simp_all [UnpackedFloat.le, UnpackedFloat.compare, Option.any,
    Ordering.swap_then, Int.compare_swap, Nat.compare_swap, lexLE, nn, np, pn, pp]
  all_goals rcases ab with h1 | ⟨h1, h2⟩ <;>
    rcases bc with h3 | ⟨h3, h4⟩ <;> omega

private theorem unpacked_le_refl (a : UnpackedFloat) (ha : a.isFinite = true) : a.le a = true := by
  induction a using unpacked_cases
  all_goals simp_all [UnpackedFloat.isFinite, UnpackedFloat.le,
    UnpackedFloat.compare, Ordering.swap_then, Int.compare_swap, Nat.compare_swap, lexLE]

private theorem unpacked_lower (a x y : UnpackedFloat)
    (ha : a.isFinite = false) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (ax : a.le x = true) : a.le y = true := by
  induction a using unpacked_cases <;> induction x using unpacked_cases <;>
    induction y using unpacked_cases
  all_goals simp_all [UnpackedFloat.isFinite, UnpackedFloat.le, UnpackedFloat.compare]

private theorem unpacked_upper (a x y : UnpackedFloat)
    (ha : a.isFinite = false) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (xa : x.le a = true) : y.le a = true := by
  induction a using unpacked_cases <;> induction x using unpacked_cases <;>
    induction y using unpacked_cases
  all_goals simp_all [UnpackedFloat.isFinite, UnpackedFloat.le, UnpackedFloat.compare]

/-- The native ordered comparison is transitive, including infinite endpoints. -/
theorem le_trans {a b c : Float} (ab : Float.le a b = true) (bc : Float.le b c = true) :
    Float.le a c = true :=
  unpacked_le_trans a.toModel.unpack b.toModel.unpack c.toModel.unpack ab bc

/-- Every finite native value compares less than or equal to itself. -/
theorem le_refl {a : Float} (ha : a.isFinite = true) : Float.le a a = true :=
  unpacked_le_refl a.toModel.unpack ha

/-- A nonfinite lower bound admitting one finite point admits every finite point. -/
theorem lower_le {a x y : Float} (ha : a.isFinite = false)
    (hx : x.isFinite = true) (hy : y.isFinite = true) (ax : Float.le a x = true) :
    Float.le a y = true :=
  unpacked_lower a.toModel.unpack x.toModel.unpack y.toModel.unpack ha hx hy ax

/-- The corresponding fact for an upper bound. -/
theorem le_upper {a x y : Float} (ha : a.isFinite = false)
    (hx : x.isFinite = true) (hy : y.isFinite = true) (xa : Float.le x a = true) :
    Float.le y a = true :=
  unpacked_upper a.toModel.unpack x.toModel.unpack y.toModel.unpack ha hx hy xa

end Gabbro.Grammatik.NativeFloat
