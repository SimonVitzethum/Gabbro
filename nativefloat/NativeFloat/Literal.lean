/- Compile-time literal conversion without intermediate integer rounding. -/
module
public import NativeFloat.IntConversion
import all NativeFloat.IntConversion
@[expose] public section

namespace RootNativeFloat
open Float.Model
open Float.Model.UnpackedFloat

/-- Round a source fraction only after division of its exact integer
    mantissas. Runtime arithmetic continues to use the native primitives. -/
def canonLiteral (q : Int × Int) : Float :=
  let exact (z : Int) : UnpackedFloat :=
    if h : z = 0 then .zero .positive
    else .finite (if z < 0 then .negative else .positive) z.natAbs 0 (Int.natAbs_pos.mpr h)
  Float.ofModel (Float.Model.pack (UnpackedFloat.div Format.binary64 (exact q.1) (exact q.2)))

private theorem padded_integer_round (s : Sign) (m k : Nat) (positive : 0 < m)
    (enough : -(k : Int) ≤ Format.binary64.targetExponent (totalExponent m 0)) :
    round Format.binary64 s m 0 =
      roundWithAccuracy Format.binary64 s (m <<< k) (-(k : Int)) .exact := by
  let t := Format.binary64.targetExponent (totalExponent m 0)
  have lower : -53 ≤ t := by
    dsimp [t, Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  have initial : shiftToTargetExponent Format.binary64 (m <<< k) (-(k : Int)) .exact =
      shiftToTargetExponent Format.binary64 (m <<< 53) (-53) .exact := by
    rw [integer_initial m k positive, integer_initial m 53 positive]
    change (Nat.repeat ExtendedMantissa.shiftRightOne (t + k).toNat ⟨m <<< k, false, false⟩,
        -(k : Int) + (t + k).toNat) =
      (Nat.repeat ExtendedMantissa.shiftRightOne (t + 53).toNat ⟨m <<< 53, false, false⟩,
        -53 + (t + 53).toNat)
    by_cases small : k ≤ 53
    · have amount : (t + 53).toNat = (53 - k) + (t + k).toNat := by dsimp [t] at *; omega
      have shifted : m <<< 53 = (m <<< k) <<< (53 - k) := by
        rw [← Nat.shiftLeft_add]
        congr 1
        omega
      rw [amount, shifted, repeat_sum, shifted_exact]
      congr 1
      omega
    · have amount : (t + k).toNat = (k - 53) + (t + 53).toNat := by omega
      have shifted : m <<< k = (m <<< 53) <<< (k - 53) := by
        rw [← Nat.shiftLeft_add]
        congr 1
        omega
      rw [amount, shifted, repeat_sum, shifted_exact]
      congr 1
      omega
  have same : roundWithAccuracy Format.binary64 s (m <<< k) (-(k : Int)) .exact =
      roundWithAccuracy Format.binary64 s (m <<< 53) (-53) .exact := by
    unfold roundWithAccuracy
    rw [initial]
  exact (round_integer_prescale s m positive).trans same.symm

private theorem exact_div_one (s : Sign) (m : Nat) (positive : 0 < m) :
    UnpackedFloat.div Format.binary64 (.finite s m 0 positive)
      (.finite .positive 1 0 (by decide)) = round Format.binary64 s m 0 := by
  let t := min 0 (Format.binary64.targetExponent (totalExponent m 0 - 1))
  let k := (-t).toNat
  have nonpositive : t ≤ 0 := by dsimp [t]; omega
  have back : t = -(k : Int) := by dsimp [k]; omega
  have enough : -(k : Int) ≤ Format.binary64.targetExponent (totalExponent m 0) := by
    rw [← back]
    dsimp [t, Format.targetExponent]
    omega
  have core : divCore Format.binary64 m 0 1 0 = (m <<< k, t, .exact) := by
    unfold divCore
    change ((m <<< (0 - t).toNat) / 1, t,
      accuracyOfFraction ((m <<< (0 - t).toNat) % 1) 1) = _
    have amount : (0 - t).toNat = k := by dsimp [k]; omega
    rw [amount]
    simp [accuracyOfFraction]
  simp only [UnpackedFloat.div, core, back, sign_div_one]
  exact (padded_integer_round s m k positive enough).symm

/-- Exact integer fractions preserve the source integer conversion, even
    outside machine-word bounds and when the result overflows to infinity. -/
theorem canonLiteral_integer (z : Int) : canonLiteral (z, 1) = Float.ofInt z := by
  by_cases zero : z = 0
  · subst z
    rw [ofInt_model]
    rfl
  · unfold canonLiteral
    dsimp only
    rw [dif_neg zero, dif_neg (by decide : ¬ (1 : Int) = 0)]
    change Float.ofModel (Float.Model.pack (UnpackedFloat.div Format.binary64
      (.finite (if z < 0 then .negative else .positive) z.natAbs 0 (Int.natAbs_pos.mpr zero))
      (.finite .positive 1 0 (by decide)))) = Float.ofInt z
    rw [exact_div_one, ofInt_model]
    apply congrArg Float.ofModel
    apply congrArg Float.Model.pack
    exact (integer_round z zero).symm

/-- Zero denominators use the existing toolchain infinity/NaN classification. -/
theorem canonLiteral_den_zero (z : Int) :
    canonLiteral (z, 0) = if z = 0 then Float.ofModel (Float.Model.pack .notANumber)
      else Float.ofModel (Float.Model.pack (.infinity (if z < 0 then .negative else .positive))) := by
  by_cases zero : z = 0
  · subst z
    rfl
  · simp only [canonLiteral, zero, ↓reduceDIte, UnpackedFloat.div, sign_div_one]

/-- A zero numerator retains the denominator's sign unless both are zero. -/
theorem canonLiteral_zero_num (d : Int) :
    canonLiteral (0, d) = if d = 0 then Float.ofModel (Float.Model.pack .notANumber)
      else Float.ofModel (Float.Model.pack (.zero (if d < 0 then .negative else .positive))) := by
  by_cases zero : d = 0
  · subst d
    rfl
  · have sign (s : Sign) : Sign.positive / s = s := by cases s <;> rfl
    simp only [canonLiteral, zero, ↓reduceDIte, UnpackedFloat.div, sign]

/-- The smallest subnormal must survive exact compile-time fraction conversion. -/
theorem canonLiteral_subnormal_one : (canonLiteral (1, 2 ^ 1074)).toBits = 1 := by decide

theorem canonLiteral_subnormal_two : (canonLiteral (2, 2 ^ 1074)).toBits = 2 := by decide

theorem canonLiteral_subnormal_negative :
    (canonLiteral (-1, 2 ^ 1074)).toBits = 0x8000000000000001 ∧
      (canonLiteral (1, -(2 ^ 1074))).toBits = 0x8000000000000001 ∧
      (canonLiteral (-1, -(2 ^ 1074))).toBits = 1 := by decide

end RootNativeFloat
