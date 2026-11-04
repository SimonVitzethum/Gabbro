/- Correspondence and exact-value facts for compile-time native literals. -/
module
public import NativeFloat.Literal
public import NativeFloat.IntConversion
import all NativeFloat.IntConversion
import all NativeFloat.NormalForm
import all NativeFloat.IntSticky
@[expose] public section

namespace RootNativeFloat
open Float.Model
open Float.Model.UnpackedFloat

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
    have fixed := integer_initial m 53 positive
    simp only [Int.cast_ofNat_Int] at fixed
    rw [integer_initial m k positive, fixed]
    change (Nat.repeat ExtendedMantissa.shiftRightOne (t + k).toNat ⟨m <<< k, false, false⟩,
        -(k : Int) + (t + k).toNat) =
      (Nat.repeat ExtendedMantissa.shiftRightOne (t + 53).toNat ⟨m <<< 53, false, false⟩,
        (-53 : Int) + (t + 53).toNat)
    by_cases small : k ≤ 53
    · have amount : (t + 53).toNat = (53 - k) + (t + k).toNat := by dsimp [t] at *; omega
      have shifted : m <<< 53 = (m <<< k) <<< (53 - k) := by
        rw [← Nat.shiftLeft_add]
        congr 1
        omega
      have kept : Nat.repeat ExtendedMantissa.shiftRightOne (53 - k) ⟨m <<< 53, false, false⟩ =
          ⟨m <<< k, false, false⟩ := by
        rw [shifted]
        exact shifted_exact (m <<< k) (53 - k)
      have composed : Nat.repeat ExtendedMantissa.shiftRightOne ((53 - k) + (t + k).toNat)
          ⟨m <<< 53, false, false⟩ =
          Nat.repeat ExtendedMantissa.shiftRightOne (t + k).toNat ⟨m <<< k, false, false⟩ :=
        (repeat_sum ExtendedMantissa.shiftRightOne (53 - k) (t + k).toNat ⟨m <<< 53, false, false⟩).trans
          (congrArg (Nat.repeat ExtendedMantissa.shiftRightOne (t + k).toNat) kept)
      apply Prod.ext
      · change Nat.repeat ExtendedMantissa.shiftRightOne (t + k).toNat ⟨m <<< k, false, false⟩ =
          Nat.repeat ExtendedMantissa.shiftRightOne (t + 53).toNat ⟨m <<< 53, false, false⟩
        rw [amount]
        exact composed.symm
      · change -(k : Int) + (t + k).toNat = (-53 : Int) + (t + 53).toNat
        rw [amount]
        omega
    · have amount : (t + k).toNat = (k - 53) + (t + 53).toNat := by omega
      have shifted : m <<< k = (m <<< 53) <<< (k - 53) := by
        rw [← Nat.shiftLeft_add]
        congr 1
        omega
      have kept : Nat.repeat ExtendedMantissa.shiftRightOne (k - 53) ⟨m <<< k, false, false⟩ =
          ⟨m <<< 53, false, false⟩ := by
        rw [shifted]
        exact shifted_exact (m <<< 53) (k - 53)
      have composed : Nat.repeat ExtendedMantissa.shiftRightOne ((k - 53) + (t + 53).toNat)
          ⟨m <<< k, false, false⟩ =
          Nat.repeat ExtendedMantissa.shiftRightOne (t + 53).toNat ⟨m <<< 53, false, false⟩ :=
        (repeat_sum ExtendedMantissa.shiftRightOne (k - 53) (t + 53).toNat ⟨m <<< k, false, false⟩).trans
          (congrArg (Nat.repeat ExtendedMantissa.shiftRightOne (t + 53).toNat) kept)
      apply Prod.ext
      · change Nat.repeat ExtendedMantissa.shiftRightOne (t + k).toNat ⟨m <<< k, false, false⟩ =
          Nat.repeat ExtendedMantissa.shiftRightOne (t + 53).toNat ⟨m <<< 53, false, false⟩
        rw [amount]
        exact composed
      · change -(k : Int) + (t + k).toNat = (-53 : Int) + (t + 53).toNat
        rw [amount]
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
    simp only [Nat.div_one, Nat.mod_one, accuracyOfFraction, ↓reduceIte]
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
  · simp only [canonLiteral, zero, ↓reduceDIte, UnpackedFloat.div, sign_div_one, ↓reduceIte]

/-- A zero numerator retains the denominator's sign unless both are zero. -/
theorem canonLiteral_zero_num (d : Int) :
    canonLiteral (0, d) = if d = 0 then Float.ofModel (Float.Model.pack .notANumber)
      else Float.ofModel (Float.Model.pack (.zero (if d < 0 then .negative else .positive))) := by
  by_cases zero : d = 0
  · subst d
    rfl
  · have sign (s : Sign) : Sign.positive / s = s := by cases s <;> rfl
    simp only [canonLiteral, zero, ↓reduceDIte, UnpackedFloat.div, sign, ↓reduceIte]

private theorem literal_mantissas (s t : Sign) (m d : Nat) (hm : 0 < m) (hd : 0 < d) :
    canonLiteral (s.apply m, t.apply d) = Float.ofModel (Float.Model.pack
      (UnpackedFloat.div Format.binary64 (.finite s m 0 hm) (.finite t d 0 hd))) := by
  have input (s : Sign) (n : Nat) (hn : 0 < n) :
      (if h : s.apply n = 0 then UnpackedFloat.zero .positive else
        .finite (if s.apply n < 0 then .negative else .positive)
          (s.apply n).natAbs 0 (Int.natAbs_pos.mpr h)) = .finite s n 0 hn := by
    have positive : (0 : Int) < n := by omega
    have nonzero : (n : Int) ≠ 0 := by omega
    have negNonzero : -(n : Int) ≠ 0 := by omega
    have negative : -(n : Int) < 0 := by omega
    have nonnegative : ¬ (n : Int) < 0 := by omega
    cases s <;> simp only [Sign.apply, nonzero, negNonzero, negative, nonnegative,
      ↓reduceDIte, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]
  unfold canonLiteral
  dsimp only
  rw [input s m hm, input t d hd]

private theorem subnormal_core (m : Nat) (small : m = 1 ∨ m = 2) :
    divCore Format.binary64 m 0 (2 ^ 1074) 0 = (m, -1074, .exact) := by
  have target : min (0 - 0 : Int) (Format.binary64.targetExponent
      (totalExponent m 0 - totalExponent (2 ^ 1074) 0)) = -1074 := by
    rcases small with rfl | rfl <;>
      simp only [totalExponent, Nat.log2_two_pow, Format.targetExponent] <;> rfl
  unfold divCore
  dsimp only
  rw [target]
  change ((m <<< 1074) / 2 ^ 1074, (-1074 : Int),
    accuracyOfFraction ((m <<< 1074) % 2 ^ 1074) (2 ^ 1074)) = _
  rw [Nat.shiftLeft_eq, Nat.mul_div_cancel m (Nat.two_pow_pos 1074), Nat.mul_mod_left]
  rfl

private theorem literal_subnormal (s t : Sign) (m : Nat) (small : m = 1 ∨ m = 2) :
    canonLiteral (s.apply m, t.apply ((2 ^ 1074 : Nat) : Int)) =
      Float.ofModel (Float.Model.pack (.finite (s / t) m (-1074) (by omega))) := by
  rw [literal_mantissas s t m (2 ^ 1074) (by omega) (Nat.two_pow_pos 1074)]
  simp only [UnpackedFloat.div, subnormal_core m small]
  apply congrArg Float.ofModel
  apply congrArg Float.Model.pack
  apply exact_at_target
  rcases small with rfl | rfl <;> rfl

/-- The smallest subnormal must survive exact compile-time fraction conversion. -/
theorem canonLiteral_subnormal_one : (canonLiteral (1, 2 ^ 1074)).toBits = 1 := by
  rw [← Int.natCast_pow]
  change (canonLiteral (Sign.positive.apply (1 : Int),
    Sign.positive.apply ((2 ^ 1074 : Nat) : Int))).toBits = 1
  rw [literal_subnormal .positive .positive 1 (Or.inl rfl)]
  cbv

theorem canonLiteral_subnormal_two : (canonLiteral (2, 2 ^ 1074)).toBits = 2 := by
  rw [← Int.natCast_pow]
  change (canonLiteral (Sign.positive.apply (2 : Int),
    Sign.positive.apply ((2 ^ 1074 : Nat) : Int))).toBits = 2
  rw [literal_subnormal .positive .positive 2 (Or.inr rfl)]
  cbv

theorem canonLiteral_subnormal_negative :
    (canonLiteral (-1, 2 ^ 1074)).toBits = 0x8000000000000001 ∧
      (canonLiteral (1, -(2 ^ 1074))).toBits = 0x8000000000000001 ∧
      (canonLiteral (-1, -(2 ^ 1074))).toBits = 1 := by
  rw [← Int.natCast_pow]
  constructor
  · change (canonLiteral (Sign.negative.apply (1 : Int),
      Sign.positive.apply ((2 ^ 1074 : Nat) : Int))).toBits = _
    rw [literal_subnormal .negative .positive 1 (Or.inl rfl)]
    cbv
  · constructor
    · change (canonLiteral (Sign.positive.apply (1 : Int),
        Sign.negative.apply ((2 ^ 1074 : Nat) : Int))).toBits = _
      rw [literal_subnormal .positive .negative 1 (Or.inl rfl)]
      cbv
    · change (canonLiteral (Sign.negative.apply (1 : Int),
        Sign.negative.apply ((2 ^ 1074 : Nat) : Int))).toBits = _
      rw [literal_subnormal .negative .negative 1 (Or.inl rfl)]
      cbv

end RootNativeFloat
