/- Canonical native rounding states used by wide integer conversion. -/
module
public import NativeFloat.IntConversion
public import NativeFloat.IntSticky
public import NativeFloat.RoundState
import all NativeFloat.IntConversion
import all NativeFloat.IntSticky
import all NativeFloat.NormalForm
import all NativeFloat.Transport
import all NativeFloat.RoundState
@[expose] public section

namespace RootNativeFloat.NativeScale
open Float.Model
open Float.Model.UnpackedFloat

private theorem retained_bounds (g : Nat) (lower : 2 ^ 55 ≤ g) (upper : g < 2 ^ 56) :
    2 ^ 52 ≤ ((⟨g, false, false⟩ : ExtendedMantissa) >>> 3).roundedMantissa ∧
      ((⟨g, false, false⟩ : ExtendedMantissa) >>> 3).roundedMantissa ≤ 2 ^ 53 := by
  have bounds := rounded_bounds ((⟨g, false, false⟩ : ExtendedMantissa) >>> 3)
  have mantissa : ((⟨g, false, false⟩ : ExtendedMantissa) >>> 3).mantissa = g / 8 := by
    change (Nat.repeat ExtendedMantissa.shiftRightOne 3 ⟨g, false, false⟩).mantissa = _
    rw [exact_shift_bits g 2]
  rw [mantissa] at bounds
  omega

private theorem final_shift (r : Nat) (e : Int) (nonnegative : 0 ≤ e)
    (lower : 2 ^ 52 ≤ r) (upper : r ≤ 2 ^ 53) :
    shiftToTargetExponent Format.binary64 r e .exact =
      if r = 2 ^ 53 then (⟨2 ^ 52, false, false⟩, e + 1)
      else (⟨r, false, false⟩, e) := by
  exact after_round_shift Format.binary64 r e (by change -1074 ≤ e; omega) lower upper

private theorem retained_round (s : Sign) (g : Nat) (lower : 2 ^ 55 ≤ g) (upper : g < 2 ^ 56) :
    let r := ((⟨g, false, false⟩ : ExtendedMantissa) >>> 3).roundedMantissa
    round Format.binary64 s g 0 =
      if h : r = 2 ^ 53 then .finite s (2 ^ 52) 4 (by decide)
      else .finite s r 3 (by have := (retained_bounds g lower upper).1; omega) := by
  dsimp only
  have log : g.log2 = 55 := (Nat.log2_eq_iff (by omega)).mpr ⟨lower, upper⟩
  have target : Format.binary64.targetExponent (totalExponent g 0) = 3 := by
    simp only [Format.targetExponent, totalExponent, log]
    rfl
  have first : shiftToTargetExponent Format.binary64 g 0 .exact =
      (((⟨g, false, false⟩ : ExtendedMantissa) >>> 3), 3) := by
    unfold shiftToTargetExponent
    rw [target]
    rfl
  have bounds := retained_bounds g lower upper
  have same : round Format.binary64 s g 0 = roundWithAccuracy Format.binary64 s g 0 .exact := by
    unfold round decreaseExponent
    rw [target]
    rfl
  rw [same]
  unfold roundWithAccuracy
  rw [first]
  dsimp only
  have last := final_shift _ 3 (by decide) bounds.1 bounds.2
  by_cases carry : ((⟨g, false, false⟩ : ExtendedMantissa) >>> 3).roundedMantissa = 2 ^ 53
  · rw [if_pos carry] at last
    rw [last]
    dsimp only
    simp only [carry, Nat.ne_of_gt (Nat.two_pow_pos 52), ↓reduceDIte] <;> rfl
  · have nonzero : ((⟨g, false, false⟩ : ExtendedMantissa) >>> 3).roundedMantissa ≠ 0 := by omega
    rw [if_neg carry] at last
    rw [last]
    dsimp only
    simp only [carry, nonzero, ↓reduceDIte]

private theorem magnitude_bounds (n : Nat) (large : 2 ^ 55 ≤ n) :
    let k := n.log2 - 55
    let g := (n >>> k) ||| (if n % 2 ^ k = 0 then 0 else 1)
    2 ^ 55 ≤ g ∧ g < 2 ^ 56 ∧ n.log2 = k + 55 := by
  dsimp only
  have positive : 0 < n := by omega
  have bounds := (Nat.log2_eq_iff (Nat.ne_of_gt positive)).mp rfl
  have log : 55 ≤ n.log2 := (Nat.le_log2 (Nat.ne_of_gt positive)).mpr large
  have exponent : n.log2 = (n.log2 - 55) + 55 := by omega
  have power : 2 ^ n.log2 = 2 ^ 55 * 2 ^ (n.log2 - 55) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have quotientLower : 2 ^ 55 ≤ n / 2 ^ (n.log2 - 55) :=
    (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by rw [← power]; exact bounds.1)
  have quotientUpper : n / 2 ^ (n.log2 - 55) < 2 ^ 56 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    have top : 2 ^ (n.log2 + 1) = 2 ^ 56 * 2 ^ (n.log2 - 55) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [← top]
    exact bounds.2
  rw [Nat.shiftRight_eq_div_pow]
  refine ⟨?_, Nat.or_lt_two_pow quotientUpper ?_, exponent⟩
  · exact Nat.le_trans quotientLower Nat.left_le_or
  · split <;> decide

private theorem magnitude_round (s : Sign) (n : Nat) (large : 2 ^ 55 ≤ n) :
    let k := n.log2 - 55
    let g := (n >>> k) ||| (if n % 2 ^ k = 0 then 0 else 1)
    let r := ((⟨g, false, false⟩ : ExtendedMantissa) >>> 3).roundedMantissa
    round Format.binary64 s n 0 =
      if h : r = 2 ^ 53 then .finite s (2 ^ 52) ((k : Int) + 4) (by decide)
      else .finite s r ((k : Int) + 3) (by
        have bounds := magnitude_bounds n large
        have := (retained_bounds g bounds.1 bounds.2.1).1
        omega) := by
  dsimp only
  let k := n.log2 - 55
  let g := (n >>> k) ||| (if n % 2 ^ k = 0 then 0 else 1)
  have bounds : 2 ^ 55 ≤ g ∧ g < 2 ^ 56 ∧ n.log2 = k + 55 := magnitude_bounds n large
  let r := ((⟨g, false, false⟩ : ExtendedMantissa) >>> 3).roundedMantissa
  have rounded : 2 ^ 52 ≤ r ∧ r ≤ 2 ^ 53 := retained_bounds g bounds.1 bounds.2.1
  have rpositive : 0 < r := by omega
  change round Format.binary64 s n 0 =
    if h : r = 2 ^ 53 then .finite s (2 ^ 52) ((k : Int) + 4) (by decide)
    else .finite s r ((k : Int) + 3) rpositive
  have target : Format.binary64.targetExponent (totalExponent n 0) = (k : Int) + 3 := by
    simp only [Format.targetExponent, totalExponent, bounds.2.2, Int.natCast_add]
    change max ((k : Int) + 55 + 1 + 0 - 53) (-1074) = (k : Int) + 3
    omega
  have first : shiftToTargetExponent Format.binary64 n 0 .exact =
      (((⟨g, false, false⟩ : ExtendedMantissa) >>> 3), (k : Int) + 3) := by
    unfold shiftToTargetExponent
    rw [target]
    unfold shiftToExponent
    dsimp only
    have amount : ((k : Int) + 3 - 0).toNat = k + 3 := by omega
    rw [amount]
    apply Prod.ext
    · change (⟨n, false, false⟩ : ExtendedMantissa) >>> (k + 3) =
        (⟨g, false, false⟩ : ExtendedMantissa) >>> 3
      exact (jam56_shift n k).symm
    · change (0 : Int) + (k + 3 : Nat) = (k : Int) + 3
      omega
  have same : round Format.binary64 s n 0 = roundWithAccuracy Format.binary64 s n 0 .exact := by
    unfold round decreaseExponent
    rw [target]
    dsimp only
    have noDecrease : (0 - ((k : Int) + 3)).toNat = 0 := by omega
    rw [noDecrease]
    rfl
  rw [same]
  unfold roundWithAccuracy
  rw [first]
  dsimp only
  have last := final_shift _ ((k : Int) + 3) (by omega) rounded.1 rounded.2
  by_cases carry : r = 2 ^ 53
  · rw [if_pos carry] at last
    rw [last]
    dsimp only
    have exponent : (k : Int) + 3 + 1 = (k : Int) + 4 := by omega
    simp only [carry, exponent, Nat.ne_of_gt (Nat.two_pow_pos 52), ↓reduceDIte] <;> rfl
  · have nonzero : r ≠ 0 := Nat.ne_of_gt rpositive
    rw [if_neg carry] at last
    rw [last]
    dsimp only
    simp only [carry, nonzero, ↓reduceDIte] <;> rfl

private theorem canonical_unpack (s : Sign) (m : Nat) (e : Int) (positive : 0 < m)
    (lower : 2 ^ 52 ≤ m) (upper : m < 2 ^ 53) (emin : -1074 ≤ e) (emax : e ≤ 971) :
    UnpackedFloat.unpack Format.binary64
      (UnpackedFloat.pack Format.binary64 (.finite s m e positive)) = .finite s m e positive := by
  exact normal_unpack Format.binary64 s m e positive lower upper emin emax

private theorem power_word (s : Sign) (j : Nat) (lower : 1023 ≤ j) (upper : j ≤ 1992) :
    Float.ofBits (UInt64.ofNat ((if s = .negative then 2 ^ 63 else 0) + j * 2 ^ 52)) =
      Float.ofModel (Float.Model.pack (.finite s (2 ^ 52) ((j : Int) - 1075) (by decide))) := by
  have biased : (((j : Int) - 1075) + Format.binary64.exponentBias +
      Format.binary64.mantissaBitsWithoutImplicit).toNat = j := by
    change (((j : Int) - 1075) + 1023 + 52).toNat = j
    omega
  have packed : UnpackedFloat.pack Format.binary64
      (.finite s (2 ^ 52) ((j : Int) - 1075) (by decide)) =
      packComponents Format.binary64 s (BitVec.ofNat 11 j) 0#52 := by
    have implicitBit : BitVec.ofNat 52 (2 ^ 52) = 0#52 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, Nat.mod_self, Nat.zero_mod]
    have noOverflow : ¬ 2 ^ Format.binary64.exponentBits ≤ j + 1 := by
      change ¬ 2048 ≤ j + 1
      omega
    have normal : (52 : Nat) + 1 = Format.binary64.mantissaBits := rfl
    simp only [UnpackedFloat.pack, Nat.log2_two_pow, biased, noOverflow, normal,
      ↓reduceIte, implicitBit]
  have field : (BitVec.ofNat 11 j).toNat = j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have encoded : (UnpackedFloat.pack Format.binary64
      (.finite s (2 ^ 52) ((j : Int) - 1075) (by decide))).toNat =
      (if s = .negative then 2 ^ 63 else 0) + j * 2 ^ 52 := by
    rw [packed]
    unfold packComponents
    rw [BitVec.toNat_append, BitVec.toNat_append]
    simp only [field, BitVec.toNat_ofNat, Nat.zero_mod, Nat.or_zero]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (show j < 2 ^ 11 by omega)]
    simp only [Nat.shiftLeft_eq]
    cases s <;> simp [Sign.toBitVec, Nat.add_mul]
  have inWord : (if s = .negative then 2 ^ 63 else 0) + j * 2 ^ 52 < 2 ^ 64 := by
    split <;> omega
  have numeric : ((if s = .negative then 2 ^ 63 else 0) + j * 2 ^ 52) % 2 ^ 64 =
      (UnpackedFloat.pack Format.binary64
        (.finite s (2 ^ 52) ((j : Int) - 1075) (by decide))).toNat :=
    (Nat.mod_eq_of_lt inWord).trans encoded.symm
  have rawBits : (UInt64.ofNat
      ((if s = .negative then 2 ^ 63 else 0) + j * 2 ^ 52)).toBitVec =
      UnpackedFloat.pack Format.binary64
        (.finite s (2 ^ 52) ((j : Int) - 1075) (by decide)) :=
    BitVec.eq_of_toNat_eq numeric
  have raw : UInt64.ofNat ((if s = .negative then 2 ^ 63 else 0) + j * 2 ^ 52) =
      UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
        (.finite s (2 ^ 52) ((j : Int) - 1075) (by decide))) :=
    UInt64.eq_of_toBitVec_eq rawBits
  let target : Float := Float.ofModel (Float.Model.pack
    (.finite s (2 ^ 52) ((j : Int) - 1075) (by decide)))
  have targetBits : target.toBits = UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
      (.finite s (2 ^ 52) ((j : Int) - 1075) (by decide))) := rfl
  have delivered : Float.ofBits (UInt64.ofNat
      ((if s = .negative then 2 ^ 63 else 0) + j * 2 ^ 52)) = Float.ofBits target.toBits :=
    congrArg Float.ofBits (raw.trans targetBits.symm)
  exact delivered.trans (bits_roundtrip target)

private theorem power_unpacked (s : Sign) (j : Nat) (lower : 1023 ≤ j) (upper : j ≤ 1992) :
    (Float.ofBits (UInt64.ofNat ((if s = .negative then 2 ^ 63 else 0) + j * 2 ^ 52))).toModel.unpack =
      .finite s (2 ^ 52) ((j : Int) - 1075) (by decide) := by
  rw [power_word s j lower upper]
  change UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64
    (.finite s (2 ^ 52) ((j : Int) - 1075) (by decide))) = _
  exact canonical_unpack s _ _ (by decide) (by decide) (by decide) (by omega) (by omega)

private theorem sign_positive_mul (s : Sign) : Sign.positive * s = s := by cases s <;> rfl

private theorem mul_canonical_power (s : Sign) (m : Nat) (e : Int) (j : Nat)
    (positive : 0 < m) (lower : 2 ^ 52 ≤ m) (upper : m < 2 ^ 53) (nonnegative : 0 ≤ e)
    (jlower : 1023 ≤ j) :
    UnpackedFloat.mul Format.binary64 (.finite .positive m e positive)
      (.finite s (2 ^ 52) ((j : Int) - 1075) (by decide)) =
      .finite s m (e + ((j : Int) - 1023)) positive := by
  have log : m.log2 = 52 := (Nat.log2_eq_iff (Nat.ne_of_gt positive)).mpr ⟨lower, upper⟩
  have target : Format.binary64.targetExponent (totalExponent m (e + ((j : Int) - 1023))) =
      e + ((j : Int) - 1023) := by
    simp only [Format.targetExponent, totalExponent, log]
    change max (52 + 1 + (e + ((j : Int) - 1023)) - 53) (-1074) = e + ((j : Int) - 1023)
    omega
  have exponent : e + ((j : Int) - 1075) = (e + ((j : Int) - 1023)) - 52 := by omega
  have result := exact_scaled Format.binary64 s m 52 (e + ((j : Int) - 1023)) positive target
  simpa only [UnpackedFloat.mul, sign_positive_mul, Nat.shiftLeft_eq,
    Int.cast_ofNat_Int, exponent] using result

private theorem packed_overflow (s : Sign) (m : Nat) (e : Int) (positive : 0 < m) (overflow : 972 ≤ e) :
    UnpackedFloat.pack Format.binary64 (.finite s m e positive) = packedInfinity Format.binary64 s := by
  unfold UnpackedFloat.pack
  dsimp only
  rw [if_pos (by
    change 2048 ≤ (e + (1023 : Int) + 52).toNat + 1
    omega)]

private theorem retained_unpacked (g : Nat) (lower : 2 ^ 55 ≤ g) (upper : g < 2 ^ 56) :
    (Float.ofModel (Float.Model.ofInt (g : Int))).toModel.unpack = round Format.binary64 .positive g 0 := by
  have input : (Float.ofModel (Float.Model.ofInt (g : Int))).toModel.unpack =
      UnpackedFloat.unpack Format.binary64
        (UnpackedFloat.pack Format.binary64 (UnpackedFloat.ofInt Format.binary64 (g : Int))) := rfl
  rw [input]
  have cp : compare (g : Int) 0 = .gt := Int.compare_eq_gt.mpr (by omega)
  simp only [UnpackedFloat.ofInt, normalize, cp, Int.toNat_natCast]
  let r := ((⟨g, false, false⟩ : ExtendedMantissa) >>> 3).roundedMantissa
  have bounds : 2 ^ 52 ≤ r ∧ r ≤ 2 ^ 53 := retained_bounds g lower upper
  have positive : 0 < r := by omega
  have formed : round Format.binary64 .positive g 0 =
      if h : r = 2 ^ 53 then .finite .positive (2 ^ 52) 4 (by decide)
      else .finite .positive r 3 positive := retained_round .positive g lower upper
  rw [formed]
  by_cases carry : r = 2 ^ 53
  · simp only [carry, ↓reduceDIte]
    exact canonical_unpack .positive _ 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  · simp only [carry, ↓reduceDIte]
    exact canonical_unpack .positive r 3 positive bounds.1 (by omega) (by decide) (by decide)

private theorem packed_product (s : Sign) (n : Nat) (large : 2 ^ 55 ≤ n) :
    let k := n.log2 - 55
    let g := (n >>> k) ||| (if n % 2 ^ k = 0 then 0 else 1)
    let j := min 2047 (k + 1078) - 55
    UnpackedFloat.pack Format.binary64 (round Format.binary64 s n 0) =
      UnpackedFloat.pack Format.binary64 (UnpackedFloat.mul Format.binary64
        (round Format.binary64 .positive g 0)
        (.finite s (2 ^ 52) ((j : Int) - 1075) (by decide))) := by
  dsimp only
  let k := n.log2 - 55
  let g := (n >>> k) ||| (if n % 2 ^ k = 0 then 0 else 1)
  let j := min 2047 (k + 1078) - 55
  change UnpackedFloat.pack Format.binary64 (round Format.binary64 s n 0) =
    UnpackedFloat.pack Format.binary64 (UnpackedFloat.mul Format.binary64
      (round Format.binary64 .positive g 0)
      (.finite s (2 ^ 52) ((j : Int) - 1075) (by decide)))
  have bounds : 2 ^ 55 ≤ g ∧ g < 2 ^ 56 ∧ n.log2 = k + 55 := magnitude_bounds n large
  have jl : 1023 ≤ j := by dsimp [j]; omega
  have scale : (j : Int) - 1023 = (min 969 k : Nat) := by
    by_cases fits : k ≤ 969
    · have cap : min 2047 (k + 1078) = k + 1078 := Nat.min_eq_right (by omega)
      simp only [j, cap, Nat.min_eq_right fits]
      omega
    · have cap : min 2047 (k + 1078) = 2047 := Nat.min_eq_left (by omega)
      simp only [j, cap, Nat.min_eq_left (by omega : 969 ≤ k)]
      decide
  let r := ((⟨g, false, false⟩ : ExtendedMantissa) >>> 3).roundedMantissa
  have rBounds : 2 ^ 52 ≤ r ∧ r ≤ 2 ^ 53 := retained_bounds g bounds.1 bounds.2.1
  have positive : 0 < r := by omega
  have full : round Format.binary64 s n 0 =
      if h : r = 2 ^ 53 then .finite s (2 ^ 52) ((k : Int) + 4) (by decide)
      else .finite s r ((k : Int) + 3) positive := magnitude_round s n large
  have half : round Format.binary64 .positive g 0 =
      if h : r = 2 ^ 53 then .finite .positive (2 ^ 52) 4 (by decide)
      else .finite .positive r 3 positive := retained_round .positive g bounds.1 bounds.2.1
  rw [full, half]
  by_cases carry : r = 2 ^ 53
  · simp only [carry, ↓reduceDIte]
    rw [mul_canonical_power s (2 ^ 52) 4 j (by decide) (by decide) (by decide) (by decide) jl, scale]
    by_cases fits : k ≤ 969
    · rw [Nat.min_eq_right fits]
      have exponent : (k : Int) + 4 = 4 + (k : Int) := by omega
      rw [exponent]
    · rw [Nat.min_eq_left (by omega : 969 ≤ k)]
      exact (packed_overflow s (2 ^ 52) ((k : Int) + 4) (Nat.two_pow_pos 52) (by omega)).trans
        (packed_overflow s (2 ^ 52) (4 + ((969 : Nat) : Int)) (Nat.two_pow_pos 52) (by decide)).symm
  · simp only [carry, ↓reduceDIte]
    rw [mul_canonical_power s r 3 j positive rBounds.1 (by omega) (by decide) jl, scale]
    by_cases fits : k ≤ 969
    · rw [Nat.min_eq_right fits]
      have exponent : (k : Int) + 3 = 3 + (k : Int) := by omega
      rw [exponent]
    · rw [Nat.min_eq_left (by omega : 969 ≤ k)]
      exact (packed_overflow s r ((k : Int) + 3) positive (by omega)).trans
        (packed_overflow s r (3 + ((969 : Nat) : Int)) positive (by decide)).symm

end RootNativeFloat.NativeScale
