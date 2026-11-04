/- Integer facts at Std's native floating cast boundary. -/
module
public import NativeFloat.NormalForm
public import NativeFloat.IntSticky
public import Init.Data.SInt.Float
public import Init.Data.SInt.Float32
import all NativeFloat.NormalForm
import all NativeFloat.IntSticky
import Init.Data.SInt.Lemmas
import Init.Data.UInt.Lemmas
@[expose] public section

namespace RootNativeFloat.CastCore
open Float.Model
open Float.Model.UnpackedFloat

private theorem shifted_mantissa (m k : Nat) :
    ((⟨m, false, false⟩ : ExtendedMantissa) >>> k).mantissa = m / 2 ^ k := by
  cases k with
  | zero =>
    change m = m / 2 ^ 0
    simp only [Nat.pow_zero, Nat.div_one]
  | succ k => exact congrArg ExtendedMantissa.mantissa (exact_shift_bits m k)

private theorem truncation_nat (s : Sign) (m : Nat) (e : Int) :
    roundToInt s m e = s.apply
      ((if 0 ≤ e then m <<< e.toNat else m / 2 ^ (-e).toNat : Nat) : Int) := by
  by_cases nonnegative : 0 ≤ e
  · rw [if_pos nonnegative]
    have decreased : decreaseExponent m e 0 = (m <<< e.toNat, 0) := by
      unfold decreaseExponent
      dsimp only
      simp only [Int.sub_zero]
      apply Prod.ext
      · rfl
      · omega
    unfold roundToInt
    rw [decreased]
    rfl
  · rw [if_neg nonnegative]
    have decreased : decreaseExponent m e 0 = (m, e) := by
      unfold decreaseExponent
      dsimp only
      have amount : (e - 0).toNat = 0 := by omega
      rw [amount]
      simp only [Nat.shiftLeft_zero, Int.natCast_zero, Int.sub_zero]
    unfold roundToInt
    rw [decreased]
    dsimp only
    unfold shiftToExponent
    dsimp only
    simp only [Int.zero_sub, ExtendedMantissa.ofMantissaAndAccuracy]
    rw [shifted_mantissa]

private theorem truncation (s : Sign) (m : Nat) (e : Int) :
    roundToInt s m e = s.apply
      (if 0 ≤ e then (m <<< e.toNat : Nat) else m / 2 ^ (-e).toNat) := by
  rw [truncation_nat]
  by_cases nonnegative : 0 ≤ e
  · simp only [nonnegative, ↓reduceIte]
  · simp only [nonnegative, ↓reduceIte, Int.natCast_ediv, Int.natCast_pow, Int.cast_ofNat_Int]

private theorem truncation_scaled (s : Sign) (m padding e : Nat) :
    roundToInt s (m <<< padding) ((e : Int) - padding) = s.apply (m <<< e : Nat) := by
  rw [truncation_nat]
  by_cases enough : padding ≤ e
  · rw [if_pos (by omega)]
    have amount : ((e : Int) - padding).toNat = e - padding := by omega
    rw [amount, ← Nat.shiftLeft_add]
    have total : padding + (e - padding) = e := by omega
    rw [total]
  · rw [if_neg (by omega)]
    have amount : (-((e : Int) - padding)).toNat = padding - e := by omega
    have shifted : m <<< padding = (m <<< e) <<< (padding - e) := by
      rw [← Nat.shiftLeft_add]
      congr 1
      omega
    rw [amount, shifted, Nat.shiftLeft_eq, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

private theorem magnitude_small (p m : Nat) (e : Int) (room : p < 63)
    (mantissa : m < 2 ^ (p + 1)) (exponent : e < 63 - (p : Int)) :
    (if 0 ≤ e then m <<< e.toNat else m / 2 ^ (-e).toNat) < 2 ^ 63 := by
  by_cases nonnegative : 0 ≤ e
  · rw [if_pos nonnegative, Nat.shiftLeft_eq]
    have amount : p + 1 + e.toNat ≤ 63 := by omega
    have top := Nat.mul_lt_mul_of_pos_right mantissa (Nat.two_pow_pos e.toNat)
    have power : 2 ^ (p + 1) * 2 ^ e.toNat = 2 ^ (p + 1 + e.toNat) := (Nat.pow_add ..).symm
    rw [power] at top
    exact Nat.lt_of_lt_of_le top (Nat.pow_le_pow_right (by decide : 0 < 2) amount)
  · rw [if_neg nonnegative]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_of_lt_of_le mantissa
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : p + 1 ≤ 63)))

private theorem magnitude_large (p b m : Nat) (e : Int) (room : p ≤ b)
    (mantissa : 2 ^ p ≤ m) (exponent : (b : Int) - p ≤ e) :
    2 ^ b ≤ (if 0 ≤ e then m <<< e.toNat else m / 2 ^ (-e).toNat) := by
  have nonnegative : 0 ≤ e := by omega
  rw [if_pos nonnegative, Nat.shiftLeft_eq]
  have power : 2 ^ b ≤ 2 ^ (p + e.toNat) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  rw [Nat.pow_add] at power
  exact Nat.le_trans power (Nat.mul_le_mul_right (2 ^ e.toNat) mantissa)

private theorem clamp_signed (v : Int) (lo : -(2 ^ 63) ≤ v) (hi : v < 2 ^ 63) :
    Int64.ofIntClamp v = Int64.ofInt v := by
  exact (Int64.ofIntLE_eq_ofIntClamp (h₁ := by change -(2 ^ 63) ≤ v; exact lo)
    (h₂ := by change v ≤ 2 ^ 63 - 1; omega)).symm

private theorem clamp_positive (v : Int) (large : 2 ^ 63 ≤ v) :
    Int64.ofIntClamp v = Int64.maxValue := by
  unfold Int64.ofIntClamp
  rw [dif_pos (by change -(2 ^ 63) ≤ v; omega), dif_neg (by change ¬ v ≤ 2 ^ 63 - 1; omega)]

private theorem clamp_negative (v : Int) (large : v ≤ -(2 ^ 63)) :
    Int64.ofIntClamp v = Int64.minValue := by
  by_cases boundary : v = -(2 ^ 63)
  · rw [boundary]
    rfl
  · unfold Int64.ofIntClamp
    rw [dif_neg (by change ¬ -(2 ^ 63) ≤ v; omega)]

private theorem unsigned_of_nonpositive (v : Int) (negative : v ≤ 0) :
    UInt64.ofNatClamp v.toNat = 0 := by
  have zero : v.toNat = 0 := by omega
  rw [zero, UInt64.ofNatClamp_eq_ofNat 0 (by decide)]

private theorem positive_low (m : Nat) (e : Int) (positive : 0 < m)
    (small : (if 0 ≤ e then m <<< e.toNat else m / 2 ^ (-e).toNat) < 2 ^ 63) :
    (UnpackedFloat.finite .positive m e positive).toUInt64.toBitVec =
      (UnpackedFloat.finite .positive m e positive).toInt64.toBitVec := by
  let n : Nat := if 0 ≤ e then m <<< e.toNat else m / 2 ^ (-e).toNat
  have smallN : n < 2 ^ 63 := small
  have value : roundToInt .positive m e = (n : Int) := by
    simpa only [Sign.apply] using truncation_nat .positive m e
  change (UInt64.ofNatClamp (roundToInt .positive m e).toNat).toBitVec =
    (Int64.ofIntClamp (roundToInt .positive m e)).toBitVec
  rw [value]
  simp only [Int.toNat_natCast]
  have intSmall : (n : Int) < 2 ^ 63 := by
    simpa only [Int.natCast_pow, Int.cast_ofNat_Int] using (Int.ofNat_lt.mpr smallN)
  have minNonpositive : -(2 ^ 63 : Int) ≤ 0 :=
    Int.neg_nonpos_of_nonneg (Int.pow_nonneg (by decide : (0 : Int) ≤ 2))
  have intLower : -(2 ^ 63 : Int) ≤ n := Int.le_trans minNonpositive (Int.natCast_nonneg n)
  have unsignedBound : n < UInt64.size := Nat.lt_trans smallN (by decide)
  rw [clamp_signed (n : Int) intLower intSmall, UInt64.ofNatClamp_eq_ofNat n unsignedBound]
  change BitVec.ofNat 64 n = BitVec.ofInt 64 (n : Int)
  exact (BitVec.ofInt_natCast 64 n).symm

private theorem negative_unsigned (m : Nat) (e : Int) (positive : 0 < m) :
    (UnpackedFloat.finite .negative m e positive).toUInt64 = 0 := by
  let n : Nat := if 0 ≤ e then m <<< e.toNat else m / 2 ^ (-e).toNat
  have value : roundToInt .negative m e = -(n : Int) := by
    simpa only [Sign.apply] using truncation_nat .negative m e
  change UInt64.ofNatClamp (roundToInt .negative m e).toNat = 0
  rw [value]
  exact unsigned_of_nonpositive _ (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg n))

private theorem finite_signed_overflow (s : Sign) (m : Nat) (e : Int) (positive : 0 < m)
    (large : 2 ^ 63 ≤ (if 0 ≤ e then m <<< e.toNat else m / 2 ^ (-e).toNat)) :
    (UnpackedFloat.finite s m e positive).toInt64 =
      if s = .negative then Int64.minValue else Int64.maxValue := by
  let n : Nat := if 0 ≤ e then m <<< e.toNat else m / 2 ^ (-e).toNat
  have largeN : 2 ^ 63 ≤ n := large
  have intLarge : (2 ^ 63 : Int) ≤ n := by
    simpa only [Int.natCast_pow, Int.cast_ofNat_Int] using (Int.ofNat_le.mpr largeN)
  have value : roundToInt s m e = s.apply (n : Int) := truncation_nat s m e
  change Int64.ofIntClamp (roundToInt s m e) = _
  rw [value]
  cases s
  · change Int64.ofIntClamp (-(n : Int)) = Int64.minValue
    exact clamp_negative _ (Int.neg_le_neg intLarge)
  · change Int64.ofIntClamp (n : Int) = Int64.maxValue
    exact clamp_positive _ intLarge

private theorem finite_unsigned_overflow (m : Nat) (e : Int) (positive : 0 < m)
    (large : 2 ^ 64 ≤ (if 0 ≤ e then m <<< e.toNat else m / 2 ^ (-e).toNat)) :
    (UnpackedFloat.finite .positive m e positive).toUInt64.toBitVec = -1#64 := by
  let n : Nat := if 0 ≤ e then m <<< e.toNat else m / 2 ^ (-e).toNat
  have largeN : 2 ^ 64 ≤ n := large
  have value : roundToInt .positive m e = (n : Int) := by
    simpa only [Sign.apply] using truncation_nat .positive m e
  change BitVec.ofNatClamp 64 (roundToInt .positive m e).toNat = -1#64
  rw [value]
  simp only [Int.toNat_natCast]
  exact BitVec.ofNatClamp_eq_allOnes_of_le largeN

private theorem cvtt_small (F : Format) (s : Sign) (m : Nat) (e : Int) (positive : 0 < m)
    (exponent : e < 63 - (F.mantissaBitsWithoutImplicit : Int)) :
    (UnpackedFloat.finite s m e positive).isNaN = false ∧
      (UnpackedFloat.finite s m e positive).lt
        (.finite .negative (2 ^ F.mantissaBitsWithoutImplicit)
          (63 - (F.mantissaBitsWithoutImplicit : Int)) (Nat.two_pow_pos _)) = false ∧
      (UnpackedFloat.finite s m e positive).lt
        (.finite .positive (2 ^ F.mantissaBitsWithoutImplicit)
          (63 - (F.mantissaBitsWithoutImplicit : Int)) (Nat.two_pow_pos _)) = true := by
  have comparison : compare e (63 - (F.mantissaBitsWithoutImplicit : Int)) = .lt :=
    Int.compare_eq_lt.mpr exponent
  cases s <;> simp only [UnpackedFloat.isNaN, UnpackedFloat.lt, UnpackedFloat.compare,
    comparison, Ordering.then] <;> decide

private theorem cvtt_zero (F : Format) (s : Sign) :
    (UnpackedFloat.zero s).isNaN = false ∧
      (UnpackedFloat.zero s).lt (.finite .negative (2 ^ F.mantissaBitsWithoutImplicit)
        (63 - (F.mantissaBitsWithoutImplicit : Int)) (Nat.two_pow_pos _)) = false ∧
      (UnpackedFloat.zero s).lt (.finite .positive (2 ^ F.mantissaBitsWithoutImplicit)
        (63 - (F.mantissaBitsWithoutImplicit : Int)) (Nat.two_pow_pos _)) = true := by
  exact ⟨rfl, rfl, rfl⟩

end RootNativeFloat.CastCore
