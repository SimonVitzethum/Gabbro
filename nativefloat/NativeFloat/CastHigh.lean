/- Exact native subtraction in the upper unsigned 64-bit cast interval. -/
module
public import NativeFloat.CastBounds
import all NativeFloat.CastCore
import all NativeFloat.CastDecode
import all NativeFloat.NormalForm
import all NativeFloat.Transport
@[expose] public section

namespace RootNativeFloat.CastHigh
open Float.Model
open Float.Model.UnpackedFloat
open CastCore CastDecode

private theorem bias_unpacked (F : Format) (standard : F = .binary32 ∨ F = .binary64) :
    UnpackedFloat.unpack F (limitBits F 63) =
      .finite .positive (2 ^ F.mantissaBitsWithoutImplicit)
        (63 - (F.mantissaBitsWithoutImplicit : Int)) (Nat.two_pow_pos _) := by
  have fits : 0 < F.exponentBias + 63 ∧ F.exponentBias + 63 < 2 ^ F.exponentBits - 1 := by
    rcases standard with rfl | rfl <;> decide
  have field : (BitVec.ofNat F.exponentBits (F.exponentBias + 63)).toNat = F.exponentBias + 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have nonzero : BitVec.ofNat F.exponentBits (F.exponentBias + 63) ≠ 0#_ := by
    intro eq
    have := congrArg BitVec.toNat eq
    simp only [field, BitVec.toNat_zero] at this
    omega
  have notMax : BitVec.ofNat F.exponentBits (F.exponentBias + 63) ≠ -1#_ := by
    intro eq
    have := congrArg BitVec.toNat eq
    simp only [field, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at this
    omega
  have exponent : ((F.exponentBias + 63 : Nat) : Int) -
      ((F.exponentBias : Int) + (F.mantissaBitsWithoutImplicit : Int)) =
        63 - (F.mantissaBitsWithoutImplicit : Int) := by omega
  simp only [limitBits, UnpackedFloat.unpack, unpackMantissa_packComponents,
    unpackExponent_packComponents, unpack_sign_components, sign_unbits,
    nonzero, notMax, ↓reduceIte, field, leading_mantissa, BitVec.toNat_zero, Nat.add_zero, exponent]

private theorem high_cases (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (word : BitVec F.numBits) {P : UnpackedFloat → Prop}
    (finite : ∀ m, m < 2 ^ F.mantissaBitsWithoutImplicit →
      P (.finite .positive (2 ^ F.mantissaBitsWithoutImplicit + m)
        (63 - (F.mantissaBitsWithoutImplicit : Int)) (by have := Nat.two_pow_pos F.mantissaBitsWithoutImplicit; omega)))
    (nonnegative : word.msb = false)
    (lower : (word &&& magnitudeMask F).ult (limitBits F 63) = false)
    (upper : (word &&& magnitudeMask F).ult (limitBits F 64) = true) :
    P (UnpackedFloat.unpack F word) := by
  apply with_fields F word (P := fun word =>
    word.msb = false → (word &&& magnitudeMask F).ult (limitBits F 63) = false →
      (word &&& magnitudeMask F).ult (limitBits F 64) = true → P (UnpackedFloat.unpack F word))
    ?_ nonnegative lower upper
  intro s e m sign lo hi
  rw [sign_fields] at sign
  cases s
  · cases sign
  · rw [range_guard F standard _ _ _ 63 (by decide)] at lo
    rw [range_guard F standard _ _ _ 64 (by decide)] at hi
    have below := of_decide_eq_true hi
    have above := of_decide_eq_false lo
    have field : e.toNat = F.exponentBias + 63 := by omega
    have nonzero : e ≠ 0#_ := by
      intro eq
      have := congrArg BitVec.toNat eq
      simp only [field, BitVec.toNat_zero] at this
      omega
    have notMax : e ≠ -1#_ := by
      intro eq
      have := congrArg BitVec.toNat eq
      simp only [field, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at this
      rcases standard with rfl | rfl <;> dsimp [Format.exponentBias] at * <;> omega
    have exponent : (e.toNat : Int) - ((F.exponentBias : Int) + (F.mantissaBitsWithoutImplicit : Int)) =
        63 - (F.mantissaBitsWithoutImplicit : Int) := by rw [field]; omega
    simpa only [UnpackedFloat.unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
      unpack_sign_components, sign_unbits, notMax, nonzero, ↓reduceIte, leading_mantissa, exponent]
      using finite m.toNat m.isLt

private theorem subtract_bias (F : Format) (m : Nat) :
    UnpackedFloat.sub F
      (.finite .positive (2 ^ F.mantissaBitsWithoutImplicit + m)
        (63 - (F.mantissaBitsWithoutImplicit : Int)) (by have := Nat.two_pow_pos F.mantissaBitsWithoutImplicit; omega))
      (.finite .positive (2 ^ F.mantissaBitsWithoutImplicit)
        (63 - (F.mantissaBitsWithoutImplicit : Int)) (Nat.two_pow_pos _)) =
      if h : m = 0 then .zero .positive else
        round F .positive m (63 - (F.mantissaBitsWithoutImplicit : Int)) := by
  simp only [UnpackedFloat.sub, Int.min_self, decreaseExponent, Int.sub_self, Int.toNat_zero,
    Nat.shiftLeft_zero, Int.natCast_zero, Int.sub_zero, Sign.apply]
  have difference : ((2 ^ F.mantissaBitsWithoutImplicit + m : Nat) : Int) -
      (2 ^ F.mantissaBitsWithoutImplicit : Nat) = (m : Int) := by omega
  rw [difference]
  by_cases zero : m = 0
  · rw [dif_pos zero, zero]
    rfl
  · have comparison : compare (m : Int) 0 = .gt := Int.compare_eq_gt.mpr (by omega)
    simp only [normalize, comparison, Int.toNat_natCast, zero, ↓reduceDIte]

private theorem reduced_round (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (m : Nat) (positive : 0 < m) (upper : m < 2 ^ F.mantissaBitsWithoutImplicit) :
    let padding := F.mantissaBitsWithoutImplicit - m.log2
    let k := 63 - F.mantissaBitsWithoutImplicit
    UnpackedFloat.unpack F (UnpackedFloat.pack F (round F .positive m (k : Int))) =
      .finite .positive (m <<< padding) ((k : Int) - padding)
        (by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos positive (Nat.two_pow_pos _)) := by
  dsimp only
  let p := F.mantissaBitsWithoutImplicit
  let padding := p - m.log2
  let k := 63 - p
  have log : m.log2 < p := (Nat.log2_lt (Nat.ne_of_gt positive)).mpr upper
  have magnitude := (Nat.log2_eq_iff (Nat.ne_of_gt positive)).mp (Eq.refl m.log2)
  have length : m.log2 + padding = p := by dsimp [padding]; omega
  have normLower : 2 ^ p ≤ m <<< padding := by
    have multiplied := Nat.mul_le_mul_right (2 ^ padding) magnitude.1
    rw [← Nat.pow_add, length] at multiplied
    simpa only [Nat.shiftLeft_eq] using multiplied
  have normUpper : m <<< padding < 2 ^ (p + 1) := by
    have multiplied := Nat.mul_lt_mul_of_pos_right magnitude.2 (Nat.two_pow_pos padding)
    rw [← Nat.pow_add] at multiplied
    have exponent : m.log2 + 1 + padding = p + 1 := by omega
    simpa only [exponent, Nat.shiftLeft_eq] using multiplied
  have normPositive : 0 < m <<< padding := by
    rw [Nat.shiftLeft_eq]
    exact Nat.mul_pos positive (Nat.two_pow_pos padding)
  have minBound : F.minExponent ≤ (k : Int) - padding := by
    rcases standard with rfl | rfl <;>
      dsimp [p, padding, k, Format.minExponent, Format.mantissaBits] at * <;> omega
  have target : F.targetExponent (totalExponent m (k : Int)) = (k : Int) - padding := by
    change max ((m.log2 : Int) + 1 + k - (1 + (p : Int))) F.minExponent = (k : Int) - padding
    have aligned : (m.log2 : Int) + 1 + k - (1 + (p : Int)) = (k : Int) - padding := by omega
    rw [aligned]
    exact Int.max_eq_left minBound
  have total : totalExponent (m <<< padding) ((k : Int) - padding) = totalExponent m (k : Int) := by
    unfold totalExponent
    rw [shifted_log m padding (Nat.ne_of_gt positive)]
    simp only [Int.natCast_add]
    omega
  have normTarget : F.targetExponent (totalExponent (m <<< padding) ((k : Int) - padding)) =
      (k : Int) - padding := by rw [total, target]
  have rounded : round F .positive m (k : Int) =
      .finite .positive (m <<< padding) ((k : Int) - padding) normPositive := by
    unfold round decreaseExponent
    rw [target]
    dsimp only
    have amount : ((k : Int) - ((k : Int) - padding)).toNat = padding := by omega
    rw [amount]
    exact exact_at_target F .positive _ _ normPositive normTarget
  rw [rounded]
  apply normal_unpack F .positive _ _ normPositive normLower normUpper
  · rcases standard with rfl | rfl <;> dsimp [p, padding, k, Format.exponentBias] at * <;> omega
  · rcases standard with rfl | rfl <;> dsimp [p, padding, k, Format.exponentBias] at * <;> omega

private theorem residual_post (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (m : Nat) (upper : m < 2 ^ F.mantissaBitsWithoutImplicit) :
    let reduced := UnpackedFloat.unpack F (UnpackedFloat.pack F (UnpackedFloat.sub F
      (.finite .positive (2 ^ F.mantissaBitsWithoutImplicit + m)
        (63 - (F.mantissaBitsWithoutImplicit : Int)) (by have := Nat.two_pow_pos F.mantissaBitsWithoutImplicit; omega))
      (.finite .positive (2 ^ F.mantissaBitsWithoutImplicit)
        (63 - (F.mantissaBitsWithoutImplicit : Int)) (Nat.two_pow_pos _))))
    Domain F reduced ∧ reduced.toInt64.toBitVec = BitVec.ofNat 64 (m <<< (63 - F.mantissaBitsWithoutImplicit)) := by
  dsimp only
  rw [subtract_bias]
  by_cases zero : m = 0
  · rw [dif_pos zero]
    have decoded : UnpackedFloat.unpack F (UnpackedFloat.pack F (.zero .positive)) = .zero .positive := by
      rcases standard with rfl | rfl <;> rfl
    rw [decoded]
    refine ⟨cvtt_zero F .positive, ?_⟩
    simp only [zero, Nat.zero_shiftLeft]
    rfl
  · rw [dif_neg zero]
    let p := F.mantissaBitsWithoutImplicit
    let k := 63 - p
    let padding := p - m.log2
    have positive : 0 < m := by omega
    have room : p < 63 := by rcases standard with rfl | rfl <;> decide
    have exponent : (k : Int) = 63 - (p : Int) := by dsimp [k]; omega
    have log : m.log2 < p := (Nat.log2_lt (Nat.ne_of_gt positive)).mpr upper
    have normPositive : 0 < m <<< padding := by
      rw [Nat.shiftLeft_eq]
      exact Nat.mul_pos positive (Nat.two_pow_pos padding)
    have formed : UnpackedFloat.unpack F (UnpackedFloat.pack F
        (round F .positive m (63 - (F.mantissaBitsWithoutImplicit : Int)))) =
        .finite .positive (m <<< padding) ((k : Int) - padding) normPositive := by
      have aligned : round F .positive m (63 - (F.mantissaBitsWithoutImplicit : Int)) =
          round F .positive m (k : Int) := congrArg (round F .positive m) exponent.symm
      exact (congrArg (fun value : UnpackedFloat => UnpackedFloat.unpack F (UnpackedFloat.pack F value))
        aligned).trans (reduced_round F standard m positive upper)
    rw [formed]
    change Domain F (.finite .positive (m <<< padding) ((k : Int) - padding) normPositive) ∧
      (UnpackedFloat.finite .positive (m <<< padding) ((k : Int) - padding) normPositive).toInt64.toBitVec =
        BitVec.ofNat 64 (m <<< k)
    have normExponent : (k : Int) - padding < 63 - (F.mantissaBitsWithoutImplicit : Int) := by
      change (k : Int) - padding < 63 - (p : Int)
      rw [← exponent]
      have padPositive : 0 < padding := by dsimp [padding]; omega
      omega
    refine ⟨cvtt_small F .positive (m <<< padding) ((k : Int) - padding) normPositive normExponent, ?_⟩
    have small : m <<< k < 2 ^ 63 := by
      have bound : m * 2 ^ k < 2 ^ p * 2 ^ k :=
        Nat.mul_lt_mul_of_pos_right (show m < 2 ^ p from upper) (Nat.two_pow_pos k)
      have power : 2 ^ p * 2 ^ k = 2 ^ 63 := by
        rw [← Nat.pow_add]
        congr 1
        dsimp [k]
        omega
      rw [power] at bound
      simpa only [Nat.shiftLeft_eq] using bound
    let n := m <<< k
    have smallN : n < 2 ^ 63 := small
    have value : roundToInt .positive (m <<< padding) ((k : Int) - padding) = (n : Int) := by
      simpa only [Sign.apply] using truncation_scaled .positive m padding k
    change (Int64.ofIntClamp (roundToInt .positive (m <<< padding) ((k : Int) - padding))).toBitVec =
      BitVec.ofNat 64 n
    rw [value]
    have intSmall : (n : Int) < 2 ^ 63 := by
      simpa only [Int.natCast_pow, Int.cast_ofNat_Int] using (Int.ofNat_lt.mpr smallN)
    have minNonpositive : -(2 ^ 63 : Int) ≤ 0 :=
      Int.neg_nonpos_of_nonneg (Int.pow_nonneg (by decide : (0 : Int) ≤ 2))
    have intLower : -(2 ^ 63 : Int) ≤ n := Int.le_trans minNonpositive (Int.natCast_nonneg n)
    rw [clamp_signed (n : Int) intLower intSmall]
    change BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n
    exact BitVec.ofInt_natCast 64 n

private theorem high_result (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (m : Nat) (upper : m < 2 ^ F.mantissaBitsWithoutImplicit) :
    let x := UnpackedFloat.finite .positive (2 ^ F.mantissaBitsWithoutImplicit + m)
      (63 - (F.mantissaBitsWithoutImplicit : Int)) (by have := Nat.two_pow_pos F.mantissaBitsWithoutImplicit; omega)
    let reduced := UnpackedFloat.unpack F (UnpackedFloat.pack F (UnpackedFloat.sub F x
      (.finite .positive (2 ^ F.mantissaBitsWithoutImplicit)
        (63 - (F.mantissaBitsWithoutImplicit : Int)) (Nat.two_pow_pos _))))
    x.toUInt64.toBitVec = reduced.toInt64.toBitVec ||| 0x8000000000000000 ∧ Domain F reduced := by
  dsimp only
  have post := residual_post F standard m upper
  dsimp only at post
  refine ⟨?_, post.1⟩
  rw [post.2]
  let p := F.mantissaBitsWithoutImplicit
  let k := 63 - p
  have room : p < 63 := by rcases standard with rfl | rfl <;> decide
  have exponent : 63 - (p : Int) = (k : Int) := by dsimp [k]; omega
  have power : 2 ^ p * 2 ^ k = 2 ^ 63 := by
    rw [← Nat.pow_add]
    congr 1
    dsimp [k]
    omega
  have small : m <<< k < 2 ^ 63 := by
    have bound : m * 2 ^ k < 2 ^ p * 2 ^ k :=
      Nat.mul_lt_mul_of_pos_right (show m < 2 ^ p from upper) (Nat.two_pow_pos k)
    rw [power] at bound
    simpa only [Nat.shiftLeft_eq] using bound
  have value : (2 ^ p + m) <<< k = 2 ^ 63 + (m <<< k) := by
    simp only [Nat.shiftLeft_eq, Nat.add_mul, power]
  let n := m <<< k
  have smallN : n < 2 ^ 63 := small
  have wholeValue : roundToInt .positive (2 ^ p + m) (63 - (p : Int)) = ((2 ^ 63 + n : Nat) : Int) := by
    rw [exponent]
    simp only [truncation_nat, Sign.apply, Int.natCast_nonneg k, ↓reduceIte,
      Int.toNat_natCast, value]
    rfl
  change (UInt64.ofNatClamp (roundToInt .positive (2 ^ p + m) (63 - (p : Int))).toNat).toBitVec =
    BitVec.ofNat 64 n ||| 0x8000000000000000
  rw [wholeValue]
  simp only [Int.toNat_natCast]
  have wholeBound : 2 ^ 63 + n < UInt64.size := by change 2 ^ 63 + n < 2 ^ 64; omega
  rw [UInt64.ofNatClamp_eq_ofNat (2 ^ 63 + n) wholeBound]
  change BitVec.ofNat 64 (2 ^ 63 + n) = BitVec.ofNat 64 n ||| BitVec.ofNat 64 (2 ^ 63)
  rw [← BitVec.ofNat_or, Nat.or_two_pow_eq_add_of_lt smallN]
  exact congrArg (BitVec.ofNat 64) (Nat.add_comm (2 ^ 63) n)

private theorem decoded_high (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (word : BitVec F.numBits) (nonnegative : word.msb = false)
    (lower : (word &&& magnitudeMask F).ult (limitBits F 63) = false)
    (upper : (word &&& magnitudeMask F).ult (limitBits F 64) = true) :
    let reduced := UnpackedFloat.unpack F (UnpackedFloat.pack F
      (UnpackedFloat.sub F (UnpackedFloat.unpack F word) (UnpackedFloat.unpack F (limitBits F 63))))
    (UnpackedFloat.unpack F word).toUInt64.toBitVec = reduced.toInt64.toBitVec ||| 0x8000000000000000 ∧
      Domain F reduced := by
  dsimp only
  rw [bias_unpacked F standard]
  apply high_cases F standard word
    (P := fun value : UnpackedFloat =>
      let reduced := UnpackedFloat.unpack F (UnpackedFloat.pack F (UnpackedFloat.sub F value
        (.finite .positive (2 ^ F.mantissaBitsWithoutImplicit)
          (63 - (F.mantissaBitsWithoutImplicit : Int)) (Nat.two_pow_pos _))))
      value.toUInt64.toBitVec = reduced.toInt64.toBitVec ||| 0x8000000000000000 ∧ Domain F reduced)
  · intro m bound
    exact high_result F standard m bound
  · exact nonnegative
  · exact lower
  · exact upper

end RootNativeFloat.CastHigh
