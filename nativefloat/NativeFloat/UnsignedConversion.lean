/- Native correspondence for the portable high-half UInt64 request sequence. -/
module
public import NativeFloat.UnsignedCore
public import Init.Data.SInt.Float
public import Init.Data.SInt.Float32
import all NativeFloat.UnsignedCore
import all NativeFloat.IntSticky
import all Init.Data.SInt.Float
import all Init.Data.SInt.Float32
@[expose] public section

namespace RootNativeFloat
open Float.Model
open Float.Model.UnpackedFloat

private theorem jam_more (n k extra : Nat) :
    let g := (n >>> k) ||| (if n % 2 ^ k = 0 then 0 else 1)
    (⟨g, false, false⟩ : ExtendedMantissa) >>> (3 + extra) =
      (⟨n, false, false⟩ : ExtendedMantissa) >>> ((k + 3) + extra) := by
  dsimp only
  induction extra with
  | zero => exact jam56_shift n k
  | succ extra ih =>
    change ExtendedMantissa.shiftRightOne
        ((⟨(n >>> k) ||| (if n % 2 ^ k = 0 then 0 else 1), false, false⟩ : ExtendedMantissa) >>>
          (3 + extra)) =
      ExtendedMantissa.shiftRightOne ((⟨n, false, false⟩ : ExtendedMantissa) >>> ((k + 3) + extra))
    exact congrArg ExtendedMantissa.shiftRightOne ih

private theorem high_half (word : BitVec 64) (high : word.msb = true) :
    let half := (word >>> 1) ||| (word &&& 1)
    2 ^ 63 ≤ word.toNat ∧ 2 ^ 62 ≤ half.toNat ∧ half.toNat < 2 ^ 63 ∧ half.msb = false ∧
      half.toNat = (word.toNat >>> 1) ||| (if word.toNat % 2 ^ 1 = 0 then 0 else 1) := by
  dsimp only
  let half := (word >>> 1) ||| (word &&& 1)
  have lower : 2 ^ 63 ≤ word.toNat := BitVec.le_toNat_of_msb_true high
  have upper : word.toNat < 2 ^ 64 := word.isLt
  have value : half.toNat = (word.toNat >>> 1) ||| (word.toNat % 2) := by
    simp only [half, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_and,
      BitVec.toNat_one (by decide : 0 < 64), Nat.and_one_is_mod]
  have quotientLower : 2 ^ 62 ≤ word.toNat >>> 1 := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have quotientUpper : word.toNat >>> 1 < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have halfLower : 2 ^ 62 ≤ half.toNat := by
    rw [value]
    exact Nat.le_trans quotientLower Nat.left_le_or
  have halfUpper : half.toNat < 2 ^ 63 := by
    rw [value]
    exact Nat.or_lt_two_pow quotientUpper (by have := Nat.mod_lt word.toNat (by decide : 0 < 2); omega)
  have msb : half.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by omega)
  refine ⟨lower, halfLower, halfUpper, msb, ?_⟩
  rw [value]
  have bit : (if word.toNat % 2 ^ 1 = 0 then 0 else 1) = word.toNat % 2 := by
    have := Nat.mod_lt word.toNat (by decide : 0 < 2)
    simp only [Nat.pow_one]
    split <;> omega
  rw [bit]

private theorem positive_integer (F : Format) (n : Nat) (positive : 0 < n) :
    UnpackedFloat.ofInt F (n : Int) = round F .positive n 0 := by
  have comparison : compare (n : Int) 0 = .gt := Int.compare_eq_gt.mpr (by omega)
  simp only [UnpackedFloat.ofInt, normalize, comparison, Int.toNat_natCast]

private theorem high_pack (F : Format) (standard : F = .binary32 ∨ F = .binary64)
    (word : BitVec 64) (high : word.msb = true) :
    let half := (word >>> 1) ||| (word &&& 1)
    UnpackedFloat.pack F (UnpackedFloat.ofUInt64 F (UInt64.ofBitVec word)) =
      UnpackedFloat.pack F (UnpackedFloat.add F
        (UnpackedFloat.unpack F (UnpackedFloat.pack F (UnpackedFloat.ofInt64 F (Int64.ofBitVec half))))
        (UnpackedFloat.unpack F (UnpackedFloat.pack F (UnpackedFloat.ofInt64 F (Int64.ofBitVec half))))) := by
  dsimp only
  let half := (word >>> 1) ||| (word &&& 1)
  have facts := high_half word high
  have npositive : 0 < word.toNat := Nat.lt_of_lt_of_le (Nat.two_pow_pos 63) facts.1
  have tpositive : 0 < half.toNat := Nat.lt_of_lt_of_le (Nat.two_pow_pos 62) facts.2.1
  have nlog : word.toNat.log2 = 63 :=
    (Nat.log2_eq_iff (Nat.ne_of_gt npositive)).mpr ⟨facts.1, word.isLt⟩
  have tlog : half.toNat.log2 = 62 :=
    (Nat.log2_eq_iff (Nat.ne_of_gt tpositive)).mpr ⟨facts.2.1, facts.2.2.1⟩
  let j := 62 - F.mantissaBitsWithoutImplicit
  have jlower : 3 ≤ j := by rcases standard with rfl | rfl <;> decide
  have states : (⟨half.toNat, false, false⟩ : ExtendedMantissa) >>> j =
      (⟨word.toNat, false, false⟩ : ExtendedMantissa) >>> (j + 1) := by
    have kept := jam_more word.toNat 1 (j - 3)
    dsimp only at kept
    have left : 3 + (j - 3) = j := by omega
    have right : (1 + 3) + (j - 3) = j + 1 := by omega
    rw [← facts.2.2.2.2, left, right] at kept
    exact kept
  change UnpackedFloat.pack F (UnpackedFloat.ofInt F (word.toNat : Int)) =
    UnpackedFloat.pack F (UnpackedFloat.add F
      (UnpackedFloat.unpack F (UnpackedFloat.pack F (UnpackedFloat.ofInt F half.toInt)))
      (UnpackedFloat.unpack F (UnpackedFloat.pack F (UnpackedFloat.ofInt F half.toInt))))
  rw [BitVec.toInt_eq_toNat_of_msb facts.2.2.2.1,
    positive_integer F word.toNat npositive, positive_integer F half.toNat tpositive]
  exact UnsignedCore.double_pack F standard word.toNat half.toNat npositive tpositive nlog tlog states

/-- The high-half portable sequence retains a sticky low bit before the
    signed native conversion, then doubles with one native addition. -/
theorem uint64_toFloat_high (word : BitVec 64) (high : word.msb = true) :
    let half := (word >>> 1) ||| (word &&& 1)
    (UInt64.ofBitVec word).toFloat =
      Float.add (Int64.ofBitVec half).toFloat (Int64.ofBitVec half).toFloat := by
  dsimp only
  unfold Int64.toFloat Float.Model.ofInt64
  change Float.ofModel (Float.Model.pack (UnpackedFloat.ofUInt64 Format.binary64 (UInt64.ofBitVec word))) =
    Float.ofModel (Float.Model.pack (UnpackedFloat.add Format.binary64
      (UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64
        (UnpackedFloat.ofInt64 Format.binary64 (Int64.ofBitVec ((word >>> 1) ||| (word &&& 1))))))
      (UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64
        (UnpackedFloat.ofInt64 Format.binary64 (Int64.ofBitVec ((word >>> 1) ||| (word &&& 1))))))))
  apply congrArg Float.ofModel
  unfold Float.Model.pack
  congr 1
  exact congrArg UInt64.ofBitVec (high_pack Format.binary64 (Or.inr rfl) word high)

/-- The same portable sequence is rounded directly by the native binary32
    conversion and addition, without an intermediate binary64 conversion. -/
theorem uint64_toFloat32_high (word : BitVec 64) (high : word.msb = true) :
    let half := (word >>> 1) ||| (word &&& 1)
    (UInt64.ofBitVec word).toFloat32 =
      Float32.add (Int64.ofBitVec half).toFloat32 (Int64.ofBitVec half).toFloat32 := by
  dsimp only
  unfold Int64.toFloat32 Float32.Model.ofInt64
  change Float32.ofModel (Float32.Model.pack (UnpackedFloat.ofUInt64 Format.binary32 (UInt64.ofBitVec word))) =
    Float32.ofModel (Float32.Model.pack (UnpackedFloat.add Format.binary32
      (UnpackedFloat.unpack Format.binary32 (UnpackedFloat.pack Format.binary32
        (UnpackedFloat.ofInt64 Format.binary32 (Int64.ofBitVec ((word >>> 1) ||| (word &&& 1))))))
      (UnpackedFloat.unpack Format.binary32 (UnpackedFloat.pack Format.binary32
        (UnpackedFloat.ofInt64 Format.binary32 (Int64.ofBitVec ((word >>> 1) ||| (word &&& 1))))))))
  apply congrArg Float32.ofModel
  unfold Float32.Model.pack
  congr 1
  exact congrArg UInt32.ofBitVec (high_pack Format.binary32 (Or.inl rfl) word high)

end RootNativeFloat
