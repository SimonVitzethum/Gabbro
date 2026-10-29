/- Signed integer keys for binary64 words; both zero encodings map to zero. -/
import Stage0.Senke.Ausdruck.Gleit.Ordnung

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gabbro.Grammatik.Gleitkomma Runner.IR

theorem floatMag_lt {a : GFloat} (ha : wf f64 a) : floatMag a < 2 ^ 63 := by
  have he : a.bexp ≤ 2047 := ha.1
  have hf : a.frac < 4503599627370496 := ha.2
  unfold floatMag
  omega

theorem float_bits {a : GFloat} :
    zuBits f64 a = (if a.sign then 2 ^ 63 else 0) + floatMag a := by
  change (if a.sign then 2 ^ 63 else 0) + a.bexp * 4503599627370496 + a.frac =
    (if a.sign then 2 ^ 63 else 0) + (a.bexp * 4503599627370496 + a.frac)
  omega

theorem float_raw_sign {a : GFloat} (ha : wf f64 a) :
    (BitVec.ofNat 64 (zuBits f64 a)).slt 0 = a.sign := by
  have hm := floatMag_lt ha
  rw [BitVec.slt_eq_decide, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, float_bits]
  change decide ((if 2 * (((if a.sign then 2 ^ 63 else 0) + floatMag a) % 2^64) < 2^64
    then ((((if a.sign then 2 ^ 63 else 0) + floatMag a) % 2^64 : Nat) : Int)
    else (((((if a.sign then 2 ^ 63 else 0) + floatMag a) % 2^64 : Nat) : Int) - 2^64)) < 0) = a.sign
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  cases a.sign <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  all_goals split <;> simp_all <;> omega

theorem float_raw_mag {a : GFloat} (ha : wf f64 a) :
    ((BitVec.ofNat 64 (zuBits f64 a) <<< 1) >>> 1) = BitVec.ofNat 64 (floatMag a) := by
  have hm := floatMag_lt ha
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, float_bits]
  cases a.sign <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] <;> omega

theorem float_key_algebra (n : Nat) (s : Bool) :
    BitVec.ofNat 64 n * (1 - 2 * Runner.IR.bool s) =
      BitVec.ofInt 64 (if s then -(n : Int) else n) := by
  cases s
  · have hc : (1 - 2 * Runner.IR.bool false : Runner.W) = 1 := by decide
    rw [hc]
    exact (BitVec.mul_one _).trans (BitVec.ofInt_natCast _ _).symm
  · have hc : (1 - 2 * Runner.IR.bool true : Runner.W) = -(1#64) := by decide
    rw [hc]
    calc
      _ = -(BitVec.ofNat 64 n * (1#64)) := BitVec.mul_neg _ _
      _ = -(BitVec.ofNat 64 n) := congrArg Neg.neg (BitVec.mul_one _)
      _ = BitVec.ofInt 64 (if true then -(n : Int) else n) := by
        rw [show (if true then -(n : Int) else n) = -(n : Int) from rfl,
          BitVec.ofInt_neg, BitVec.ofInt_natCast]

/-- Removing the sign bit and applying its sign yields a signed, zero-normalised key. -/
theorem float_key_word {a : GFloat} (ha : wf f64 a) :
    ((BitVec.ofNat 64 (zuBits f64 a) <<< 1) >>> 1) *
      (1 - 2 * Runner.IR.bool ((BitVec.ofNat 64 (zuBits f64 a)).slt 0)) =
        BitVec.ofInt 64 (floatKey a) := by
  rw [float_raw_mag ha, float_raw_sign ha]
  exact float_key_algebra _ _

theorem float_key_range {a : GFloat} (ha : wf f64 a) :
    -2 ^ 63 ≤ floatKey a ∧ floatKey a < 2 ^ 63 := by
  have hm := floatMag_lt ha
  unfold floatKey
  cases a.sign <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

end Gabbro.Stage0.Senke
