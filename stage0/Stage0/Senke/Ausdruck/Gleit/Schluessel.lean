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

end Gabbro.Stage0.Senke
