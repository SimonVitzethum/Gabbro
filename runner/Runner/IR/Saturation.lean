module
public import Runner.IR.Seq
import NativeFloat.Saturation
@[expose] public section

namespace Runner

/-! Only representation transports live here. Numerical cast identities and
    domains come from NativeFloat.Saturation; Run still uses its original
    constructors and the original portable request trees. -/

private theorem and_extend32 (value : BitVec 32) (mask : W) :
    value.setWidth 64 &&& mask = (value &&& mask.setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro bit bound
  by_cases low : bit < 32
  · simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, bound, low,
      decide_true, Bool.true_and]
  · have zero : value.getLsbD bit = false := BitVec.getLsbD_of_ge value bit (by omega)
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, zero, Bool.and_false,
      Bool.false_and]

private theorem ult_extend32 (a b : BitVec 32) :
    (a.setWidth 64).ult (b.setWidth 64) = a.ult b := by
  simp only [BitVec.ult_eq_decide, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]

private theorem magnitude32 (value : W) :
    fpMagnitude .f32 value = ((value.setWidth 32) &&& 0x7FFFFFFF).setWidth 64 := by
  change (value.setWidth 32).setWidth 64 &&& ~~~(0x80000000 : W) = _
  rw [and_extend32]
  rfl

private theorem magnitude32_ult (value : W) (limit : BitVec 32) :
    (fpMagnitude .f32 value).ult (limit.setWidth 64) =
      ((value.setWidth 32) &&& 0x7FFFFFFF).ult limit := by
  rw [magnitude32, ult_extend32]

private theorem nan32 (value : W) :
    fpNaN .f32 value = (0x7F800000 : BitVec 32).ult ((value.setWidth 32) &&& 0x7FFFFFFF) := by
  change ((0x7F800000 : BitVec 32).setWidth 64).ult (fpMagnitude .f32 value) = _
  rw [magnitude32, ult_extend32]

private theorem negative32 (value : W) : fpNegative .f32 value = (value.setWidth 32).msb := by
  change (fpLow32 value &&& BitVec.twoPow 64 31 != 0) = _
  rw [BitVec.and_twoPow]
  simp only [fpLow32, BitVec.getLsbD_setWidth, BitVec.msb_eq_getLsbD_last]
  cases value.getLsbD 31 <;> decide

private theorem negative64 (value : W) : fpNegative .f64 value = value.msb := by
  change (value &&& BitVec.twoPow 64 63 != 0) = _
  rw [BitVec.and_twoPow, BitVec.msb_eq_getLsbD_last]
  cases value.getLsbD 63 <;> decide

private theorem truncate32_domain (value : Float32)
    (domain : value.isNaN = false ∧ Float32.lt value Int64.minValue.toFloat32 = false ∧
      Float32.lt value (UInt64.ofNat (2 ^ 63)).toFloat32 = true) :
    truncateFloat32 value = value.toInt64.toBitVec := by
  simp only [truncateFloat32, domain.1, domain.2.1, domain.2.2,
    Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]

private theorem truncate64_domain (value : Float)
    (domain : value.isNaN = false ∧ Float.lt value Int64.minValue.toFloat = false ∧
      Float.lt value (UInt64.ofNat (2 ^ 63)).toFloat = true) :
    truncateFloat64 value = value.toInt64.toBitVec := by
  simp only [truncateFloat64, domain.1, domain.2.1, domain.2.2,
    Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]

private theorem signed_result {format : FPFormat} {value result : W}
    (expected : NativeFPEval (.toInt64 format) value 0 result) :
    result = nativeFPBits (.toInt64 format) value 0 := by
  cases format <;> exact expected

private theorem unsigned_result {format : FPFormat} {value result : W}
    (expected : NativeFPEval (.toUInt64 format) value 0 result) :
    result = nativeFPBits (.toUInt64 format) value 0 := by
  cases format <;> exact expected

private theorem nan_results (format : FPFormat) (value : W) (nan : fpNaN format value = true) :
    nativeFPBits (.toInt64 format) value 0 = 0 ∧ nativeFPBits (.toUInt64 format) value 0 = 0 := by
  cases format with
  | f32 =>
    rw [nan32] at nan
    exact ⟨RootNativeFloat.float32_toInt64_nan (value.setWidth 32) nan,
      RootNativeFloat.float32_toUInt64_nan (value.setWidth 32) nan⟩
  | f64 =>
    change (0x7FF0000000000000 : W).ult (value &&& 0x7FFFFFFFFFFFFFFF) = true at nan
    exact ⟨RootNativeFloat.float64_toInt64_nan value nan,
      RootNativeFloat.float64_toUInt64_nan value nan⟩

private theorem small_truncate (format : FPFormat) (value : W)
    (small : (fpMagnitude format value).ult format.int64Limit = true) :
    NativeFPEval (.truncateInt64 format) value 0 (nativeFPBits (.toInt64 format) value 0) := by
  cases format with
  | f32 =>
    change (fpMagnitude .f32 value).ult ((0x5F000000 : BitVec 32).setWidth 64) = true at small
    rw [magnitude32_ult] at small
    exact (truncate32_domain _ (RootNativeFloat.float32_cvtt_domain (value.setWidth 32) small)).symm
  | f64 =>
    change (value &&& 0x7FFFFFFFFFFFFFFF).ult 0x43E0000000000000 = true at small
    exact (truncate64_domain _ (RootNativeFloat.float64_cvtt_domain value small)).symm

private theorem signed_overflow (format : FPFormat) (value : W)
    (nan : fpNaN format value = false)
    (large : (fpMagnitude format value).ult format.int64Limit = false) :
    nativeFPBits (.toInt64 format) value 0 =
      if fpNegative format value then 0x8000000000000000 else 0x7FFFFFFFFFFFFFFF := by
  cases format with
  | f32 =>
    rw [nan32] at nan
    change (fpMagnitude .f32 value).ult ((0x5F000000 : BitVec 32).setWidth 64) = false at large
    rw [magnitude32_ult] at large
    simpa only [negative32] using
      RootNativeFloat.float32_toInt64_overflow (value.setWidth 32) nan large
  | f64 =>
    change (0x7FF0000000000000 : W).ult (value &&& 0x7FFFFFFFFFFFFFFF) = false at nan
    change (value &&& 0x7FFFFFFFFFFFFFFF).ult 0x43E0000000000000 = false at large
    simpa only [negative64] using RootNativeFloat.float64_toInt64_overflow value nan large

private theorem unsigned_negative (format : FPFormat) (value : W)
    (negative : fpNegative format value = true) : nativeFPBits (.toUInt64 format) value 0 = 0 := by
  cases format with
  | f32 =>
    rw [negative32] at negative
    exact RootNativeFloat.float32_toUInt64_negative (value.setWidth 32) negative
  | f64 =>
    rw [negative64] at negative
    exact RootNativeFloat.float64_toUInt64_negative value negative

private theorem unsigned_low (format : FPFormat) (value : W)
    (nonnegative : fpNegative format value = false)
    (small : (fpMagnitude format value).ult format.int64Limit = true) :
    nativeFPBits (.toUInt64 format) value 0 = nativeFPBits (.toInt64 format) value 0 := by
  cases format with
  | f32 =>
    rw [negative32] at nonnegative
    change (fpMagnitude .f32 value).ult ((0x5F000000 : BitVec 32).setWidth 64) = true at small
    rw [magnitude32_ult] at small
    exact RootNativeFloat.float32_toUInt64_low (value.setWidth 32) nonnegative small
  | f64 =>
    rw [negative64] at nonnegative
    change (value &&& 0x7FFFFFFFFFFFFFFF).ult 0x43E0000000000000 = true at small
    exact RootNativeFloat.float64_toUInt64_low value nonnegative small

private theorem unsigned_overflow (format : FPFormat) (value : W)
    (nonnegative : fpNegative format value = false) (nan : fpNaN format value = false)
    (large : (fpMagnitude format value).ult format.uint64Limit = false) :
    nativeFPBits (.toUInt64 format) value 0 = 0xFFFFFFFFFFFFFFFF := by
  cases format with
  | f32 =>
    rw [negative32] at nonnegative
    rw [nan32] at nan
    change (fpMagnitude .f32 value).ult ((0x5F800000 : BitVec 32).setWidth 64) = false at large
    rw [magnitude32_ult] at large
    exact RootNativeFloat.float32_toUInt64_overflow (value.setWidth 32) nonnegative nan large
  | f64 =>
    rw [negative64] at nonnegative
    change (0x7FF0000000000000 : W).ult (value &&& 0x7FFFFFFFFFFFFFFF) = false at nan
    change (value &&& 0x7FFFFFFFFFFFFFFF).ult 0x43F0000000000000 = false at large
    exact RootNativeFloat.float64_toUInt64_overflow value nonnegative nan large

private theorem unsigned_high (format : FPFormat) (value reduced : W)
    (nonnegative : fpNegative format value = false)
    (lower : (fpMagnitude format value).ult format.int64Limit = false)
    (upper : (fpMagnitude format value).ult format.uint64Limit = true)
    (subtracted : NativeFPEval (.sub format) value format.int64Limit reduced) :
    nativeFPBits (.toUInt64 format) value 0 =
      nativeFPBits (.truncateInt64 format) reduced 0 ||| 0x8000000000000000 := by
  cases format with
  | f32 =>
    rw [negative32] at nonnegative
    change (fpMagnitude .f32 value).ult ((0x5F000000 : BitVec 32).setWidth 64) = false at lower
    change (fpMagnitude .f32 value).ult ((0x5F800000 : BitVec 32).setWidth 64) = true at upper
    rw [magnitude32_ult] at lower upper
    have post := RootNativeFloat.float32_toUInt64_high (value.setWidth 32) nonnegative lower upper
    change reduced = (reduced.setWidth 32).setWidth 64 ∧
      readFloat32 reduced = readFloat32 value - Float32.ofBits 0x5F000000 at subtracted
    change (readFloat32 value).toUInt64.toBitVec =
      truncateFloat32 (readFloat32 reduced) ||| 0x8000000000000000
    rw [subtracted.2, truncate32_domain _ post.2]
    exact post.1
  | f64 =>
    rw [negative64] at nonnegative
    change (value &&& 0x7FFFFFFFFFFFFFFF).ult 0x43E0000000000000 = false at lower
    change (value &&& 0x7FFFFFFFFFFFFFFF).ult 0x43F0000000000000 = true at upper
    have post := RootNativeFloat.float64_toUInt64_high value nonnegative lower upper
    change readFloat reduced = readFloat value - Float.ofBits 0x43E0000000000000 at subtracted
    change (readFloat value).toUInt64.toBitVec =
      truncateFloat64 (readFloat reduced) ||| 0x8000000000000000
    rw [subtracted, truncate64_domain _ post.2]
    exact post.1

namespace IR
variable [Kern]

/-- Every signed portable branch implements the original native saturation
    certificate. The only requested primitive is CVTT on its proven domain. -/
theorem Run.fp_toInt64 {format : FPFormat} {value result : W}
    {continuation : W → Res T} {m m' : Mem} {t : T}
    (heval : NativeFPEval (.toInt64 format) value 0 result)
    (hk : Run (continuation result) m t m') :
    Run (fpToInt64 format value continuation) m t m' := by
  have resultEq := signed_result heval
  cases nan : fpNaN format value with
  | true =>
    have same : result = 0 := resultEq.trans (nan_results format value nan).1
    simpa only [fpToInt64, nan, ↓reduceIte, same] using hk
  | false =>
    cases small : (fpMagnitude format value).ult format.int64Limit with
    | true =>
      have primitive : NativeFPEval (.truncateInt64 format) value 0 result := by
        rw [resultEq]
        exact small_truncate format value small
      simpa only [fpToInt64, nan, small, Bool.false_eq_true, ↓reduceIte] using
        Run.native_fp primitive hk
    | false =>
      have same := resultEq.trans (signed_overflow format value nan small)
      simpa only [fpToInt64, nan, small, Bool.false_eq_true, ↓reduceIte, same] using hk

/-- Every unsigned portable branch, including native Sub followed by CVTT and
    high-bit OR, implements the full-domain native UInt64 certificate. -/
theorem Run.fp_toUInt64 {format : FPFormat} {value result : W}
    {continuation : W → Res T} {m m' : Mem} {t : T}
    (heval : NativeFPEval (.toUInt64 format) value 0 result)
    (hk : Run (continuation result) m t m') :
    Run (fpToUInt64 format value continuation) m t m' := by
  have resultEq := unsigned_result heval
  cases nan : fpNaN format value with
  | true =>
    have same : result = 0 := resultEq.trans (nan_results format value nan).2
    simpa only [fpToUInt64, nan, Bool.true_or, ↓reduceIte, same] using hk
  | false =>
    cases negative : fpNegative format value with
    | true =>
      have same : result = 0 := resultEq.trans (unsigned_negative format value negative)
      simpa only [fpToUInt64, nan, negative, Bool.false_or, ↓reduceIte, same] using hk
    | false =>
      cases upper : (fpMagnitude format value).ult format.uint64Limit with
      | false =>
        have same := resultEq.trans (unsigned_overflow format value negative nan upper)
        simpa only [fpToUInt64, nan, negative, upper, Bool.false_or,
          Bool.false_eq_true, ↓reduceIte, same] using hk
      | true =>
        cases lower : (fpMagnitude format value).ult format.int64Limit with
        | true =>
          have same := resultEq.trans (unsigned_low format value negative lower)
          have primitive : NativeFPEval (.truncateInt64 format) value 0 result := by
            rw [same]
            exact small_truncate format value lower
          simpa only [fpToUInt64, nan, negative, upper, lower, Bool.false_or,
            Bool.false_eq_true, ↓reduceIte] using Run.native_fp primitive hk
        | false =>
          let reduced := nativeFPBits (.sub format) value format.int64Limit
          have subtracted : NativeFPEval (.sub format) value format.int64Limit reduced :=
            nativeFPBits_eval _ _ _
          let integer := nativeFPBits (.truncateInt64 format) reduced 0
          have truncated : NativeFPEval (.truncateInt64 format) reduced 0 integer :=
            nativeFPBits_eval _ _ _
          have same : result = integer ||| 0x8000000000000000 :=
            resultEq.trans (unsigned_high format value reduced negative lower upper subtracted)
          have finish : Run (continuation (integer ||| 0x8000000000000000)) m t m' := by
            simpa only [same] using hk
          have afterSub : Run (Runner.fp (.truncateInt64 format) reduced 0
              fun word => continuation (word ||| 0x8000000000000000)) m t m' :=
            Run.native_fp truncated finish
          have actual : Run (Runner.fp (.sub format) value format.int64Limit fun reducedWord =>
              Runner.fp (.truncateInt64 format) reducedWord 0
                fun word => continuation (word ||| 0x8000000000000000)) m t m' :=
            Run.native_fp (continuation := fun reducedWord =>
              Runner.fp (.truncateInt64 format) reducedWord 0
                fun word => continuation (word ||| 0x8000000000000000)) subtracted afterSub
          simpa only [fpToUInt64, nan, negative, upper, lower, Bool.false_or,
            Bool.false_eq_true, ↓reduceIte] using actual

end IR
end Runner
