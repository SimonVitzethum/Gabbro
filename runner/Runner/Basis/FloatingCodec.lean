module
public import Runner.Basis.FloatingSequence
import NativeFloat.Transport
@[expose] public section

namespace Runner

/-! The codec instructions refine the existing native value semantics. Raw NaN
    payloads are allowed; only the physical NEG word operation is deterministic. -/

theorem fpNegWord_decoded (format : FPFormat) (word : W) :
    match format with
    | .f32 => readFloat32 (fpNegWord .f32 word) = -readFloat32 word
    | .f64 => readFloat (fpNegWord .f64 word) = -readFloat word := by
  cases format
  · simpa only [readFloat32, fpNegWord, BitVec.setWidth_setWidth_of_le _ (by decide),
      BitVec.setWidth_eq] using RootNativeFloat.neg_bits32 (word.setWidth 32)
  · exact RootNativeFloat.neg_bits64 word

theorem nativeNeg_result {format : FPFormat} {a b result : W}
    (h : NativeFPEval (.neg format) a b result) : result = fpNegWord format a := h

theorem NativeFPEval.neg_decoded {format : FPFormat} {a b result : W}
    (h : NativeFPEval (.neg format) a b result) :
    match format with
    | .f32 => readFloat32 result = -readFloat32 a
    | .f64 => readFloat result = -readFloat a := by
  rw [nativeNeg_result h]
  exact fpNegWord_decoded format a

theorem nativeFinite_value (format : FPFormat) (a b : W) :
    nativeFP (.isFinite format) a b = .word (fpFiniteWord format a) := by
  cases format
  · simp only [nativeFP, readFloat32, RootNativeFloat.finite_word32_mask, fpFiniteWord]
  · simp only [nativeFP, readFloat, RootNativeFloat.finite_word_mask, fpFiniteWord]

theorem nativeFinite_result {format : FPFormat} {a b result : W}
    (h : NativeFPEval (.isFinite format) a b result) : result = fpFiniteWord format a := by
  simpa only [NativeFPEval, nativeFinite_value, NativeFPValue.Matches] using h

/-- A model witness for composing native requests. This is a proof about the
    reference representative; it is not an executable program backend. -/
theorem nativeFPBits_eval (kind : NativeFPOp) (a b : W) :
    NativeFPEval kind a b (nativeFPBits kind a b) := by
  unfold NativeFPEval nativeFPBits
  cases value : nativeFP kind a b with
  | word result => rfl
  | f64 result =>
    change Float.ofBits result.toBits = result
    exact RootNativeFloat.bits_roundtrip result
  | f32 result =>
    constructor
    · change result.toBits.toBitVec.setWidth 64 =
        ((result.toBits.toBitVec.setWidth 64).setWidth 32).setWidth 64
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    · change Float32.ofBits (UInt32.ofBitVec ((result.toBits.toBitVec.setWidth 64).setWidth 32)) = result
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
      exact RootNativeFloat.bits32_roundtrip result

end Runner
