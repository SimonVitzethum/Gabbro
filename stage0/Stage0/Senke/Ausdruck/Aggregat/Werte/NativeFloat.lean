/- Native CPU float words and the existing complete-value frame encoding. -/
module
public import NativeFloat.Hardware
public import Runner.Basis.Floating
public import Stage0.Senke.Ausdruck.Aggregat.Werte.Encoding
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik

/-- The canonical frame word decodes to the complete native value. -/
theorem nativeFloat_read_word [RootNativeFloat.Hardware] (value : Float) :
    Runner.readFloat value.hwToBits.toBitVec = value := by
  simpa only [Runner.readFloat, UInt64.ofBitVec_toBitVec] using
    RootNativeFloat.bits_roundtrip value

/-- A finite CPU result has exactly the word used by the existing frame ABI.
    The premise intentionally excludes any demand on NaN payload encodings. -/
theorem nativeFloat_word_eq [RootNativeFloat.Hardware] {value : Float} {word : Runner.W}
    (finite : value.hwIsFinite = true) (decoded : Runner.readFloat word = value) :
    word = value.hwToBits.toBitVec := by
  have finiteWord : (Float.hwOfBits (UInt64.ofBitVec word)).hwIsFinite = true := by
    change (Runner.readFloat word).hwIsFinite = true
    rw [decoded]
    exact finite
  have inverse := RootNativeFloat.finite_bits_inverse finiteWord
  have encoded : UInt64.ofBitVec word = value.hwToBits :=
    inverse.symm.trans (congrArg Float.hwToBits decoded)
  simpa only [UInt64.toBitVec_ofBitVec] using congrArg UInt64.toBitVec encoded

/-- Non-NaN conversion results retain their complete encoding on overflow too. -/
theorem nativeFloat_word_eq_nonNaN [RootNativeFloat.Hardware] {value : Float} {word : Runner.W}
    (notNaN : value.hwIsNaN = false) (decoded : Runner.readFloat word = value) :
    word = value.hwToBits.toBitVec := by
  have valid : (Float.hwOfBits (UInt64.ofBitVec word)).hwIsNaN = false := by
    change (Runner.readFloat word).hwIsNaN = false
    rw [decoded]
    exact notNaN
  have inverse := RootNativeFloat.bits_ofBits_notNaN valid
  have encoded : UInt64.ofBitVec word = value.hwToBits :=
    inverse.symm.trans (congrArg Float.hwToBits decoded)
  simpa only [UInt64.toBitVec_ofBitVec] using congrArg UInt64.toBitVec encoded

/-- Complete source float values keep the same one-word frame span. -/
theorem encodeWords_nativeFloat {D : Deklaration} (L : Lay D)
    {lo hi : Int × Int} (value : Wert D (.fl lo hi)) :
    encodeWords L (.fl lo hi) value = [value.x.hwToBits.toBitVec] := by
  rw [encodeWords.eq_def]

end Gabbro.Stage0.Senke
