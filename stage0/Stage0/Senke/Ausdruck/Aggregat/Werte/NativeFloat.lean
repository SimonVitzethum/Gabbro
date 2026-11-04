/- Native CPU float words and the existing complete-value frame encoding. -/
module
public import Grammatik.Kern.Syntax.Typen.FloatTransport
public import Runner.Basis.Floating
public import Stage0.Senke.Ausdruck.Aggregat.Werte.Encoding
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik

/-- The canonical frame word decodes to the complete native value. -/
theorem nativeFloat_read_word (value : Float) :
    Runner.readFloat value.toBits.toBitVec = value := by
  simpa only [Runner.readFloat, UInt64.ofBitVec_toBitVec] using
    NativeFloat.bits_roundtrip value

/-- A finite CPU result has exactly the word used by the existing frame ABI.
    The premise intentionally excludes any demand on NaN payload encodings. -/
theorem nativeFloat_word_eq {value : Float} {word : Runner.W}
    (finite : value.isFinite = true) (decoded : Runner.readFloat word = value) :
    word = value.toBits.toBitVec := by
  have finiteWord : (Float.ofBits (UInt64.ofBitVec word)).isFinite = true := by
    change (Runner.readFloat word).isFinite = true
    rw [decoded]
    exact finite
  have inverse := NativeFloat.finite_bits_inverse finiteWord
  have encoded : UInt64.ofBitVec word = value.toBits :=
    inverse.symm.trans (congrArg Float.toBits decoded)
  simpa only [UInt64.toBitVec_ofBitVec] using congrArg UInt64.toBitVec encoded

/-- Complete source float values keep the same one-word frame span. -/
theorem encodeWords_nativeFloat {D : Deklaration} (L : Lay D)
    {lo hi : Int × Int} (value : Wert D (.fl lo hi)) :
    encodeWords L (.fl lo hi) value = [value.x.toBits.toBitVec] := by
  rw [encodeWords.eq_def]

end Gabbro.Stage0.Senke
