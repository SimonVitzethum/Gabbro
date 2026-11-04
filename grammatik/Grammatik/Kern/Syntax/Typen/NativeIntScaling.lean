/- Native CPU conversion and scaling of the existing wide integer form. -/
module
public import Grammatik.Kern.Syntax.Typen.NativeIntScaleCore
import all Grammatik.Kern.Syntax.Typen.NativeIntScaleCore
import all Grammatik.Kern.Syntax.Typen.NativeIntConversion
@[expose] public section

namespace Gabbro.Grammatik.NativeFloat
open Float.Model
open Float.Model.UnpackedFloat
open NativeScale

/-- The existing wide integer normalization needs one signed native conversion
    and one native multiplication. The saturated exponent index is retained
    exactly, including both signed overflow outcomes. -/
theorem ofInt_jam56 (z : Int) (large : 2 ^ 55 ≤ z.natAbs) :
    let n := z.natAbs
    let k := n.log2 - 55
    let g := (n >>> k) ||| (if n % 2 ^ k = 0 then 0 else 1)
    let i := min 2047 (k + 1078)
    Float.ofInt z = Float.mul (Int64.ofInt (g : Int)).toFloat
      (Float.ofBits (UInt64.ofNat ((if z < 0 then 2 ^ 63 else 0) + (i - 55) * 2 ^ 52))) := by
  dsimp only
  let n := z.natAbs
  let k := n.log2 - 55
  let g := (n >>> k) ||| (if n % 2 ^ k = 0 then 0 else 1)
  let i := min 2047 (k + 1078)
  let j := i - 55
  let s : Sign := if z < 0 then .negative else .positive
  have bounds : 2 ^ 55 ≤ g ∧ g < 2 ^ 56 ∧ n.log2 = k + 55 := magnitude_bounds n large
  have jl : 1023 ≤ j := by dsimp [j, i]; omega
  have ju : j ≤ 1992 := by dsimp [j, i]; omega
  have word : (Int64.ofInt (g : Int)).toInt = (g : Int) :=
    Int64.toInt_ofInt_of_le (by omega) (by omega)
  have converted : ((Int64.ofInt (g : Int)).toFloat).toModel.unpack =
      round Format.binary64 .positive g 0 := by
    change (Float.ofModel (Float.Model.ofInt (Int64.ofInt (g : Int)).toInt)).toModel.unpack = _
    rw [word]
    exact retained_unpacked g bounds.1 bounds.2.1
  have signWord : (if s = .negative then 2 ^ 63 else 0 : Nat) =
      (if z < 0 then 2 ^ 63 else 0) := by
    dsimp [s]
    split <;> rfl
  have power : (Float.ofBits (UInt64.ofNat
      ((if z < 0 then 2 ^ 63 else 0) + j * 2 ^ 52))).toModel.unpack =
      .finite s (2 ^ 52) ((j : Int) - 1075) (by decide) := by
    simpa only [signWord] using power_unpacked s j jl ju
  have nonzero : z ≠ 0 := by
    intro zero
    simp only [zero, Int.natAbs_zero] at large
    omega
  rw [ofInt_model]
  change Float.ofModel (Float.Model.pack (UnpackedFloat.ofInt Format.binary64 z)) =
    Float.ofModel (Float.Model.pack (UnpackedFloat.mul Format.binary64
      ((Int64.ofInt (g : Int)).toFloat).toModel.unpack
      (Float.ofBits (UInt64.ofNat
        ((if z < 0 then 2 ^ 63 else 0) + j * 2 ^ 52))).toModel.unpack))
  rw [converted, power]
  apply congrArg Float.ofModel
  apply model_eq
  change UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (UnpackedFloat.ofInt Format.binary64 z)) =
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (UnpackedFloat.mul Format.binary64
      (round Format.binary64 .positive g 0) (.finite s (2 ^ 52) ((j : Int) - 1075) (by decide))))
  rw [integer_round z nonzero]
  exact congrArg UInt64.ofBitVec (packed_product s n large)

end Gabbro.Grammatik.NativeFloat
