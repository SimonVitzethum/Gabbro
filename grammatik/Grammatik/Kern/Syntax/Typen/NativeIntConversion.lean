/- Correspondence of native integer conversions and the toolchain model. -/
module
public import Grammatik.Kern.Syntax.Typen.FloatTransport
public import Init.Data.OfScientific
public import Init.Data.SInt.Float
import Init.Data.SInt.Lemmas
@[expose] public section

namespace Gabbro.Grammatik.NativeFloat
open Float.Model
open Float.Model.UnpackedFloat

private theorem shifted_log (m k : Nat) (nonzero : m ≠ 0) :
    (m <<< k).log2 = m.log2 + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have nz : m <<< k ≠ 0 := by
        rw [Nat.shiftLeft_eq]
        exact Nat.mul_ne_zero nonzero (Nat.ne_of_gt (Nat.two_pow_pos k))
      rw [Nat.shiftLeft_succ, Nat.log2_two_mul nz, ih]
      omega

private theorem shifted_exact (m k : Nat) :
    Nat.repeat ExtendedMantissa.shiftRightOne k ⟨m <<< k, false, false⟩ =
      ⟨m, false, false⟩ := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
      rw [Nat.repeat, Nat.shiftLeft_succ_inside, ih]
      simp [ExtendedMantissa.shiftRightOne]

private theorem exact_at_target (F : Format) (s : Sign) (m : Nat) (e : Int)
    (positive : 0 < m) (target : F.targetExponent (totalExponent m e) = e) :
    roundWithAccuracy F s m e .exact = .finite s m e positive := by
  simp [roundWithAccuracy, shiftToTargetExponent, target, shiftToExponent,
    ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.roundedMantissa,
    ExtendedMantissa.accuracy, Accuracy.roundToNearestEven, Nat.repeat,
    Nat.ne_of_gt positive]

private theorem scaled_to_target (F : Format) (m k : Nat) (e : Int)
    (positive : 0 < m) (target : F.targetExponent (totalExponent m e) = e) :
    shiftToTargetExponent F (m <<< k) (e - k) .exact =
      (⟨m, false, false⟩, e) := by
  have total : totalExponent (m <<< k) (e - k) = totalExponent m e := by
    unfold totalExponent
    rw [shifted_log m k (Nat.ne_of_gt positive)]
    simp only [Nat.cast_add]
    omega
  have amount : (e - (e - (k : Int))).toNat = k := by omega
  unfold shiftToTargetExponent
  rw [total, target]
  unfold shiftToExponent
  rw [amount]
  change (Nat.repeat ExtendedMantissa.shiftRightOne k ⟨m <<< k, false, false⟩,
    e - (k : Int) + k) = (⟨m, false, false⟩, e)
  rw [shifted_exact]
  congr 1
  omega

private theorem exact_scaled (F : Format) (s : Sign) (m k : Nat) (e : Int)
    (positive : 0 < m) (target : F.targetExponent (totalExponent m e) = e) :
    roundWithAccuracy F s (m <<< k) (e - k) .exact = .finite s m e positive := by
  unfold roundWithAccuracy
  rw [scaled_to_target F m k e positive target]
  dsimp only [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
    Accuracy.roundToNearestEven]
  have unchanged : shiftToTargetExponent F m e .exact = (⟨m, false, false⟩, e) := by
    simpa using scaled_to_target F m 0 e positive target
  rw [unchanged]
  simp [Nat.ne_of_gt positive]

private theorem unpack_target {bits : BitVec 64} {s : Sign} {m : Nat} {e : Int} {positive : 0 < m}
    (decoded : UnpackedFloat.unpack Format.binary64 bits = .finite s m e positive) :
    Format.binary64.targetExponent (totalExponent m e) = e := by
  unfold UnpackedFloat.unpack at decoded
  dsimp only at decoded
  split at decoded
  · split at decoded <;> cases decoded
  · split at decoded
    · next zero =>
        split at decoded
        · cases decoded
        · next nonzero =>
            cases decoded
            have mn : (unpackMantissa (spec := Format.binary64) bits).toNat ≠ 0 := by
              intro h
              apply nonzero
              apply BitVec.eq_of_toNat_eq
              simpa using h
            have logBound : (unpackMantissa (spec := Format.binary64) bits).toNat.log2 < 52 :=
              (Nat.log2_lt mn).mpr (unpackMantissa (spec := Format.binary64) bits).isLt
            simp only [zero, BitVec.toNat_ofNat, Nat.zero_mod]
            change max ((↑(unpackMantissa (spec := Format.binary64) bits).toNat.log2 : Int) +
              1 + (0 - 1075 + 1) - 53) (-1074) = 0 - 1075 + 1
            omega
    · next nonzero =>
        cases decoded
        have ev : 0 < (unpackExponent (spec := Format.binary64) bits).toNat := by
          have ne : (unpackExponent (spec := Format.binary64) bits).toNat ≠ 0 := by
            intro h
            apply nonzero
            apply BitVec.eq_of_toNat_eq
            simpa using h
          omega
        have mb := (unpackMantissa (spec := Format.binary64) bits).isLt
        have magnitude : (1#1 ++ unpackMantissa (spec := Format.binary64) bits).toNat =
            2 ^ 52 + (unpackMantissa (spec := Format.binary64) bits).toNat := by
          rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt mb, Nat.shiftLeft_eq]
          simp
        have logValue : (1#1 ++ unpackMantissa (spec := Format.binary64) bits).toNat.log2 = 52 := by
          apply (Nat.log2_eq_iff (by rw [magnitude]; omega)).mpr
          rw [magnitude]
          omega
        change max ((↑(1#1 ++ unpackMantissa (spec := Format.binary64) bits).toNat.log2 : Int) +
          1 + (↑(unpackExponent (spec := Format.binary64) bits).toNat - 1075) - 53) (-1074) =
          ↑(unpackExponent (spec := Format.binary64) bits).toNat - 1075
        rw [logValue]
        omega

private theorem one_unpacked : (Float.ofInt 1).toModel.unpack =
    .finite .positive (2 ^ 52) (-52) (by decide) := by decide

private theorem mul_one_unpacked (x : Float.Model) :
    UnpackedFloat.mul Format.binary64 x.unpack (Float.ofInt 1).toModel.unpack = x.unpack := by
  rw [one_unpacked]
  cases decoded : x.unpack with
  | notANumber => rfl
  | infinity s => cases s <;> rfl
  | zero s => cases s <;> rfl
  | finite s m e positive =>
      have target := unpack_target (bits := x.toBits.toBitVec) decoded
      have result := exact_scaled Format.binary64 s m 52 e positive target
      cases s <;> simpa [UnpackedFloat.mul, Nat.shiftLeft_eq, Int.sub_eq_add_neg] using result

/-- Multiplication by the actual native conversion of integer one preserves
    the complete native value, including infinities and canonical NaN. -/
theorem mul_one (x : Float) : Float.mul x (Float.ofInt 1) = x := by
  change Float.ofModel (Float.Model.pack
    (UnpackedFloat.mul Format.binary64 x.toModel.unpack (Float.ofInt 1).toModel.unpack)) = x
  rw [mul_one_unpacked]
  exact bits_roundtrip x

private theorem div_one_unpacked (x : Float.Model) :
    UnpackedFloat.div Format.binary64 x.unpack (Float.ofInt 1).toModel.unpack = x.unpack := by
  rw [one_unpacked]
  cases decoded : x.unpack with
  | notANumber => rfl
  | infinity s => cases s <;> rfl
  | zero s => cases s <;> rfl
  | finite s m e positive =>
      have target := unpack_target (bits := x.toBits.toBitVec) decoded
      let t := Format.binary64.targetExponent (totalExponent m e - 1)
      have below : t ≤ e := by
        dsimp [t, Format.targetExponent] at *
        omega
      let k := (e - t).toNat
      have back : t = e - (k : Int) := by dsimp [k]; omega
      have quotientTarget : min (e - (-52)) t = t := Int.min_eq_right (by omega)
      have amount : (e - (-52) - t).toNat = k + 52 := by dsimp [k]; omega
      have core : divCore Format.binary64 m e (2 ^ 52) (-52) = (m <<< k, t, .exact) := by
        unfold divCore
        have oneTotal : totalExponent (2 ^ 52) (-52) = 1 := by decide
        rw [oneTotal]
        change ((m <<< (e - (-52) - min (e - (-52)) t).toNat) / 2 ^ 52,
          min (e - (-52)) t,
          accuracyOfFraction ((m <<< (e - (-52) - min (e - (-52)) t).toNat) % 2 ^ 52)
            (2 ^ 52)) = (m <<< k, t, .exact)
        rw [quotientTarget, amount, Nat.shiftLeft_add, Nat.shiftLeft_eq]
        simp [accuracyOfFraction, Nat.mul_div_cancel, Nat.two_pow_pos]
      have result := exact_scaled Format.binary64 s m k e positive target
      cases s <;> simpa only [UnpackedFloat.div, core, back] using result

/-- Division by the actual native conversion of integer one is an identity.
    No finite-only premise or raw NaN-payload equality is required. -/
theorem div_one (x : Float) : Float.div x (Float.ofInt 1) = x := by
  change Float.ofModel (Float.Model.pack
    (UnpackedFloat.div Format.binary64 x.toModel.unpack (Float.ofInt 1).toModel.unpack)) = x
  rw [div_one_unpacked]
  exact bits_roundtrip x

/-- The existing integer-literal fraction path agrees with native conversion. -/
theorem integerbruch_single (z : Int) : Float.div (Float.ofInt z) (Float.ofInt 1) = Float.ofInt z :=
  div_one (Float.ofInt z)

end Gabbro.Grammatik.NativeFloat
