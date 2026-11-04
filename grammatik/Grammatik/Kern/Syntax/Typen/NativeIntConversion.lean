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

private theorem extended_shift (x : ExtendedMantissa) (k : Nat) :
    x >>> k = Nat.repeat ExtendedMantissa.shiftRightOne k x := rfl

private theorem exact_at_target (F : Format) (s : Sign) (m : Nat) (e : Int)
    (positive : 0 < m) (target : F.targetExponent (totalExponent m e) = e) :
    roundWithAccuracy F s m e .exact = .finite s m e positive := by
  simp [roundWithAccuracy, shiftToTargetExponent, target, shiftToExponent,
    ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.roundedMantissa,
    ExtendedMantissa.accuracy, Accuracy.roundToNearestEven, extended_shift, Nat.repeat,
    Nat.ne_of_gt positive]

private theorem scaled_to_target (F : Format) (m k : Nat) (e : Int)
    (positive : 0 < m) (target : F.targetExponent (totalExponent m e) = e) :
    shiftToTargetExponent F (m <<< k) (e - k) .exact =
      (⟨m, false, false⟩, e) := by
  have total : totalExponent (m <<< k) (e - k) = totalExponent m e := by
    unfold totalExponent
    rw [shifted_log m k (Nat.ne_of_gt positive)]
    simp only [Int.natCast_add]
    omega
  have amount : (e - (e - (k : Int))).toNat = k := by omega
  unfold shiftToTargetExponent
  rw [total, target]
  unfold shiftToExponent
  dsimp only
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
    .finite .positive (2 ^ 52) (-52) (by decide) := by
  have one : Float.ofInt 1 = Float.ofBits 0x3ff0000000000000 := by decide
  rw [one]
  rfl

private theorem sign_mul_one (s : Sign) : s * Sign.positive = s := by cases s <;> rfl

private theorem sign_div_one (s : Sign) : s / Sign.positive = s := by cases s <;> rfl

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
      simpa only [UnpackedFloat.mul, sign_mul_one, Nat.shiftLeft_eq, Int.sub_eq_add_neg] using result

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
      simpa only [UnpackedFloat.div, sign_div_one, core, back] using result

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

private theorem repeat_sum {α : Type} (f : α → α) (a b : Nat) (x : α) :
    Nat.repeat f (a + b) x = Nat.repeat f b (Nat.repeat f a x) := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [Nat.add_succ, Nat.repeat, ih]

private theorem integer_initial (m k : Nat) (positive : 0 < m) :
    shiftToTargetExponent Format.binary64 (m <<< k) (-(k : Int)) .exact =
      (Nat.repeat ExtendedMantissa.shiftRightOne
        (Format.binary64.targetExponent (totalExponent m 0) + k).toNat ⟨m <<< k, false, false⟩,
       -(k : Int) + (Format.binary64.targetExponent (totalExponent m 0) + k).toNat) := by
  have total : totalExponent (m <<< k) (-(k : Int)) = totalExponent m 0 := by
    unfold totalExponent
    rw [shifted_log m k (Nat.ne_of_gt positive)]
    simp only [Int.natCast_add]
    omega
  unfold shiftToTargetExponent
  rw [total]
  unfold shiftToExponent
  dsimp only
  rw [extended_shift]
  congr 2 <;> omega

private theorem round_integer_prescale (s : Sign) (m : Nat) (positive : 0 < m) :
    round Format.binary64 s m 0 =
      roundWithAccuracy Format.binary64 s (m <<< 53) (-53) .exact := by
  let t := Format.binary64.targetExponent (totalExponent m 0)
  let a := (-t).toNat
  have lower : -52 ≤ t := by
    dsimp [t, Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  have initial : shiftToTargetExponent Format.binary64 (m <<< a) (-(a : Int)) .exact =
      shiftToTargetExponent Format.binary64 (m <<< 53) (-53) .exact := by
    rw [integer_initial m a positive, integer_initial m 53 positive]
    change (Nat.repeat ExtendedMantissa.shiftRightOne (t + a).toNat ⟨m <<< a, false, false⟩,
        -(a : Int) + (t + a).toNat) =
      (Nat.repeat ExtendedMantissa.shiftRightOne (t + 53).toNat ⟨m <<< 53, false, false⟩,
        -53 + (t + 53).toNat)
    by_cases nonnegative : 0 ≤ t
    · have azero : a = 0 := by dsimp [a]; omega
      have amount : (t + 53).toNat = 53 + t.toNat := by omega
      rw [azero, amount, repeat_sum, shifted_exact]
      simp only [Nat.shiftLeft_zero, Int.natCast_zero, Int.add_zero, Int.neg_zero]
      congr 1
      omega
    · have small : a ≤ 53 := by dsimp [a]; omega
      have sourceAmount : (t + a).toNat = 0 := by dsimp [a]; omega
      have targetAmount : (t + 53).toNat = 53 - a := by dsimp [a]; omega
      have shifted : m <<< 53 = (m <<< a) <<< (53 - a) := by
        rw [← Nat.shiftLeft_add]
        congr 1
        omega
      rw [sourceAmount, targetAmount, shifted, shifted_exact]
      simp only [Nat.repeat]
      congr 1
      dsimp [a]
      omega
  have same : roundWithAccuracy Format.binary64 s (m <<< a) (-(a : Int)) .exact =
      roundWithAccuracy Format.binary64 s (m <<< 53) (-53) .exact := by
    unfold roundWithAccuracy
    rw [initial]
  simpa only [round, decreaseExponent, t, a, Int.zero_sub] using same

private theorem scientific_zero (n : Nat) :
    UnpackedFloat.ofScientific Format.binary64 n 0 = UnpackedFloat.ofNat Format.binary64 n := by
  by_cases zero : n = 0
  · subst n
    rfl
  have comparePositive : compare (n : Int) 0 = .gt := Int.compare_eq_gt.mpr (by omega)
  have notLarge : ¬ (0 : Int) > 2 ^ Format.binary64.exponentBits := by decide
  have notSmall : ¬ (0 : Int) < -((2 ^ Format.binary64.exponentBits : Int) + n.log2) := by omega
  simp only [UnpackedFloat.ofScientific, zero, notLarge, notSmall, ↓reduceDIte,
    show (0 : Int) ≤ 0 from Int.le_refl 0, ↓reduceIte, Int.toNat_zero, Nat.pow_zero,
    UnpackedFloat.mul, Nat.mul_one, Int.add_zero,
    UnpackedFloat.ofNat, UnpackedFloat.ofInt, normalize, comparePositive]
  exact (round_integer_prescale .positive n (Nat.pos_of_ne_zero zero)).symm

/-- The actual scientific-literal conversion agrees with the toolchain's
    integer-normalization model, including integers larger than a machine word. -/
theorem ofNat_model (n : Nat) : Float.ofNat n = Float.ofModel (Float.Model.ofNat n) := by
  unfold Float.ofNat
  change Float.ofScientific n false 0 = _
  unfold Float.ofScientific
  by_cases small : n < 2 ^ 53
  · rw [dif_pos ⟨small, by decide⟩]
    change Float.mul (UInt64.ofNat n).toFloat (Float.ofBits 0x3ff0000000000000) = _
    have one : Float.ofBits 0x3ff0000000000000 = Float.ofInt 1 := by decide
    rw [one, mul_one]
    change Float.ofModel (Float.Model.ofNat (n % 2 ^ 64)) = _
    rw [Nat.mod_eq_of_lt (by omega)]
  · rw [dif_neg (by intro h; exact small h.1)]
    change Float.ofModel (Float.Model.pack (UnpackedFloat.ofScientific Format.binary64 n 0)) = _
    rw [scientific_zero]
    rfl

private theorem unpack_sign_components (F : Format) (s : Sign)
    (e : BitVec F.exponentBits) (m : BitVec F.mantissaBitsWithoutImplicit) :
    unpackSign (packComponents F s e m) = s.toBitVec := by
  ext i hi
  simp [unpackSign, packComponents, BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append, hi]

private theorem sign_unbits (s : Sign) : Sign.ofBitVec s.toBitVec = s := by cases s <;> rfl

private theorem unpack_components_neg (F : Format) (s : Sign)
    (e : BitVec F.exponentBits) (m : BitVec F.mantissaBitsWithoutImplicit) :
    UnpackedFloat.unpack F (packComponents F (-s) e m) =
      UnpackedFloat.neg (UnpackedFloat.unpack F (packComponents F s e m)) := by
  simp only [UnpackedFloat.unpack, unpackMantissa_packComponents,
    unpackExponent_packComponents, unpack_sign_components, sign_unbits]
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · rfl

private theorem neg_decode_pack (u : UnpackedFloat) :
    UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64 (UnpackedFloat.neg u)) =
      UnpackedFloat.neg (UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64 u)) := by
  cases u with
  | notANumber => rfl
  | infinity s =>
      exact unpack_components_neg Format.binary64 s (-1#11) 0
  | zero s =>
      exact unpack_components_neg Format.binary64 s 0 0
  | finite s m e positive =>
      simp only [UnpackedFloat.neg, UnpackedFloat.pack, packedInfinity]
      split
      · exact unpack_components_neg Format.binary64 s (-1#11) 0
      · split <;> exact unpack_components_neg Format.binary64 s _ _

private theorem model_eq {a b : Float.Model} (same : a.toBits = b.toBits) : a = b := by
  cases a
  cases b
  cases same
  rfl

private theorem model_neg_pack (u : UnpackedFloat) :
    Float.Model.neg (Float.Model.pack u) = Float.Model.pack (UnpackedFloat.neg u) := by
  apply model_eq
  change UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
    (UnpackedFloat.neg (UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64 u)))) =
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (UnpackedFloat.neg u))
  rw [← neg_decode_pack]
  exact congrArg UInt64.ofBitVec
    (pack_unpack Format.binary64 _ (valid_pack (f := UnpackedFloat.neg u)))

private theorem round_neg (F : Format) (s : Sign) (m : Nat) (e : Int) :
    UnpackedFloat.neg (round F s m e) = round F (-s) m e := by
  unfold round roundWithAccuracy
  dsimp only
  split <;> rfl

private theorem model_neg_ofNat (n : Nat) (positive : 0 < n) :
    Float.Model.neg (Float.Model.ofNat n) = Float.Model.ofInt (-(n : Int)) := by
  unfold Float.Model.ofNat Float.Model.ofInt
  rw [model_neg_pack]
  have cp : compare (n : Int) 0 = .gt := Int.compare_eq_gt.mpr (by omega)
  have cn : compare (-(n : Int)) 0 = .lt := Int.compare_eq_lt.mpr (by omega)
  have sign : -Sign.positive = Sign.negative := rfl
  simp only [UnpackedFloat.ofNat, UnpackedFloat.ofInt, normalize, cp, cn,
    Int.toNat_natCast, Int.neg_neg, round_neg, sign]

/-- The actual public integer conversion, including its scientific fast/slow
    paths and negative case, agrees with native integer normalization. -/
theorem ofInt_model (z : Int) : Float.ofInt z = Float.ofModel (Float.Model.ofInt z) := by
  cases z with
  | ofNat n => exact ofNat_model n
  | negSucc n =>
      change Float.neg (Float.ofNat (n + 1)) = Float.ofModel (Float.Model.ofInt (.negSucc n))
      rw [ofNat_model]
      change Float.ofModel (Float.Model.neg (Float.Model.ofNat (n + 1))) = _
      rw [model_neg_ofNat (n + 1) (by omega)]
      rfl

/-- A signed native conversion preserves the actual source conversion on its
    complete signed64 input range. -/
theorem ofInt_signed64 (z : Int) (lower : -(2 ^ 63) ≤ z) (upper : z < 2 ^ 63) :
    Float.ofInt z = (Int64.ofInt z).toFloat := by
  rw [ofInt_model]
  change Float.ofModel (Float.Model.ofInt z) =
    Float.ofModel (Float.Model.ofInt (Int64.ofInt z).toInt)
  rw [Int64.toInt_ofInt_of_le lower upper]

/-- The same adapter at the stored signed-word boundary used by native IR. -/
theorem ofInt_signed64_bits (z : Int) (lower : -(2 ^ 63) ≤ z) (upper : z < 2 ^ 63) :
    Float.ofInt z = (Int64.ofBitVec (BitVec.ofInt 64 z)).toFloat := by
  have word : Int64.ofBitVec (BitVec.ofInt 64 z) = Int64.ofInt z := rfl
  rw [word]
  exact ofInt_signed64 z lower upper

/-- Unsigned native conversion agrees on the complete unsigned64 input range. -/
theorem ofInt_unsigned64 (z : Int) (lower : 0 ≤ z) (upper : z < 2 ^ 64) :
    Float.ofInt z = (UInt64.ofNat z.toNat).toFloat := by
  rw [ofInt_model]
  change Float.ofModel (Float.Model.ofInt z) =
    Float.ofModel (Float.Model.ofInt (z.toNat % 2 ^ 64 : Nat))
  rw [Nat.mod_eq_of_lt (by omega), Int.toNat_of_nonneg lower]

end Gabbro.Grammatik.NativeFloat
