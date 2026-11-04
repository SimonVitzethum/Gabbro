/- Shared normal-form transport for the toolchain's floating primitives. -/
module
public import NativeFloat.Transport
import all NativeFloat.Transport
@[expose] public section

namespace RootNativeFloat
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

private theorem normal_unpack (F : Format) (s : Sign) (m : Nat) (e : Int) (positive : 0 < m)
    (lower : 2 ^ F.mantissaBitsWithoutImplicit ≤ m)
    (upper : m < 2 ^ (F.mantissaBitsWithoutImplicit + 1))
    (emin : (1 : Int) - F.exponentBias - F.mantissaBitsWithoutImplicit ≤ e)
    (emax : e ≤ ((2 ^ F.exponentBits : Nat) : Int) - 2 - F.exponentBias - F.mantissaBitsWithoutImplicit) :
    UnpackedFloat.unpack F (UnpackedFloat.pack F (.finite s m e positive)) = .finite s m e positive := by
  let j := (e + F.exponentBias + F.mantissaBitsWithoutImplicit).toNat
  have exponentRoom : 4 ≤ 2 ^ F.exponentBits := Nat.pow_le_pow_right (by decide : 0 < 2) F.he
  have jb : 1 ≤ j ∧ j + 1 < 2 ^ F.exponentBits := by dsimp [j]; omega
  have log : m.log2 = F.mantissaBitsWithoutImplicit :=
    (Nat.log2_eq_iff (Nat.ne_of_gt positive)).mpr ⟨lower, upper⟩
  have field : (BitVec.ofNat F.exponentBits j).toNat = j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have nonzero : BitVec.ofNat F.exponentBits j ≠ 0#F.exponentBits := by
    intro h
    have := congrArg BitVec.toNat h
    simp only [field, BitVec.toNat_ofNat, Nat.zero_mod] at this
    omega
  have nonmax : BitVec.ofNat F.exponentBits j ≠ -1#F.exponentBits := by
    intro h
    have := congrArg BitVec.toNat h
    simp only [field, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at this
    omega
  have packed : UnpackedFloat.pack F (.finite s m e positive) =
      packComponents F s (BitVec.ofNat F.exponentBits j) (BitVec.ofNat F.mantissaBitsWithoutImplicit m) := by
    have width : F.mantissaBitsWithoutImplicit + 1 = F.mantissaBits := by
      unfold Format.mantissaBits
      omega
    simp only [UnpackedFloat.pack, log, width]
    rw [if_neg (by change ¬ 2 ^ F.exponentBits ≤ j + 1; omega)]
    rfl
  have quotient : m / 2 ^ F.mantissaBitsWithoutImplicit = 1 :=
    Nat.div_eq_of_lt_le (by simpa using lower) (by simpa [Nat.pow_succ, Nat.mul_comm] using upper)
  have decomposition := Nat.mod_add_div m (2 ^ F.mantissaBitsWithoutImplicit)
  rw [quotient, Nat.mul_one] at decomposition
  have magnitude : (1#1 ++ BitVec.ofNat F.mantissaBitsWithoutImplicit m).toNat = m := by
    rw [BitVec.toNat_append,
      ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.ofNat F.mantissaBitsWithoutImplicit m).isLt,
      Nat.shiftLeft_eq]
    simp only [BitVec.toNat_ofNat]
    omega
  rw [packed]
  simp only [UnpackedFloat.unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
    unpack_sign_components, sign_unbits, nonmax, nonzero, ↓reduceIte, field, magnitude]
  congr 1
  dsimp [j]
  simp only [Int.natCast_add]
  omega

end RootNativeFloat
