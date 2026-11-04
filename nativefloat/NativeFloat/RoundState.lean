/- Shared final-state facts for the toolchain's native integer rounding. -/
module
public import NativeFloat.NormalForm
import all NativeFloat.NormalForm
@[expose] public section

namespace RootNativeFloat
open Float.Model
open Float.Model.UnpackedFloat

private theorem rounded_bounds (x : ExtendedMantissa) :
    x.mantissa ≤ x.roundedMantissa ∧ x.roundedMantissa ≤ x.mantissa + 1 := by
  rcases x with ⟨m, roundBit, stickyBit⟩
  cases roundBit <;> cases stickyBit <;>
    simp [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
      Accuracy.roundToNearestEven]
  omega

private theorem after_round_shift (F : Format) (r : Nat) (e : Int) (emin : F.minExponent ≤ e)
    (lower : 2 ^ F.mantissaBitsWithoutImplicit ≤ r)
    (upper : r ≤ 2 ^ (F.mantissaBitsWithoutImplicit + 1)) :
    shiftToTargetExponent F r e .exact =
      if r = 2 ^ (F.mantissaBitsWithoutImplicit + 1) then
        (⟨2 ^ F.mantissaBitsWithoutImplicit, false, false⟩, e + 1)
      else (⟨r, false, false⟩, e) := by
  by_cases carry : r = 2 ^ (F.mantissaBitsWithoutImplicit + 1)
  · rw [if_pos carry, carry]
    have target : F.targetExponent (totalExponent (2 ^ (F.mantissaBitsWithoutImplicit + 1)) e) = e + 1 := by
      simp only [Format.targetExponent, totalExponent, Nat.log2_two_pow,
        Format.mantissaBits, Int.natCast_add, Int.cast_ofNat_Int]
      omega
    unfold shiftToTargetExponent
    rw [target]
    unfold shiftToExponent
    dsimp only
    have amount : (e + 1 - e).toNat = 1 := by omega
    rw [amount]
    change (ExtendedMantissa.shiftRightOne ⟨2 ^ (F.mantissaBitsWithoutImplicit + 1), false, false⟩,
      e + 1) = _
    simp [ExtendedMantissa.shiftRightOne, Nat.pow_succ]
  · rw [if_neg carry]
    have positive : 0 < r := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) lower
    have log : r.log2 = F.mantissaBitsWithoutImplicit :=
      (Nat.log2_eq_iff (Nat.ne_of_gt positive)).mpr ⟨lower, by omega⟩
    have target : F.targetExponent (totalExponent r e) = e := by
      simp only [Format.targetExponent, totalExponent, log, Format.mantissaBits,
        Int.natCast_add, Int.cast_ofNat_Int]
      omega
    simpa using scaled_to_target F r 0 e positive target

end RootNativeFloat
