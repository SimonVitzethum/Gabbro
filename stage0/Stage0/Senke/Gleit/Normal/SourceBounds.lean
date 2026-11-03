/- Bounds of the actual three-guard-bit alignment, before normalization. -/
module
public import Stage0.Senke.Gleit.Normal.Source
public import Stage0.Senke.Gleit.Routine.RoutineOrderModel
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

/-- Natural shadow of the emitted directional word, with no word truncation. -/
def softAlignedMagnitude (sa sb : Bool) (l r gap : Nat) : Nat :=
  if sa == sb then l * 8 + softShiftJamNat (r * 8) gap
  else l * 8 - softShiftJamNat (r * 8) gap

/-- Ordering finite significands bounds the sticky word and leaves at least
    four units in every nonzero result. A gap of two already prevents deep
    cancellation, so inexact alignment remains in the normal replay range. -/
theorem softAlignedMagnitude_bounds (sa sb : Bool) (l r e f : Nat)
    (lb : l < 2 ^ 53) (rb : r < 2 ^ 53) (fp : 1 ≤ f) (order : f ≤ e)
    (equal : f = e → r ≤ l) (different : f < e → 2 ^ 52 ≤ l) :
    r ≤ l * 2 ^ (e - f) ∧
    softShiftJamNat (r * 8) (e - f) ≤ l * 8 ∧
    softAlignedMagnitude sa sb l r (e - f) < 2 ^ 57 ∧
    (softAlignedMagnitude sa sb l r (e - f) = 0 ∨
      4 ≤ softAlignedMagnitude sa sb l r (e - f)) ∧
    ((r * 8) % 2 ^ (e - f) ≠ 0 →
      2 ^ 54 ≤ softAlignedMagnitude sa sb l r (e - f) ∧
      f64.emin ≤ (e : Int) - 1078 +
        (bitlen (softAlignedMagnitude sa sb l r (e - f)) : Int) - 1) := by
  let gap := e - f
  let j := softShiftJamNat (r * 8) gap
  let n := softAlignedMagnitude sa sb l r gap
  have dp : 0 < (2 : Nat) ^ gap := Nat.two_pow_pos _
  have cover : r ≤ l * 2 ^ gap := by
    by_cases zero : gap = 0
    · have same : f = e := by omega
      simpa only [zero, Nat.pow_zero, Nat.mul_one] using equal same
    · have leading := different (by omega)
      have power : 2 ≤ (2 : Nat) ^ gap := Nat.pow_le_pow_right (by decide) (by omega : 1 ≤ gap)
      nlinarith
  have certificate := softShiftJamNat_interval (r * 8) gap
  by_cases narrow : gap ≤ 1
  · have casesGap : gap = 0 ∨ gap = 1 := by omega
    rcases casesGap with zero | one
    · have jam : j = r * 8 := by simp [j, softShiftJamNat, zero]
      have ordered : j ≤ l * 8 := by
        have := equal (by omega)
        omega
      refine ⟨cover, ordered, ?_, ?_, ?_⟩
      · change n < 2 ^ 57
        unfold n softAlignedMagnitude
        rw [jam]
        split <;> omega
      · change n = 0 ∨ 4 ≤ n
        unfold n softAlignedMagnitude
        rw [jam]
        split
        · omega
        · have difference := Nat.sub_add_cancel ordered
          rw [jam] at difference
          omega
      · intro tail
        exact (tail (by simp only [show e - f = 0 from zero, Nat.pow_zero, Nat.mod_one])).elim
    · have jam : j = r * 4 := by
        simp only [j, softShiftJamNat, one, Nat.shiftRight_eq_div_pow]
        have tail : (r * 8) % 2 ^ 1 = 0 := by omega
        rw [if_pos tail, Nat.or_zero]
        omega
      have leading := different (by omega)
      have ordered : j ≤ l * 8 := by rw [jam]; omega
      refine ⟨cover, ordered, ?_, ?_, ?_⟩
      · change n < 2 ^ 57
        unfold n softAlignedMagnitude
        rw [jam]
        split <;> omega
      · change n = 0 ∨ 4 ≤ n
        unfold n softAlignedMagnitude
        rw [jam]
        split
        · omega
        · have difference := Nat.sub_add_cancel ordered
          rw [jam] at difference
          omega
      · intro tail
        exact (tail (by rw [show e - f = 1 from one]; omega)).elim
  · have gap2 : 2 ≤ gap := by omega
    have power : 4 ≤ (2 : Nat) ^ gap := Nat.pow_le_pow_right (by decide) gap2
    have leading := different (by omega)
    have jb : j ≤ 2 ^ 54 := by
      rcases certificate with exactValue | ⟨odd, lo, hi⟩
      · have exactR : r * 8 = j * 2 ^ gap := exactValue.2
        nlinarith [exactR]
      · change (j - 1) * 2 ^ gap < r * 8 at lo
        by_cases positive : 0 < j
        · have pred : j - 1 + 1 = j := by omega
          nlinarith
        · omega
    have ordered : j ≤ l * 8 := by omega
    have wide : 2 ^ 54 ≤ n := by
      unfold n softAlignedMagnitude
      split <;> omega
    have nb : n < 2 ^ 57 := by
      unfold n softAlignedMagnitude
      split <;> omega
    have bits : 55 ≤ bitlen n := by
      have upper := bitlen_obere n
      by_contra h
      have power := Nat.pow_le_pow_right (by decide : 0 < 2)
        (show bitlen n ≤ 54 by omega)
      omega
    refine ⟨cover, ordered, nb, Or.inr (by omega), fun _ => ⟨wide, ?_⟩⟩
    change (-1022 : Int) ≤ (e : Int) - 1078 + (bitlen n : Int) - 1
    omega

/-- The signless source order supplies precisely the two ordering facts
    needed by the bounded alignment argument, including exponent 0 versus 1. -/
theorem routineSource_order (a b : GFloat) (ha : wf f64 a) (hb : wf f64 b)
    (order : floatMag b ≤ floatMag a) :
    (max b.bexp 1 = max a.bexp 1 → softSig b.bexp b.frac ≤ softSig a.bexp a.frac) ∧
    (max b.bexp 1 < max a.bexp 1 → 2 ^ 52 ≤ softSig a.bexp a.frac) := by
  have af : a.frac < 2 ^ 52 := ha.2
  have bf : b.frac < 2 ^ 52 := hb.2
  unfold floatMag at order
  unfold softSig
  constructor
  · intro same
    split <;> split <;> omega
  · intro different
    split <;> omega

/-- Expose the routine's actual aligned word as the bounded natural shadow.
    The signed subtraction is exact because magnitude ordering was proved
    before either word operation is replaced by natural arithmetic. -/
theorem routineDirectionalWord_canonical (a b : GFloat)
    (ha : wf f64 a) (hb : wf f64 b) (order : floatMag b ≤ floatMag a) :
    routineDirectionalWord (BitVec.ofNat 64 (zuBits f64 a))
      (BitVec.ofNat 64 (zuBits f64 b)) =
      BitVec.ofNat 64 (softAlignedMagnitude a.sign b.sign
        (softSig a.bexp a.frac) (softSig b.bexp b.frac)
        (max a.bexp 1 - max b.bexp 1)) := by
  obtain ⟨asig, aindex⟩ := routineSigIndex_canonical a ha
  obtain ⟨bsig, bindex⟩ := routineSigIndex_canonical b hb
  obtain ⟨asign, _, _⟩ := routineUnpack_canonical a ha
  obtain ⟨bsign, _, _⟩ := routineUnpack_canonical b hb
  have lb : softSig a.bexp a.frac < 2 ^ 53 := by unfold softSig; split <;> have := ha.2 <;> omega
  have rb : softSig b.bexp b.frac < 2 ^ 53 := by unfold softSig; split <;> have := hb.2 <;> omega
  have indices := routineOrder_indices a b ha hb order
  obtain ⟨equal, different⟩ := routineSource_order a b ha hb order
  have data := softAlignedMagnitude_bounds a.sign b.sign _ _ _ _ lb rb
    (by omega) indices equal different
  have ai : max a.bexp 1 < 2 ^ 64 := by have := ha.1; change a.bexp ≤ 2047 at this; omega
  have bi : max b.bexp 1 < 2 ^ 64 := by have := hb.1; change b.bexp ≤ 2047 at this; omega
  have gap64 : max a.bexp 1 - max b.bexp 1 < 2 ^ 64 := by omega
  have leftShift (n : Nat) (bound : n < 2 ^ 53) :
      (BitVec.ofNat 64 n) <<< 3 = BitVec.ofNat 64 (n * 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), Nat.shiftLeft_eq]
    rfl
  have jam : floatShiftJamWord (BitVec.ofNat 64 (softSig b.bexp b.frac * 8))
      (BitVec.ofNat 64 (max a.bexp 1 - max b.bexp 1)) =
      BitVec.ofNat 64 (softShiftJamNat (softSig b.bexp b.frac * 8)
        (max a.bexp 1 - max b.bexp 1)) := by
    have result := congrArg (BitVec.ofNat 64) (floatShiftJamWord_nat
      (BitVec.ofNat 64 (softSig b.bexp b.frac * 8))
      (BitVec.ofNat 64 (max a.bexp 1 - max b.bexp 1)))
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show softSig b.bexp b.frac * 8 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt gap64] using result
  have signs : ((Runner.IR.bool a.sign ^^^ Runner.IR.bool b.sign) == 0) = (a.sign == b.sign) := by
    cases a.sign <;> cases b.sign <;> decide
  unfold routineDirectionalWord
  rw [asig, bsig, aindex, bindex, asign, bsign,
    BitVec.ofNat_sub_ofNat_of_le _ _ bi indices, leftShift _ lb, leftShift _ rb, jam, signs]
  unfold softAlignedMagnitude
  split
  · rw [BitVec.ofNat_add]
  · exact BitVec.ofNat_sub_ofNat_of_le _ _
      (by have := data.2.1; omega) data.2.1

#print axioms softAlignedMagnitude_bounds
#print axioms routineDirectionalWord_canonical
end Gabbro.Stage0.Senke
