/- Arbitrary integer magnitudes use the existing sticky rounding replay. -/
module
public import Stage0.Senke.Gleit.Normal.GuardModel
public import Stage0.Senke.Gleit.Normal.Interval
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

/-- Three guard bits remain after compression; no rounding occurs here. -/
def integerFloatShift (n : Nat) : Nat := n.log2 - 55

def integerFloatIndex (n : Nat) : Nat := min 2047 (integerFloatShift n + 1078)

theorem integerFloat_bitlen (n : Nat) (positive : 0 < n) :
    bitlen n = n.log2 + 1 := by
  have bounds := (Nat.log2_eq_iff (by omega : n ≠ 0)).mp rfl
  exact bitlen_unique n (n.log2 + 1) (by simpa using bounds.1) bounds.2 positive

/-- Both the quotient and its odd sticky completion fit the retained span. -/
theorem integerFloat_bounds (n : Nat) :
    n / 2 ^ integerFloatShift n < 2 ^ 56 ∧
      softShiftJamNat n (integerFloatShift n) < 2 ^ 56 := by
  have quotient : n / 2 ^ integerFloatShift n < 2 ^ 56 := by
    by_cases zero : n = 0
    · subst n; decide
    · have bounds := (Nat.log2_eq_iff zero).mp rfl
      have exponent : n.log2 + 1 ≤ 56 + integerFloatShift n := by
        unfold integerFloatShift; omega
      have power : 2 ^ (n.log2 + 1) ≤ 2 ^ 56 * 2 ^ integerFloatShift n := by
        rw [← Nat.pow_add]
        exact Nat.pow_le_pow_right (by decide : 0 < 2) exponent
      exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by omega)
  refine ⟨quotient, ?_⟩
  unfold softShiftJamNat
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.or_lt_two_pow quotient
  split <;> decide

theorem integerFloat_normalized (n : Nat) (large : 2 ^ 55 ≤ n) :
    2 ^ 55 ≤ softShiftJamNat n (integerFloatShift n) ∧
      55 ≤ n.log2 := by
  have positive : 0 < n := by omega
  have bounds := (Nat.log2_eq_iff (by omega : n ≠ 0)).mp rfl
  have log : 55 ≤ n.log2 := by
    apply Classical.byContradiction
    intro h
    have power := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show n.log2 + 1 ≤ 55 by omega)
    omega
  have power : 2 ^ n.log2 = 2 ^ 55 * 2 ^ integerFloatShift n := by
    rw [← Nat.pow_add]
    congr 1
    unfold integerFloatShift
    omega
  have quotient : 2 ^ 55 ≤ n / 2 ^ integerFloatShift n :=
    (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by rw [← power]; exact bounds.1)
  have retained : n / 2 ^ integerFloatShift n ≤ softShiftJamNat n (integerFloatShift n) := by
    unfold softShiftJamNat
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.left_le_or
  exact ⟨by omega, log⟩

/-- Saturating the exponent index only affects values already rounding to
    infinity. The complete magnitude is compressed once with a sticky bit,
    then passed to precisely the adder/multiplier guard-rounding kernel. -/
theorem integerFloat_round (z : Int) (large : 2 ^ 55 ≤ z.natAbs) :
    routineRoundPackWord (Runner.IR.bool (decide (z < 0)))
      (BitVec.ofNat 64 (integerFloatIndex z.natAbs))
      (BitVec.ofNat 64 (softShiftJamNat z.natAbs (integerFloatShift z.natAbs))) =
      BitVec.ofNat 64 (zuBits f64 (ofInt f64 z)) := by
  let n := z.natAbs
  let k := integerFloatShift n
  let j := softShiftJamNat n k
  change routineRoundPackWord (Runner.IR.bool (decide (z < 0)))
    (BitVec.ofNat 64 (integerFloatIndex n)) (BitVec.ofNat 64 j) = _
  have largeN : 2 ^ 55 ≤ n := large
  have normalized : 2 ^ 55 ≤ j ∧ 55 ≤ n.log2 := integerFloat_normalized n largeN
  have bounded : n / 2 ^ k < 2 ^ 56 ∧ j < 2 ^ 56 := integerFloat_bounds n
  have bits : bitlen j = 56 := bitlen_unique j 56 normalized.1 bounded.2 (by omega)
  have nonzero : z ≠ 0 := by intro hz; simp [hz, n] at large
  have signed : (if decide (z < 0) then -(n : Int) else (n : Int)) = z := by
    by_cases negative : z < 0
    · simp only [negative, decide_true, ite_true, n]
      exact (Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt negative)).symm
    · simp only [negative, decide_false, Bool.false_eq_true, ite_false, n]
      exact (Int.eq_natAbs_of_nonneg (by omega)).symm
  have certificate : n = j * 2 ^ k ∨
      (j % 2 = 1 ∧ (j - 1) * 2 ^ k < n ∧ n < (j + 1) * 2 ^ k) := by
    rcases softShiftJamNat_interval n k with h | h
    · exact Or.inl h.2
    · exact Or.inr h
  by_cases fits : k + 1078 ≤ 2047
  · have index : integerFloatIndex n = k + 1078 := Nat.min_eq_right fits
    rw [index, routineRoundPackWord_exact _ _ _ (by omega) fits
      (by omega) bounded.2 (Or.inl normalized.1)]
    apply congrArg (fun a : GFloat => BitVec.ofNat 64 (zuBits f64 a))
    have interval := softRound_signed_interval (decide (z < 0)) j n k (k : Int)
      (by omega) (by rw [bits]; change (-1022 : Int) ≤ _; omega) certificate
    simp only [sub_self, signed] at interval
    have scale : ((k + 1078 : Nat) : Int) - 1078 = (k : Int) := by omega
    simpa only [scale, ofInt] using interval.symm
  · have index : integerFloatIndex n = 2047 := Nat.min_eq_left (by omega)
    have overflow : (f64.emax : Int) < (bitlen n : Int) - 1 := by
      rw [integerFloat_bitlen n (by omega)]
      change (1023 : Int) < _
      dsimp only [k, integerFloatShift] at fits
      omega
    have replay := softRound_replay_all z 0 nonzero
    dsimp only at replay
    rw [show 0 + (bitlen z.natAbs : Int) - 1 = (bitlen n : Int) - 1 by simp only [n, zero_add],
      if_pos overflow] at replay
    have rounded : ofInt f64 z = ⟨decide (z < 0), 2047, 0⟩ := by
      simpa only [ofInt, show f64.bexpMax = 2047 from rfl] using replay
    rw [rounded, index, routineRoundPackWord_model (decide (z < 0)) 2047 j (by decide) bounded.2]
    have exp : ¬ softCarryExp 2047 (rundeInt (j / 8) (j % 8) 8) < 2047 := by
      unfold softCarryExp; split <;> omega
    dsimp only
    simp only [if_neg exp]

/-- Wide halfway cases retain the entire discarded tail, in both signs. -/
theorem integerFloat_round_zeuge :
    ∀ z ∈ [2 ^ 127 + 2 ^ 74, 2 ^ 127 + 2 ^ 74 + 1,
      -(2 ^ 127 + 2 ^ 74 + 1), 2 ^ 1024],
      2 ^ 55 ≤ z.natAbs ∧
      routineRoundPackWord (Runner.IR.bool (decide (z < 0)))
        (BitVec.ofNat 64 (integerFloatIndex z.natAbs))
        (BitVec.ofNat 64 (softShiftJamNat z.natAbs (integerFloatShift z.natAbs))) =
        BitVec.ofNat 64 (zuBits f64 (ofInt f64 z)) := by
  intro z member
  have large : 2 ^ 55 ≤ z.natAbs := by
    have power127 : (2 : Nat) ^ 55 ≤ 2 ^ 127 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 55 ≤ 127)
    have power1024 : (2 : Nat) ^ 55 ≤ 2 ^ 1024 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 55 ≤ 1024)
    have nonnegative127 : (0 : Int) ≤ 2 ^ 127 := Int.pow_nonneg (by decide)
    have nonnegative74 : (0 : Int) ≤ 2 ^ 74 := Int.pow_nonneg (by decide)
    have sumMagnitude : (2 ^ 127 + 2 ^ 74 : Int).natAbs = (2 : Nat) ^ 127 + 2 ^ 74 := by
      simp only [Int.natAbs_add_of_nonneg nonnegative127 nonnegative74, Int.natAbs_pow,
        show (2 : Int).natAbs = 2 from rfl]
    have bumpedMagnitude : (2 ^ 127 + 2 ^ 74 + 1 : Int).natAbs =
        (2 : Nat) ^ 127 + 2 ^ 74 + 1 := by
      simp only [Int.natAbs_add_of_nonneg (Int.add_nonneg nonnegative127 nonnegative74)
        (by decide : (0 : Int) ≤ 1), sumMagnitude, show (1 : Int).natAbs = 1 from rfl]
    have sumBound := power127.trans (Nat.le_add_right (2 ^ 127) (2 ^ 74))
    have bumpedBound := sumBound.trans (Nat.le_add_right _ 1)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · simpa only [sumMagnitude] using sumBound
    · simpa only [bumpedMagnitude] using bumpedBound
    · simpa only [Int.natAbs_neg, bumpedMagnitude] using bumpedBound
    · simpa only [Int.natAbs_pow, show (2 : Int).natAbs = 2 from rfl] using power1024
  exact ⟨large, integerFloat_round z large⟩

#print axioms integerFloat_round
#print axioms integerFloat_round_zeuge
end Gabbro.Stage0.Senke
