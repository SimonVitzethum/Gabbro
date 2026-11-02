/- Nearest-even rounding from an odd jammed word and its exact interval. -/
module
public import Stage0.Senke.Gleit.Runde
public import Mathlib.Tactic.Linarith
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

/-- An odd jammed magnitude is strictly between adjacent even endpoints.
    A rounding grid divisible by four has an even midpoint, so every exact
    rational in this open interval makes the same nearest-even decision.
    The denominator is unbounded: no machine-width bound hides a large gap. -/
theorem softRound_odd_interval (j n d t : Nat) (dp : 0 < d) (tp : 0 < t)
    (odd : j % 2 = 1) (lo : (j - 1) * d < n) (hi : n < (j + 1) * d) :
    rundeInt (n / (4 * t * d)) (n % (4 * t * d)) (4 * t * d) =
      rundeInt (j / (4 * t)) (j % (4 * t)) (4 * t) := by
  have denp : 0 < 4 * t := by omega
  have division := Nat.div_add_mod' j (4 * t)
  have remBound := Nat.mod_lt j denp
  have remOdd : (j % (4 * t)) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd j (show 2 ∣ 4 * t from ⟨2 * t, by omega⟩)]
    exact odd
  have remPositive : 1 ≤ j % (4 * t) := by omega
  have lower : (j / (4 * t)) * (4 * t) ≤ j - 1 := by omega
  have upper : j + 1 ≤ (j / (4 * t) + 1) * (4 * t) := by nlinarith
  have lowerScaled := Nat.mul_le_mul_right d lower
  have upperScaled := Nat.mul_le_mul_right d upper
  have quotient : n / (4 * t * d) = j / (4 * t) :=
    Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  have exactN := Nat.div_add_mod' n (4 * t * d)
  rw [quotient] at exactN ⊢
  by_cases below : j % (4 * t) < 2 * t
  · have midpoint : j + 1 ≤ (j / (4 * t)) * (4 * t) + 2 * t := by omega
    have scaled := Nat.mul_le_mul_right d midpoint
    rw [rundeInt_fall _ _ _ (by nlinarith : 2 * (n % (4 * t * d)) < 4 * t * d),
      rundeInt_fall _ _ _ (by omega : 2 * (j % (4 * t)) < 4 * t)]
  · have above : 2 * t < j % (4 * t) := by omega
    have midpoint : (j / (4 * t)) * (4 * t) + 2 * t ≤ j - 1 := by omega
    have scaled := Nat.mul_le_mul_right d midpoint
    rw [rundeInt_steig _ _ _ (by nlinarith : 4 * t * d < 2 * (n % (4 * t * d))),
      rundeInt_steig _ _ _ (by omega : 4 * t < 2 * (j % (4 * t)))]

/-- An exact rescaling retains all ties, including both quotient parities. -/
theorem softRound_scaled (j n d t : Nat) (dp : 0 < d) (tp : 0 < t)
    (exactValue : n = j * d) :
    rundeInt (n / (t * d)) (n % (t * d)) (t * d) =
      rundeInt (j / t) (j % t) t := by
  apply softRound_congr _ _ _ _ _ _ (Nat.mod_lt _ (Nat.mul_pos tp dp)) (Nat.mod_lt _ tp)
  rw [Nat.div_add_mod', Nat.div_add_mod', exactValue]
  ring

/-- The existing word sticky lemma yields the complete rounding certificate:
    an exact quotient, or an odd word surrounding the original rational.
    The proof keeps the remainder rather than equating a sticky bit to it. -/
theorem floatShiftJamWord_interval (a k : Runner.W) :
    let j := (floatShiftJamWord a k).toNat
    let d := 2 ^ k.toNat
    (a.toNat % d = 0 ∧ a.toNat = j * d) ∨
      (j % 2 = 1 ∧ (j - 1) * d < a.toNat ∧ a.toNat < (j + 1) * d) := by
  dsimp only
  have model := floatShiftJamWord_model a k
  have toNat := congrArg BitVec.toNat model
  simp only [BitVec.toNat_or, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at toNat
  have dp : 0 < (2 : Nat) ^ k.toNat := Nat.two_pow_pos _
  have division := Nat.div_add_mod' a.toNat (2 ^ k.toNat)
  have remBound := Nat.mod_lt a.toNat dp
  by_cases exactTail : a.toNat % 2 ^ k.toNat = 0
  · left
    have quotient : (floatShiftJamWord a k).toNat = a.toNat / 2 ^ k.toNat := by
      simpa only [exactTail, ne_eq, not_true_eq_false, decide_false,
        Runner.IR.bool, Bool.false_eq_true, ite_false, BitVec.toNat_zero, Nat.or_zero] using toNat
    exact ⟨exactTail, by rw [quotient]; omega⟩
  · right
    have jam : (floatShiftJamWord a k).toNat = (a.toNat / 2 ^ k.toNat) ||| 1 := by
      simpa only [exactTail, ne_eq, not_false_eq_true, decide_true,
        Runner.IR.bool, ite_true] using toNat
    have odd : (floatShiftJamWord a k).toNat % 2 = 1 := by
      rw [jam, Nat.or_mod_two_eq_one]
      exact Or.inr rfl
    have halves : (floatShiftJamWord a k).toNat / 2 = (a.toNat / 2 ^ k.toNat) / 2 := by
      rw [jam, Nat.or_div_two]
      simp
    have quotientSplit := Nat.div_add_mod' (a.toNat / 2 ^ k.toNat) 2
    have quotientMod := Nat.mod_lt (a.toNat / 2 ^ k.toNat) (by decide : 0 < 2)
    have jamSplit := Nat.div_add_mod' (floatShiftJamWord a k).toNat 2
    have lower : (floatShiftJamWord a k).toNat - 1 ≤ a.toNat / 2 ^ k.toNat := by omega
    have upper : a.toNat / 2 ^ k.toNat + 1 ≤ (floatShiftJamWord a k).toNat + 1 := by omega
    have lowScaled := Nat.mul_le_mul_right (2 ^ k.toNat) lower
    have highScaled := Nat.mul_le_mul_right (2 ^ k.toNat) upper
    exact ⟨odd, by nlinarith, by nlinarith⟩

/-- Right-shift-with-sticky followed by rounding retains the kernel integer
    decision for any gap, including gaps exceeding the entire word width.
    At least two low bits remain before the rounding grid. -/
theorem softRound_shiftJam (a k : Runner.W) (t : Nat) (tp : 0 < t) :
    rundeInt (a.toNat / (4 * t * 2 ^ k.toNat))
      (a.toNat % (4 * t * 2 ^ k.toNat)) (4 * t * 2 ^ k.toNat) =
      rundeInt ((floatShiftJamWord a k).toNat / (4 * t))
        ((floatShiftJamWord a k).toNat % (4 * t)) (4 * t) := by
  rcases floatShiftJamWord_interval a k with exactValue | ⟨odd, lo, hi⟩
  · exact softRound_scaled _ _ _ _ (Nat.two_pow_pos _) (by omega) exactValue.2
  · exact softRound_odd_interval _ _ _ _ (Nat.two_pow_pos _) tp odd lo hi

/-- Beyond the operand's leading bit, the aligned value is precisely its
    nonzero sticky flag. This uses the remainder characterization above. -/
theorem floatShiftJamWord_large (a k : Runner.W) (large : a.toNat < 2 ^ k.toNat) :
    floatShiftJamWord a k = Runner.IR.bool (decide (a.toNat ≠ 0)) := by
  rw [floatShiftJamWord_model]
  have zero : a >>> k.toNat = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_zero]
    exact Nat.div_eq_of_lt large
  rw [zero, Nat.mod_eq_of_lt large, BitVec.zero_or]

theorem softRound_shiftJam_zeuge :
    floatShiftJamWord 9 3 = 1 ∧
    rundeInt (9 / (8 * 8)) (9 % (8 * 8)) (8 * 8) =
      rundeInt ((floatShiftJamWord 9 3).toNat / 8) ((floatShiftJamWord 9 3).toNat % 8) 8 ∧
    floatShiftJamWord (BitVec.ofNat 64 (2 ^ 55 - 8)) 1022 = 1 ∧
    rundeInt (5 / 4) (5 % 4) 4 = 1 ∧
    rundeInt (7 / 4) (7 % 4) 4 = 2 := by
  decide +kernel

#print axioms softRound_odd_interval
#print axioms softRound_scaled
#print axioms floatShiftJamWord_interval
#print axioms softRound_shiftJam
#print axioms floatShiftJamWord_large
#print axioms softRound_shiftJam_zeuge
end Gabbro.Stage0.Senke
