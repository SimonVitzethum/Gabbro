/- Sticky alignment at the exact dyadic scales used by rounding replay. -/
module
public import Stage0.Senke.Gleit.Normal.Replay
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma

/-- Moving an exact power of two from the numerator into its scale leaves
    the rounded integer unchanged, including ties and positive scales. -/
theorem softRoundDyadic_mul_pow (n t : Nat) (e : Int) :
    softRoundDyadic (n * 2 ^ t) e = softRoundDyadic n (e + (t : Int)) := by
  unfold softRoundDyadic at 1
  rw [Nat.mul_assoc, ← Nat.pow_add]
  exact softRoundDyadic_scale n (t + e.toNat) (-e).toNat _ (by omega)

private theorem guardGrid (n gap k : Nat) (guard : 2 ≤ k) :
    softRoundDyadic n (-((gap + k : Nat) : Int)) =
      rundeInt (n / (4 * 2 ^ (k - 2) * 2 ^ gap))
        (n % (4 * 2 ^ (k - 2) * 2 ^ gap)) (4 * 2 ^ (k - 2) * 2 ^ gap) := by
  have grid : (2 : Nat) ^ k = 4 * 2 ^ (k - 2) := by
    calc
      2 ^ k = 2 ^ (2 + (k - 2)) := by congr 1; omega
      _ = 4 * 2 ^ (k - 2) := by rw [Nat.pow_add]; rfl
  have scale : (2 : Nat) ^ (gap + k) = 4 * 2 ^ (k - 2) * 2 ^ gap := by
    rw [Nat.add_comm gap k, Nat.pow_add, grid]
  have result := softRoundDyadic_scale n 0 (gap + k)
    (-((gap + k : Nat) : Int)) (by omega)
  simpa only [Nat.pow_zero, Nat.mul_one, scale] using result.symm

/-- At least two retained low bits keep sticky information below every
    halfway boundary. The exact numerator may be arbitrarily wide. -/
theorem softRoundDyadic_shiftJam (small gap k : Nat) (guard : 2 ≤ k) :
    softRoundDyadic small (-((gap + k : Nat) : Int)) =
      softRoundDyadic (softShiftJamNat small gap) (-(k : Int)) := by
  rw [guardGrid small gap k guard]
  have right := guardGrid (softShiftJamNat small gap) 0 k guard
  simp only [Nat.zero_add, Nat.pow_zero, Nat.mul_one] at right
  rw [right]
  rcases softShiftJamNat_interval small gap with exactValue | ⟨odd, lo, hi⟩
  · exact softRound_scaled _ _ _ _ (Nat.two_pow_pos _)
      (by have := Nat.two_pow_pos (k - 2); omega) exactValue.2
  · exact softRound_odd_interval _ _ _ _ (Nat.two_pow_pos _) (Nat.two_pow_pos _) odd lo hi

/-- Sticky alignment followed by the replay rounding grid agrees with
    rounding the exact same-sign source sum at its original scale. -/
theorem softRoundDyadic_aligned_add (large small gap k : Nat)
    (even : large % 2 = 0) (guard : 2 ≤ k) :
    softRoundDyadic (large * 2 ^ gap + small) (-((gap + k : Nat) : Int)) =
      softRoundDyadic (large + softShiftJamNat small gap) (-(k : Int)) := by
  rw [guardGrid _ gap k guard]
  have right := guardGrid (large + softShiftJamNat small gap) 0 k guard
  simp only [Nat.zero_add, Nat.pow_zero, Nat.mul_one] at right
  rw [right]
  exact softRoundNat_aligned_add large small gap even _ (Nat.two_pow_pos _)

/-- The discarded nonzero tail is subtracted on the opposite-sign path.
    Both ordering premises prevent saturated natural subtraction. -/
theorem softRoundDyadic_aligned_sub (large small gap k : Nat)
    (even : large % 2 = 0) (ordered : softShiftJamNat small gap ≤ large)
    (cover : small ≤ large * 2 ^ gap) (guard : 2 ≤ k) :
    softRoundDyadic (large * 2 ^ gap - small) (-((gap + k : Nat) : Int)) =
      softRoundDyadic (large - softShiftJamNat small gap) (-(k : Int)) := by
  rw [guardGrid _ gap k guard]
  have right := guardGrid (large - softShiftJamNat small gap) 0 k guard
  simp only [Nat.zero_add, Nat.pow_zero, Nat.mul_one] at right
  rw [right]
  exact softRoundNat_aligned_sub large small gap even ordered cover _ (Nat.two_pow_pos _)

/-- Original and left-normalized precisions, a full-word alignment gap and
    exact tie parity all satisfy the same replay equalities. -/
theorem softRoundDyadic_aligned_zeuge :
    softRoundDyadic (16 * 2 ^ 3 + 9) (-6) =
      softRoundDyadic (16 + softShiftJamNat 9 3) (-3) ∧
    softRoundDyadic (16 * 2 ^ 3 - 9) (-5) =
      softRoundDyadic (16 - softShiftJamNat 9 3) (-2) ∧
    softRoundDyadic (2 ^ 55 * 2 ^ 1022 + 8) (-1025) =
      softRoundDyadic (2 ^ 55 + softShiftJamNat 8 1022) (-3) ∧
    softRoundDyadic (16 * 2 ^ 3 + 32) (-6) = 2 ∧
    softRoundDyadic (24 * 2 ^ 3 + 32) (-6) = 4 := by
  decide +kernel

#print axioms softRoundDyadic_mul_pow
#print axioms softRoundDyadic_shiftJam
#print axioms softRoundDyadic_aligned_add
#print axioms softRoundDyadic_aligned_sub
#print axioms softRoundDyadic_aligned_zeuge
end Gabbro.Stage0.Senke
