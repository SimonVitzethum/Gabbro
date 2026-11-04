/- Complete integer magnitudes retain the existing quotient and sticky normalization. -/
module
public import Stage0.Senke.Gleit.Native.Values
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Three guard bits remain after compression; no rounding occurs here. -/
def integerFloatShift (n : Nat) : Nat := n.log2 - 55

def integerFloatIndex (n : Nat) : Nat := min 2047 (integerFloatShift n + 1078)

/-- The existing complete integer normalization retains its quotient and exact
    nonzero-tail flag. CPU conversion performs the floating rounding. -/
def integerFloatJam (n k : Nat) : Nat :=
  (n >>> k) ||| if n % 2 ^ k = 0 then 0 else 1

/-- Both the quotient and its odd sticky completion fit the retained span. -/
theorem integerFloat_bounds (n : Nat) :
    n / 2 ^ integerFloatShift n < 2 ^ 56 ∧
      integerFloatJam n (integerFloatShift n) < 2 ^ 56 := by
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
  unfold integerFloatJam
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.or_lt_two_pow quotient
  split <;> decide

theorem integerFloat_normalized (n : Nat) (large : 2 ^ 55 ≤ n) :
    2 ^ 55 ≤ integerFloatJam n (integerFloatShift n) ∧
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
  have retained : n / 2 ^ integerFloatShift n ≤ integerFloatJam n (integerFloatShift n) := by
    unfold integerFloatJam
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.left_le_or
  exact ⟨by omega, log⟩

end Gabbro.Stage0.Senke
