/- Exact retained-bit transport for the toolchain's integer conversion. -/
module
public import Init.Data.Float
import Init.Data.Nat.Mod
import Init.Data.Nat.Bitwise.Lemmas
@[expose] public section

namespace Gabbro.Grammatik.NativeFloat
open Float.Model.UnpackedFloat

private theorem mod_mul_zero (n a b : Nat) (positive : 0 < a) :
    n % (a * b) = 0 ↔ n % a = 0 ∧ n / a % b = 0 := by
  rw [Nat.mod_mul, Nat.add_eq_zero_iff, Nat.mul_eq_zero]
  simp [Nat.ne_of_gt positive]

private theorem sticky_step (m n : Nat) :
    ((m / 2 ^ n % 2 != 0) || (m % 2 ^ n != 0)) = (m % 2 ^ (n + 1) != 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true_iff, bne_iff_ne]
  rw [Nat.pow_succ]
  have zeros := mod_mul_zero m (2 ^ n) 2 (Nat.two_pow_pos n)
  constructor
  · intro h zero
    rcases zeros.mp zero with ⟨remainder, quotient⟩
    rcases h with h | h
    · exact h quotient
    · exact h remainder
  · intro h
    by_cases remainder : m % 2 ^ n = 0
    · exact Or.inl (fun quotient => h (zeros.mpr ⟨remainder, quotient⟩))
    · exact Or.inr remainder

private theorem exact_shift_bits (m n : Nat) :
    Nat.repeat ExtendedMantissa.shiftRightOne (n + 1) ⟨m, false, false⟩ =
      ⟨m / 2 ^ (n + 1), m / 2 ^ n % 2 != 0, m % 2 ^ n != 0⟩ := by
  induction n with
  | zero => simp [Nat.repeat, ExtendedMantissa.shiftRightOne]
  | succ n ih =>
      rw [Nat.repeat, ih]
      change ⟨m / 2 ^ (n + 1) / 2, m / 2 ^ (n + 1) % 2 != 0,
        (m / 2 ^ n % 2 != 0) || (m % 2 ^ n != 0)⟩ = _
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ, sticky_step]

private theorem jam_div (n k j : Nat) (room : 1 < 2 ^ j) :
    ((n / 2 ^ k) ||| (if n % 2 ^ k = 0 then 0 else 1)) / 2 ^ j = n / 2 ^ (k + j) := by
  rw [Nat.or_div_two_pow]
  have tiny : (if n % 2 ^ k = 0 then 0 else 1) / 2 ^ j = 0 := by
    apply Nat.div_eq_of_lt
    split <;> omega
  rw [tiny, Nat.or_zero, Nat.div_div_eq_div_mul, Nat.pow_add]

private theorem jam_low_zero (n k : Nat) :
    (((n / 2 ^ k) ||| (if n % 2 ^ k = 0 then 0 else 1)) % 4 = 0) ↔
      n % 2 ^ (k + 2) = 0 := by
  change (((n / 2 ^ k) ||| (if n % 2 ^ k = 0 then 0 else 1)) % 2 ^ 2 = 0) ↔ _
  rw [Nat.or_mod_two_pow, Nat.or_eq_zero_iff]
  have low : (if n % 2 ^ k = 0 then 0 else 1) % 2 ^ 2 = 0 ↔ n % 2 ^ k = 0 := by
    split <;> simp_all
  rw [low, Nat.pow_add, mod_mul_zero n (2 ^ k) (2 ^ 2) (Nat.two_pow_pos k)]
  exact and_comm

/-- Retaining 56 bits with an odd sticky completion preserves exactly the
    native mantissa, round bit and sticky bit after the final three shifts.
    This is a proof about the existing toolchain state, not another evaluator. -/
theorem jam56_shift (n k : Nat) :
    let g := (n >>> k) ||| (if n % 2 ^ k = 0 then 0 else 1)
    (⟨g, false, false⟩ : ExtendedMantissa) >>> 3 =
      (⟨n, false, false⟩ : ExtendedMantissa) >>> (k + 3) := by
  dsimp only
  rw [Nat.shiftRight_eq_div_pow]
  change Nat.repeat ExtendedMantissa.shiftRightOne 3
      ⟨(n / 2 ^ k) ||| (if n % 2 ^ k = 0 then 0 else 1), false, false⟩ =
    Nat.repeat ExtendedMantissa.shiftRightOne (k + 3) ⟨n, false, false⟩
  rw [exact_shift_bits _ 2, show k + 3 = (k + 2) + 1 by omega, exact_shift_bits n (k + 2)]
  congr 1
  · exact jam_div n k 3 (by decide)
  · rw [jam_div n k 2 (by decide)]
  · apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne]
    exact not_congr (jam_low_zero n k)

end Gabbro.Grammatik.NativeFloat
