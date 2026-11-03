/- Exact restoring division and its rational sticky certificate.
   Reuse the wide integer divider's Nat iteration, including its remainder. -/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Divide.Run
public import Stage0.Senke.Gleit.Sticky.Round
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma

/-- The same 128 restoring steps used by the emitted two-limb divider.
    The input may be wider than a word; neither quotient nor rest is guessed. -/
def softDivQR (n d : Nat) : Nat × Nat := dvIter 2 d n 128

/-- Restoring division computes the exact quotient and remainder together. -/
theorem softDivQR_model (n d : Nat) (dp : 0 < d) (nb : n < 2 ^ 128) :
    softDivQR n d = (n / d, n % d) := by
  obtain ⟨rest, quotient⟩ := dvIter_spec 2 d n dp nb (by decide) 128 (by decide)
  simp only [show 64 * 2 - 128 = 0 from rfl, Nat.pow_zero, Nat.div_one] at rest
  simp only [show 64 * 2 - 128 = 0 from rfl, Nat.pow_zero, Nat.div_one] at quotient
  have bound : n / d < 2 ^ 128 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) nb
  have q : (softDivQR n d).1 = n / d := by
    simpa only [softDivQR, Nat.mul_comm n, Nat.mul_add_mod,
      Nat.mod_eq_of_lt bound] using quotient
  exact Prod.ext q rest

/-- Three low bits retain guard, round and sticky information. -/
def softDivJam (n d : Nat) : Nat :=
  let qr := softDivQR n d
  qr.1 ||| if qr.2 = 0 then 0 else 1

/-- The certificate is rational: its denominator need not be a power of two.
    It is consumed by the shared nearest-even interval theorem. -/
theorem softDivJam_interval (n d : Nat) (dp : 0 < d) (nb : n < 2 ^ 128) :
    n = softDivJam n d * d ∨
      (softDivJam n d % 2 = 1 ∧
        (softDivJam n d - 1) * d < n ∧ n < (softDivJam n d + 1) * d) := by
  have division := Nat.div_add_mod' n d
  have rb := Nat.mod_lt n dp
  unfold softDivJam
  rw [softDivQR_model n d dp nb]
  dsimp only
  by_cases exactTail : n % d = 0
  · simp only [exactTail, ite_true, Nat.or_zero]
    exact Or.inl (by omega)
  · simp only [exactTail, ite_false]
    right
    have odd : ((n / d) ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.mpr (Or.inr rfl)
    have halves : ((n / d) ||| 1) / 2 = (n / d) / 2 := by
      rw [Nat.or_div_two]
      simp
    have qs := Nat.div_add_mod' (n / d) 2
    have js := Nat.div_add_mod' ((n / d) ||| 1) 2
    have qm := Nat.mod_lt (n / d) (by decide : 0 < 2)
    have lower := Nat.mul_le_mul_right d (show ((n / d) ||| 1) - 1 ≤ n / d by omega)
    have upper := Nat.mul_le_mul_right d (show n / d + 1 ≤ ((n / d) ||| 1) + 1 by omega)
    rw [Nat.add_mul, Nat.one_mul] at upper
    exact ⟨odd, by omega, by omega⟩

/-- An even boundary cannot be crossed by setting the quotient's low bit.
    This fixes the guard word's leading bit and prevents machine overflow. -/
theorem softDivJam_bounds (n d : Nat) (dp : 0 < d) (nb : n < 2 ^ 128)
    (lo : 2 ^ 55 * d ≤ n) (hi : n < 2 ^ 56 * d) :
    2 ^ 55 ≤ softDivJam n d ∧ softDivJam n d < 2 ^ 56 := by
  have qlo := (Nat.le_div_iff_mul_le dp).mpr lo
  have qhi := (Nat.div_lt_iff_lt_mul dp).mpr hi
  unfold softDivJam
  rw [softDivQR_model n d dp nb]
  dsimp only
  split
  · simp only [Nat.or_zero]
    exact ⟨qlo, qhi⟩
  · have half : ((n / d) ||| 1) / 2 = (n / d) / 2 := by
      rw [Nat.or_div_two]
      simp
    have odd : ((n / d) ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.mpr (Or.inr rfl)
    have qs := Nat.div_add_mod' (n / d) 2
    have js := Nat.div_add_mod' ((n / d) ||| 1) 2
    have qm := Nat.mod_lt (n / d) (by decide : 0 < 2)
    omega

/-- Normalized operands need 55 quotient places when the ratio is at least
    one, and 56 otherwise. Both choices yield exactly 56 retained bits. -/
theorem softDivGuard_bounds (a b : Nat) (al : 2 ^ 52 ≤ a) (ah : a < 2 ^ 53)
    (bl : 2 ^ 52 ≤ b) (bh : b < 2 ^ 53) :
    let k := if a < b then 56 else 55
    2 ^ 55 * b ≤ a * 2 ^ k ∧ a * 2 ^ k < 2 ^ 56 * b ∧ a * 2 ^ k < 2 ^ 128 := by
  dsimp only
  by_cases small : a < b
  · rw [if_pos small]
    have above := Nat.mul_le_mul_right (2 ^ 56) al
    have below := Nat.mul_lt_mul_of_pos_right bh (by decide : 0 < 2 ^ 55)
    have upper := Nat.mul_lt_mul_of_pos_right small (by decide : 0 < 2 ^ 56)
    have width := Nat.mul_lt_mul_of_pos_right ah (by decide : 0 < 2 ^ 56)
    omega
  · rw [if_neg small]
    have lower := Nat.mul_le_mul_right (2 ^ 55) (show b ≤ a by omega)
    have upper := Nat.mul_lt_mul_of_pos_right ah (by decide : 0 < 2 ^ 55)
    have bound := Nat.mul_le_mul_right (2 ^ 56) bl
    omega

/-- Inexact thirds retain a nonzero rest; exact division keeps an even tail. -/
theorem softDivQR_zeuge :
    softDivQR (2 ^ 108) (3 * 2 ^ 51) = (48038396025285290, 4503599627370496) ∧
    softDivJam (2 ^ 108) (3 * 2 ^ 51) = 48038396025285291 ∧
    softDivQR (2 ^ 107) (2 ^ 52) = (2 ^ 55, 0) := by
  decide +kernel

#print axioms softDivQR_model
#print axioms softDivJam_interval
#print axioms softDivJam_bounds
#print axioms softDivGuard_bounds
#print axioms softDivQR_zeuge
end Gabbro.Stage0.Senke
