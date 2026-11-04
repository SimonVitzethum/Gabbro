/- Rational scaling for division, keeping numerator and denominator in Nat. -/
module
public import Stage0.Senke.Gleit.Div.Model
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma

/-- Move powers between the two sides of a comparison without truncation. -/
theorem softDiv_power_compare (a b u v x y : Nat) (balance : u + x = v + y) :
    a * 2 ^ u ≤ b * 2 ^ v ↔ a * 2 ^ y ≤ b * 2 ^ x := by
  have left : a * 2 ^ u ≤ b * 2 ^ v ↔
      a * 2 ^ (u + x) ≤ b * 2 ^ (v + x) := by
    rw [Nat.pow_add, Nat.pow_add, ← Nat.mul_assoc, ← Nat.mul_assoc]
    exact (Nat.mul_le_mul_right_iff (Nat.two_pow_pos x)).symm
  have right : a * 2 ^ y ≤ b * 2 ^ x ↔
      a * 2 ^ (y + v) ≤ b * 2 ^ (x + v) := by
    rw [Nat.pow_add, Nat.pow_add, ← Nat.mul_assoc, ← Nat.mul_assoc]
    exact (Nat.mul_le_mul_right_iff (Nat.two_pow_pos v)).symm
  rw [left, right, balance, Nat.add_comm v y, Nat.add_comm v x]

/-- Rounding of a rational at an arbitrary binary scale. -/
def softRoundRatio (n d : Nat) (scale : Int) : Nat :=
  rundeInt ((n * 2 ^ scale.toNat) / (d * 2 ^ (-scale).toNat))
    ((n * 2 ^ scale.toNat) % (d * 2 ^ (-scale).toNat)) (d * 2 ^ (-scale).toNat)

/-- Equivalent power distributions have the same exact rounding decision. -/
theorem softRoundRatio_power (n d t₁ j₁ t₂ j₂ : Nat) (dp : 0 < d)
    (scale : t₁ + j₂ = t₂ + j₁) :
    rundeInt ((n * 2 ^ t₁) / (d * 2 ^ j₁))
      ((n * 2 ^ t₁) % (d * 2 ^ j₁)) (d * 2 ^ j₁) =
    rundeInt ((n * 2 ^ t₂) / (d * 2 ^ j₂))
      ((n * 2 ^ t₂) % (d * 2 ^ j₂)) (d * 2 ^ j₂) := by
  apply softRound_congr _ _ _ _ _ _
    (Nat.mod_lt _ (Nat.mul_pos dp (Nat.two_pow_pos _)))
    (Nat.mod_lt _ (Nat.mul_pos dp (Nat.two_pow_pos _)))
  rw [Nat.div_add_mod', Nat.div_add_mod']
  simp only [Nat.mul_assoc, Nat.mul_left_comm (2 ^ t₁) d,
    Nat.mul_left_comm (2 ^ t₂) d, ← Nat.pow_add, scale]

theorem softRoundRatio_scale (n d t j : Nat) (dp : 0 < d) (e : Int)
    (scale : e = (t : Int) - (j : Int)) :
    rundeInt ((n * 2 ^ t) / (d * 2 ^ j))
      ((n * 2 ^ t) % (d * 2 ^ j)) (d * 2 ^ j) = softRoundRatio n d e :=
  softRoundRatio_power n d t j e.toNat (-e).toNat dp (by omega)

/-- Operand normalization changes only the rational scale. -/
theorem softRoundRatio_normalize (a b ca cb t j : Nat) (bp : 0 < b) (e : Int)
    (scale : e = (t : Int) - (j : Int) - (ca : Int) + (cb : Int)) :
    rundeInt ((a * 2 ^ t) / (b * 2 ^ j))
      ((a * 2 ^ t) % (b * 2 ^ j)) (b * 2 ^ j) =
      softRoundRatio (a * 2 ^ ca) (b * 2 ^ cb) e := by
  unfold softRoundRatio
  simp only [Nat.mul_assoc, ← Nat.pow_add]
  apply softRoundRatio_power a b t j (ca + e.toNat) (cb + (-e).toNat) bp
  omega

/-- The kernel exponent search uses the same comparison as the normalized
    divider. The two significands need not have had equal source bit lengths. -/
theorem softDiv_exponent (a b ca cb t j : Nat) (ap : 0 < a) (bp : 0 < b)
    (abits : bitlen a + ca = 53) (bbits : bitlen b + cb = 53) :
    findeExp (a * 2 ^ t) (b * 2 ^ j) =
      (t : Int) - (j : Int) - (ca : Int) + (cb : Int) -
        (if a * 2 ^ ca < b * 2 ^ cb then 1 else 0) := by
  let e : Int := (t : Int) - j - ca + cb
  have position : ((bitlen a + t : Nat) : Int) - ((bitlen b + j : Nat) : Int) = e := by
    dsimp only [e]
    omega
  unfold findeExp
  rw [bitlen_mul_pow2 a t ap, bitlen_mul_pow2 b j bp, position]
  unfold findeExpBei
  by_cases ep : 0 ≤ e
  · rw [if_pos ep]
    have test : b * 2 ^ j * 2 ^ e.toNat ≤ a * 2 ^ t ↔ b * 2 ^ cb ≤ a * 2 ^ ca := by
      rw [Nat.mul_assoc, ← Nat.pow_add]
      exact softDiv_power_compare b a (j + e.toNat) t ca cb (by dsimp only [e] at ep ⊢; omega)
    simp only [test]
    by_cases small : a * 2 ^ ca < b * 2 ^ cb
    · rw [if_neg (by omega), if_pos small]
    · rw [if_pos (by omega), if_neg small]
      simp only [e, sub_zero]
  · rw [if_neg ep]
    have test : b * 2 ^ j ≤ a * 2 ^ t * 2 ^ (-e).toNat ↔ b * 2 ^ cb ≤ a * 2 ^ ca := by
      rw [Nat.mul_assoc, ← Nat.pow_add]
      exact softDiv_power_compare b a j (t + (-e).toNat) ca cb (by dsimp only [e] at ep ⊢; omega)
    simp only [test]
    by_cases small : a * 2 ^ ca < b * 2 ^ cb
    · rw [if_neg (by omega), if_pos small]
    · rw [if_pos (by omega), if_neg small]
      simp only [e, sub_zero]

/-- Both directions of exponent subtraction instantiate the same search,
    including the one-place correction for a significand ratio below one. -/
theorem softDiv_exponent_zeuge :
    findeExp ((2 ^ 52) * 2 ^ 7) ((3 * 2 ^ 51) * 2 ^ 2) = 4 ∧
    findeExp ((3 * 2 ^ 51) * 2 ^ 2) ((2 ^ 52) * 2 ^ 7) = -5 := by
  decide +kernel

#print axioms softDiv_power_compare
#print axioms softRoundRatio_power
#print axioms softRoundRatio_normalize
#print axioms softDiv_exponent
#print axioms softDiv_exponent_zeuge
end Gabbro.Stage0.Senke
