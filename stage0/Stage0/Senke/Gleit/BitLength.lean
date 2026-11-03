/- Bit lengths and the kernel exponent position for software binary64 addition.

    `bitlen_unique` pins `bitlen` from its two-sided bound; `bitlen_pow2`
    and `bitlen_mul_pow2` fix powers of two and scaled significands.
    `findeExp_scaled` positions the kernel `findeExp` of a scaled
    power-of-two denominator from the `bitlen` bounds alone: both
    `findeExpBei` branches decide for `E0`. The rounding replay in
    `Runde.lean` builds on these. -/
module
public import Grammatik.Bausteine.Gleitkomma.GleitkommaBits
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
open Gleitkomma

/-- Uniqueness of the bit length: `2 ^ (b - 1) ≤ n < 2 ^ b` pins `bitlen`. -/
theorem bitlen_unique (n b : Nat) (hlo : 2 ^ (b - 1) ≤ n) (hhi : n < 2 ^ b)
    (hn : 0 < n) : bitlen n = b := by
  have hob := bitlen_obere n
  have hun := bitlen_untere n (by omega : n ≠ 0)
  refine Classical.byContradiction fun hne => ?_
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have h1 := Nat.pow_le_pow_right (show 0 < 2 by decide) (show bitlen n ≤ b - 1 by omega)
    omega
  · have h1 := Nat.pow_le_pow_right (show 0 < 2 by decide) (show b + 1 ≤ bitlen n by omega)
    have h2 : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ, Nat.mul_comm]
    omega

/-- Powers of two have exact bit length. -/
theorem bitlen_pow2 (j : Nat) : bitlen (2 ^ j) = j + 1 := by
  apply bitlen_unique
  · have : j + 1 - 1 = j := by omega
    rw [this]
    exact Nat.le_refl _
  · exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr (by omega)
  · exact Nat.pow_pos (by decide)

/-- Scaling by a power of two shifts the bit length. -/
theorem bitlen_mul_pow2 (S t : Nat) (hS : 0 < S) :
    bitlen (S * 2 ^ t) = bitlen S + t := by
  have hob := bitlen_obere S
  have hun := bitlen_untere S (by omega : S ≠ 0)
  have hb1 : 1 ≤ bitlen S := by
    rcases Nat.eq_zero_or_pos (bitlen S) with h0 | hpos
    · exfalso; rw [h0] at hob; simp at hob; omega
    · exact hpos
  apply bitlen_unique
  · have low : 2 ^ (bitlen S - 1) ≤ S := by
      have he : bitlen S = (bitlen S - 1) + 1 := by omega
      rw [he, Nat.pow_succ] at hun
      omega
    have h1 := Nat.mul_le_mul low (Nat.le_refl (2 ^ t))
    have h2 : 2 ^ (bitlen S - 1) * 2 ^ t = 2 ^ (bitlen S + t - 1) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    omega
  · have h1 := Nat.mul_lt_mul_of_pos_right hob (Nat.two_pow_pos t)
    have h3 : 2 ^ bitlen S * 2 ^ t = 2 ^ (bitlen S + t) := by rw [← Nat.pow_add]
    omega
  · exact Nat.mul_pos hS (Nat.pow_pos (by decide))

/-- The kernel exponent of a scaled power-of-two denominator: both
    `findeExpBei` branches decide for `E0`, from the `bitlen` bounds. -/
theorem findeExp_scaled (A t j : Nat) (hA : 0 < A) :
    findeExp (A * 2 ^ t) (2 ^ j) = (bitlen A : Int) + (t : Int) - 1 - (j : Int) := by
  have hbit := bitlen_pow2 j
  have hAm := bitlen_mul_pow2 A t hA
  have hb1 : 1 ≤ bitlen A := by
    rcases Nat.eq_zero_or_pos (bitlen A) with h0 | hpos
    · exfalso
      have hob := bitlen_obere A
      rw [h0] at hob; simp at hob; omega
    · exact hpos
  have hle : 2 ^ (bitlen A + t - 1) ≤ A * 2 ^ t := by
    have hun := bitlen_untere A (by omega : A ≠ 0)
    have low : 2 ^ (bitlen A - 1) ≤ A := by
      have he : bitlen A = (bitlen A - 1) + 1 := by omega
      rw [he, Nat.pow_succ] at hun
      omega
    have h1 := Nat.mul_le_mul low (Nat.le_refl (2 ^ t))
    have h2 : 2 ^ (bitlen A - 1) * 2 ^ t = 2 ^ (bitlen A + t - 1) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    omega
  unfold findeExp
  rw [hbit, hAm]
  have hE0 : ((bitlen A + t : Nat) : Int) - ((j + 1 : Nat) : Int)
      = (bitlen A : Int) + (t : Int) - 1 - (j : Int) := by
    omega
  rw [hE0]
  unfold findeExpBei
  by_cases hE : 0 ≤ (bitlen A : Int) + (t : Int) - 1 - (j : Int)
  · rw [if_pos hE]
    have hbj : j + 1 ≤ bitlen A + t := by omega
    have hE0n : ((bitlen A : Int) + (t : Int) - 1 - (j : Int)).toNat
        = bitlen A + t - 1 - j := by
      omega
    rw [hE0n]
    have hpow : 2 ^ j * 2 ^ (bitlen A + t - 1 - j) = 2 ^ (bitlen A + t - 1) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hcheck : 2 ^ j * 2 ^ (bitlen A + t - 1 - j) ≤ A * 2 ^ t := by
      rw [hpow]; exact hle
    rw [if_pos hcheck]
  · rw [if_neg hE]
    have hbj : bitlen A + t ≤ j := by omega
    have hE0n : (-((bitlen A : Int) + (t : Int) - 1 - (j : Int))).toNat
        = j + 1 - (bitlen A + t) := by
      omega
    rw [hE0n]
    have hpow : 2 ^ (bitlen A + t - 1) * 2 ^ (j + 1 - (bitlen A + t)) = 2 ^ j := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hmul := Nat.mul_le_mul hle (Nat.le_refl (2 ^ (j + 1 - (bitlen A + t))))
    have hcheck : 2 ^ j ≤ A * 2 ^ t * 2 ^ (j + 1 - (bitlen A + t)) := by
      omega
    rw [if_pos hcheck]

#print axioms bitlen_unique
#print axioms bitlen_pow2
#print axioms bitlen_mul_pow2
#print axioms findeExp_scaled

end Gabbro.Stage0.Senke
