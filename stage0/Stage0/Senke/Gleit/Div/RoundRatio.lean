/- Rational quotient rounding reuses the shared dyadic and sticky decisions. -/
module
public import Stage0.Senke.Gleit.Div.Scale
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma

/-- Moving a lossless numerator shift into the scale preserves every tie. -/
theorem softRoundRatio_mul_pow (n d k : Nat) (dp : 0 < d) (e : Int) :
    softRoundRatio (n * 2 ^ k) d (e - (k : Int)) = softRoundRatio n d e := by
  unfold softRoundRatio
  rw [Nat.mul_assoc, ← Nat.pow_add]
  apply softRoundRatio_power n d _ _ _ _ dp
  omega

/-- The kernel's normal significand decision at an exact rational scale. -/
theorem softDiv_normQ (a b t j : Nat) (bp : 0 < b) (E : Int) :
    normQ 53 E (a * 2 ^ t) (b * 2 ^ j) =
      softRoundRatio a b (52 - E + (t : Int) - (j : Int)) := by
  unfold normQ normQD
  split
  · next up =>
    dsimp only
    rw [Nat.mul_assoc, ← Nat.pow_add]
    apply softRoundRatio_scale a b _ _ bp
    omega
  · next down =>
    dsimp only
    rw [Nat.mul_assoc, ← Nat.pow_add]
    apply softRoundRatio_scale a b _ _ bp
    omega

/-- The subnormal grid uses the same rational rounding operation. -/
theorem softDiv_subQ (a b t j : Nat) (bp : 0 < b) :
    subQ f64 (a * 2 ^ t) (b * 2 ^ j) =
      softRoundRatio a b ((t : Int) - (j : Int) + 1074) := by
  change rundeInt (((a * 2 ^ t) * 2 ^ 1074) / (b * 2 ^ j))
    (((a * 2 ^ t) * 2 ^ 1074) % (b * 2 ^ j)) (b * 2 ^ j) = _
  rw [Nat.mul_assoc, ← Nat.pow_add]
  apply softRoundRatio_scale a b _ _ bp
  omega

/-- Apply the shared rational interval theorem after discarding at least
    two places. In particular an inexact rest cannot create an exact tie. -/
theorem softDivJam_round (n d k : Nat) (dp : 0 < d) (nb : n < 2 ^ 128)
    (guard : 2 ≤ k) :
    softRoundRatio n d (-(k : Int)) =
      softRoundDyadic (softDivJam n d) (-(k : Int)) := by
  have up : (-(k : Int)).toNat = 0 := by omega
  have down : (-(-(k : Int))).toNat = k := by omega
  unfold softRoundRatio softRoundDyadic
  rw [up, down]
  simp only [Nat.pow_zero, Nat.mul_one]
  have grid : 2 ^ k = 4 * 2 ^ (k - 2) := by
    rw [← show (2 : Nat) ^ 2 = 4 from rfl, ← Nat.pow_add]
    congr 1
    omega
  rw [Nat.mul_comm d, grid]
  rcases softDivJam_interval n d dp nb with exactValue | ⟨odd, lo, hi⟩
  · exact softRound_scaled _ _ _ _ dp
      (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) exactValue
  · exact softRound_odd_interval _ _ _ _ dp (Nat.two_pow_pos _) odd lo hi

/-- Normalizing numerator and denominator preserves their rational rounding
    at every scale, including scales below the subnormal boundary. -/
theorem softDiv_normalize_round (a b ca cb : Nat) (bp : 0 < b) (e : Int) :
    softRoundRatio a b e =
      softRoundRatio (a * 2 ^ ca) (b * 2 ^ cb) (e - (ca : Int) + (cb : Int)) := by
  unfold softRoundRatio
  simp only [Nat.mul_assoc, ← Nat.pow_add]
  apply softRoundRatio_power a b _ _ _ _ bp
  omega

/-- Exact halves, inexact thirds and a very coarse underflow grid exercise
    the same rounding theorem without restricting the denominator to powers of two. -/
theorem softDivJam_round_zeuge :
    softRoundRatio (2 ^ 108) (3 * 2 ^ 51) (-3) =
      softRoundDyadic (softDivJam (2 ^ 108) (3 * 2 ^ 51)) (-3) ∧
    softRoundRatio (2 ^ 107) (2 ^ 52) (-3) =
      softRoundDyadic (softDivJam (2 ^ 107) (2 ^ 52)) (-3) ∧
    softRoundRatio (2 ^ 108) (3 * 2 ^ 51) (-1100) =
      softRoundDyadic (softDivJam (2 ^ 108) (3 * 2 ^ 51)) (-1100) := by
  exact ⟨softDivJam_round _ _ _ (by decide) (by decide) (by decide),
    softDivJam_round _ _ _ (by decide) (by decide) (by decide),
    softDivJam_round _ _ _ (by decide) (by decide) (by decide)⟩

/-- Exact rational ties retain quotient parity before any packing step.
    Both decisions use the kernel round-to-nearest-even operation. -/
theorem softRoundRatio_ties_zeuge :
    softRoundRatio 1 2 0 = 0 ∧ softRoundRatio 3 2 0 = 2 := by
  decide +kernel

#print axioms softDiv_normQ
#print axioms softDiv_subQ
#print axioms softDivJam_round
#print axioms softDiv_normalize_round
#print axioms softDivJam_round_zeuge
#print axioms softRoundRatio_ties_zeuge
end Gabbro.Stage0.Senke
