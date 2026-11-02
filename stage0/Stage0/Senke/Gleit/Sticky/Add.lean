/- Signed-direction rounding preservation for the actual alignment operation. -/
module
public import Stage0.Senke.Gleit.Sticky.Round
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR

/-- Translating an odd interval by an even guard-scaled magnitude preserves
    its rounding decision. This covers the same-sign aligned addition path. -/
theorem softRound_aligned_add (large : Nat) (small gap : Runner.W)
    (even : large % 2 = 0) (t : Nat) (tp : 0 < t) :
    let d := 2 ^ gap.toNat
    let j := (floatShiftJamWord small gap).toNat
    rundeInt ((large * d + small.toNat) / (4 * t * d))
      ((large * d + small.toNat) % (4 * t * d)) (4 * t * d) =
      rundeInt ((large + j) / (4 * t)) ((large + j) % (4 * t)) (4 * t) := by
  dsimp only
  have dp : 0 < (2 : Nat) ^ gap.toNat := Nat.two_pow_pos _
  rcases floatShiftJamWord_interval small gap with exactValue | ⟨odd, lo, hi⟩
  · apply softRound_scaled _ _ _ _ dp (by omega)
    rw [exactValue.2]
    ring
  · have jp : 0 < (floatShiftJamWord small gap).toNat := by omega
    have pred : large + (floatShiftJamWord small gap).toNat - 1 =
        large + ((floatShiftJamWord small gap).toNat - 1) := by omega
    apply softRound_odd_interval _ _ _ _ dp tp
    · rw [Nat.add_mod, even, odd]
      decide
    · rw [pred, Nat.add_mul]
      omega
    · rw [Nat.add_mul] at *
      nlinarith

/-- Subtraction reflects the interval. The ordered magnitude premise keeps
    natural subtraction exact, including the separate exact-zero case.
    In particular the discarded nonzero tail has the correct negative sign. -/
theorem softRound_aligned_sub (large : Nat) (small gap : Runner.W)
    (even : large % 2 = 0)
    (ordered : (floatShiftJamWord small gap).toNat ≤ large)
    (cover : small.toNat ≤ large * 2 ^ gap.toNat) (t : Nat) (tp : 0 < t) :
    let d := 2 ^ gap.toNat
    let j := (floatShiftJamWord small gap).toNat
    rundeInt ((large * d - small.toNat) / (4 * t * d))
      ((large * d - small.toNat) % (4 * t * d)) (4 * t * d) =
      rundeInt ((large - j) / (4 * t)) ((large - j) % (4 * t)) (4 * t) := by
  dsimp only
  have dp : 0 < (2 : Nat) ^ gap.toNat := Nat.two_pow_pos _
  have difference := Nat.sub_add_cancel ordered
  have numerator := Nat.sub_add_cancel cover
  rcases floatShiftJamWord_interval small gap with exactValue | ⟨odd, lo, hi⟩
  · apply softRound_scaled _ _ _ _ dp (by omega)
    nlinarith [exactValue.2]
  · have oddDifference : (large - (floatShiftJamWord small gap).toNat) % 2 = 1 := by
      have parity := congrArg (fun n : Nat => n % 2) difference
      rw [Nat.add_mod, odd, even] at parity
      omega
    have positive : 0 < large - (floatShiftJamWord small gap).toNat := by omega
    have pred : large - (floatShiftJamWord small gap).toNat - 1 + 1 =
        large - (floatShiftJamWord small gap).toNat := by omega
    have jp : 0 < (floatShiftJamWord small gap).toNat := by omega
    have jpred : (floatShiftJamWord small gap).toNat - 1 + 1 =
        (floatShiftJamWord small gap).toNat := by omega
    exact softRound_odd_interval _ _ _ _ dp tp oddDifference (by nlinarith) (by nlinarith)

/-- The subtraction is not an exact-value replacement. Its final rounded
    decision nevertheless agrees, including both sides of a halfway point. -/
theorem softRound_aligned_zeuge :
    rundeInt ((16 * 8 - 9) / (8 * 8)) ((16 * 8 - 9) % (8 * 8)) (8 * 8) =
      rundeInt ((16 - (floatShiftJamWord 9 3).toNat) / 8)
        ((16 - (floatShiftJamWord 9 3).toNat) % 8) 8 ∧
    rundeInt ((16 * 8 + 9) / (8 * 8)) ((16 * 8 + 9) % (8 * 8)) (8 * 8) =
      rundeInt ((16 + (floatShiftJamWord 9 3).toNat) / 8)
        ((16 + (floatShiftJamWord 9 3).toNat) % 8) 8 ∧
    9 ≤ 16 * 8 ∧ (floatShiftJamWord 9 3).toNat ≤ 16 ∧ (16 : Nat) % 2 = 0 := by
  decide +kernel

#print axioms softRound_aligned_add
#print axioms softRound_aligned_sub
#print axioms softRound_aligned_zeuge
end Gabbro.Stage0.Senke
