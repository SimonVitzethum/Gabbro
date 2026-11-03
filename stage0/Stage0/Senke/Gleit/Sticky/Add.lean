/- Signed-direction rounding preservation for the actual alignment operation. -/
module
public import Stage0.Senke.Gleit.Sticky.Round
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR
variable [Runner.IR.Kern]

omit [Runner.IR.Kern] in
/-- Translating an odd interval by an even guard-scaled magnitude preserves
    its rounding decision. This covers the same-sign aligned addition path. -/
theorem softRoundNat_aligned_add (large small gap : Nat)
    (even : large % 2 = 0) (t : Nat) (tp : 0 < t) :
    let d := 2 ^ gap
    let j := softShiftJamNat small gap
    rundeInt ((large * d + small) / (4 * t * d))
      ((large * d + small) % (4 * t * d)) (4 * t * d) =
      rundeInt ((large + j) / (4 * t)) ((large + j) % (4 * t)) (4 * t) := by
  dsimp only
  have dp : 0 < (2 : Nat) ^ gap := Nat.two_pow_pos _
  rcases softShiftJamNat_interval small gap with exactValue | ⟨odd, lo, hi⟩
  · apply softRound_scaled _ _ _ _ dp (by omega)
    conv_lhs => rw [exactValue.2]
    ring
  · have jp : 0 < softShiftJamNat small gap := by omega
    have pred : large + softShiftJamNat small gap - 1 =
        large + (softShiftJamNat small gap - 1) := by omega
    apply softRound_odd_interval _ _ _ _ dp tp
    · rw [Nat.add_mod, even, odd]
      try decide
    · rw [pred, Nat.add_mul]
      omega
    · rw [Nat.add_mul] at *
      nlinarith

omit [Runner.IR.Kern] in
/-- Subtraction reflects the interval. The ordered magnitude premise keeps
    natural subtraction exact, including the separate exact-zero case.
    In particular the discarded nonzero tail has the correct negative sign. -/
theorem softRoundNat_aligned_sub (large small gap : Nat)
    (even : large % 2 = 0)
    (ordered : softShiftJamNat small gap ≤ large)
    (cover : small ≤ large * 2 ^ gap) (t : Nat) (tp : 0 < t) :
    let d := 2 ^ gap
    let j := softShiftJamNat small gap
    rundeInt ((large * d - small) / (4 * t * d))
      ((large * d - small) % (4 * t * d)) (4 * t * d) =
      rundeInt ((large - j) / (4 * t)) ((large - j) % (4 * t)) (4 * t) := by
  dsimp only
  have dp : 0 < (2 : Nat) ^ gap := Nat.two_pow_pos _
  have difference := Nat.sub_add_cancel ordered
  have differenceScaled := congrArg (fun n : Nat => n * 2 ^ gap) difference
  have numerator := Nat.sub_add_cancel cover
  rcases softShiftJamNat_interval small gap with exactValue | ⟨odd, lo, hi⟩
  · apply softRound_scaled _ _ _ _ dp (by omega)
    nlinarith [exactValue.2]
  · have oddDifference : (large - softShiftJamNat small gap) % 2 = 1 := by
      have parity := congrArg (fun n : Nat => n % 2) difference
      rw [Nat.add_mod, odd, even] at parity
      omega
    have positive : 0 < large - softShiftJamNat small gap := by omega
    have pred : large - softShiftJamNat small gap - 1 + 1 =
        large - softShiftJamNat small gap := by omega
    have jp : 0 < softShiftJamNat small gap := by omega
    have jpred : softShiftJamNat small gap - 1 + 1 =
        softShiftJamNat small gap := by omega
    have predScaled := congrArg (fun n : Nat => n * 2 ^ gap) pred
    have jpredScaled := congrArg (fun n : Nat => n * 2 ^ gap) jpred
    exact softRound_odd_interval _ _ _ _ dp tp oddDifference (by nlinarith) (by nlinarith)

/-- The same-sign theorem applies directly to the actual emitted word jam. -/
theorem softRound_aligned_add (large : Nat) (small gap : Runner.W)
    (even : large % 2 = 0) (t : Nat) (tp : 0 < t) :
    let d := 2 ^ gap.toNat
    let j := (floatShiftJamWord small gap).toNat
    rundeInt ((large * d + small.toNat) / (4 * t * d))
      ((large * d + small.toNat) % (4 * t * d)) (4 * t * d) =
      rundeInt ((large + j) / (4 * t)) ((large + j) % (4 * t)) (4 * t) := by
  simpa only [floatShiftJamWord_nat] using
    softRoundNat_aligned_add large small.toNat gap.toNat even t tp

/-- Ordered subtraction uses the same unbounded certificate as addition. -/
theorem softRound_aligned_sub (large : Nat) (small gap : Runner.W)
    (even : large % 2 = 0)
    (ordered : (floatShiftJamWord small gap).toNat ≤ large)
    (cover : small.toNat ≤ large * 2 ^ gap.toNat) (t : Nat) (tp : 0 < t) :
    let d := 2 ^ gap.toNat
    let j := (floatShiftJamWord small gap).toNat
    rundeInt ((large * d - small.toNat) / (4 * t * d))
      ((large * d - small.toNat) % (4 * t * d)) (4 * t * d) =
      rundeInt ((large - j) / (4 * t)) ((large - j) % (4 * t)) (4 * t) := by
  simpa only [floatShiftJamWord_nat] using
    softRoundNat_aligned_sub large small.toNat gap.toNat even
      (by simpa only [floatShiftJamWord_nat] using ordered) cover t tp

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

#print axioms softRoundNat_aligned_add
#print axioms softRoundNat_aligned_sub
#print axioms softRound_aligned_add
#print axioms softRound_aligned_sub
#print axioms softRound_aligned_zeuge
end Gabbro.Stage0.Senke
