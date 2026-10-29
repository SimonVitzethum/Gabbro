/- Relate the kernel's exact binary64 comparison to signed magnitude ordering. -/
import Stage0.Senke.Ausdruck.Gleit.Wort
import Grammatik.Logik.Vertraege.EinpassenVoll

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gabbro.Grammatik.Gleitkomma

/-- Exact nonnegative value in units of the least binary64 subnormal. -/
def floatUnits (a : GFloat) : Nat :=
  if a.bexp = 0 then a.frac else (4503599627370496 + a.frac) * 2 ^ (a.bexp - 1)

def floatSignedUnits (a : GFloat) : Int :=
  if a.sign then -(floatUnits a : Int) else floatUnits a

theorem floatUnits_bounds (a : GFloat) (hw : wf f64 a) :
    floatUnits a < 4503599627370496 * 2 ^ a.bexp ∧
    (a.bexp ≠ 0 → 4503599627370496 * 2 ^ (a.bexp - 1) ≤ floatUnits a) := by
  have hf : a.frac < 4503599627370496 := hw.2
  unfold floatUnits
  by_cases hz : a.bexp = 0
  · simp only [hz, ↓reduceIte, Nat.pow_zero, Nat.mul_one]
    exact ⟨hf, fun h => False.elim (h rfl)⟩
  · rw [if_neg hz]
    have hp := Nat.two_pow_pos (a.bexp - 1)
    constructor
    · calc
        _ < (4503599627370496 * 2) * 2 ^ (a.bexp - 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) hp
        _ = 4503599627370496 * 2 ^ a.bexp := by
          rw [Nat.mul_assoc, ← Nat.pow_succ']
          exact congrArg (fun e => 4503599627370496 * 2 ^ e) (by omega)
    · intro _
      exact Nat.mul_le_mul_right _ (by omega)

theorem floatUnits_exp_lt {a b : GFloat} (ha : wf f64 a) (hb : wf f64 b)
    (he : a.bexp < b.bexp) : floatUnits a < floatUnits b := by
  have aa := (floatUnits_bounds a ha).1
  have bb := (floatUnits_bounds b hb).2 (by omega)
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show a.bexp ≤ b.bexp - 1 by omega)
  exact Nat.lt_of_lt_of_le aa (Nat.le_trans (Nat.mul_le_mul_left _ hp) bb)

theorem floatUnits_lt {a b : GFloat} (ha : wf f64 a) (hb : wf f64 b) :
    floatUnits a < floatUnits b ↔ floatMag a < floatMag b := by
  have af : a.frac < 4503599627370496 := ha.2
  have bf : b.frac < 4503599627370496 := hb.2
  by_cases he : a.bexp = b.bexp
  · unfold floatUnits floatMag
    rw [he]
    by_cases hz : b.bexp = 0
    · simp only [hz, ↓reduceIte, Nat.zero_mul, Nat.zero_add]
    · rw [if_neg hz, if_neg hz]
      have hp := Nat.two_pow_pos (b.bexp - 1)
      rw [Nat.mul_lt_mul_right hp]
      omega
  · rcases Nat.lt_or_gt_of_ne he with he | he
    · have hm := floatUnits_exp_lt ha hb he
      unfold floatMag
      omega
    · have hm := floatUnits_exp_lt hb ha he
      unfold floatMag
      omega

theorem floatUnits_zero {a : GFloat} : floatUnits a = 0 ↔ floatMag a = 0 := by
  unfold floatUnits floatMag
  by_cases hz : a.bexp = 0
  · simp [hz]
  · rw [if_neg hz]
    have hp := Nat.mul_pos (show 0 < 4503599627370496 + a.frac by omega) (Nat.two_pow_pos (a.bexp - 1))
    constructor <;> intro h <;> omega

theorem floatSignedUnits_lt {a b : GFloat} (ha : wf f64 a) (hb : wf f64 b) :
    floatSignedUnits a < floatSignedUnits b ↔ floatKey a < floatKey b := by
  have hab := floatUnits_lt ha hb
  have hba := floatUnits_lt hb ha
  have az := floatUnits_zero (a := a)
  have bz := floatUnits_zero (a := b)
  unfold floatSignedUnits floatKey
  cases a.sign <;> cases b.sign <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The exact dyadic value can be scaled to the common subnormal unit. -/
theorem float_exact_units {a : GFloat} (hf : gleitEndlich a = true) :
    ∃ u, wertExakt f64 a = some u ∧ -1074 ≤ u.zweierExp ∧
      u.zaehler * ((2 ^ (u.zweierExp + 1074).toNat : Nat) : Int) = floatSignedUnits a := by
  rcases endlich_klasse hf with hz | hs | hn
  · have hfields : a.bexp = 0 ∧ a.frac = 0 := by
      unfold klasse at hz
      split at hz <;> split at hz <;> simp_all
    refine ⟨⟨0, 0⟩, by simp only [wertExakt, hz], by decide, ?_⟩
    simp [floatSignedUnits, floatUnits, hfields.1, hfields.2]
  · have he : a.bexp = 0 := by
      unfold klasse at hs
      split at hs <;> split at hs <;> simp_all
    refine ⟨⟨(if a.sign then (-1 : Int) else 1) * a.frac, -1074⟩,
      by simp only [wertExakt, hs]; rfl, by dsimp only; omega, ?_⟩
    change (if a.sign then (-1 : Int) else 1) * a.frac * 1 = floatSignedUnits a
    simp only [floatSignedUnits, floatUnits, he, ↓reduceIte]
    cases a.sign <;> simp
  · have he : a.bexp ≠ 0 := by
      intro h
      simp only [klasse, h, show f64.bexpMax = 2047 from rfl,
        show ¬ (0 : Nat) = 2047 from by decide, ↓reduceIte] at hn
      split at hn <;> contradiction
    refine ⟨⟨(if a.sign then (-1 : Int) else 1) * (4503599627370496 + (a.frac : Int)),
      (a.bexp : Int) - 1023 - (53 - 1)⟩, by simp only [wertExakt, hn]; rfl, ?_, ?_⟩
    · change -1074 ≤ (a.bexp : Int) - 1023 - (53 - 1)
      omega
    · change (if a.sign then (-1 : Int) else 1) * (4503599627370496 + (a.frac : Int)) *
        ((2 ^ ((a.bexp : Int) - 1023 - (53 - 1) + 1074).toNat : Nat) : Int) = floatSignedUnits a
      have ee : ((a.bexp : Int) - 1023 - (53 - 1) + 1074).toNat = a.bexp - 1 := by omega
      rw [ee]
      simp only [floatSignedUnits, floatUnits, if_neg he, Int.natCast_mul, Int.natCast_add]
      cases a.sign <;> simp [Int.neg_mul]

theorem float_lt_key {a b : GFloat} (ha : wf f64 a) (hb : wf f64 b)
    (af : gleitEndlich a = true) (bf : gleitEndlich b = true) :
    gleitLt a b = decide (floatKey a < floatKey b) := by
  obtain ⟨u, hu, hue, hus⟩ := float_exact_units af
  obtain ⟨v, hv, hve, hvs⟩ := float_exact_units bf
  rw [gleitLt, flt_exakt af bf hu hv]
  congr 1
  apply propext
  rw [exaktLt_bei u v (-1074) hue hve]
  simpa only [Int.sub_neg, hus, hvs] using floatSignedUnits_lt ha hb

end Gabbro.Stage0.Senke
