/- Constant interval endpoints may be infinite; NaN is unordered. -/
import Stage0.Senke.Ausdruck.Gleit.Schluessel
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gabbro.Grammatik.Gleitkomma

theorem float_infinity_fields {a : GFloat} (hc : klasse f64 a = .unendlich) :
    a.bexp = 2047 ∧ a.frac = 0 := by
  unfold klasse at hc
  split at hc
  · next he =>
    split at hc
    · next hf => exact ⟨he, hf⟩
    · contradiction
  · split at hc
    · split at hc <;> contradiction
    · contradiction

theorem float_finite_key_bound {a : GFloat} (hw : wf f64 a) (hf : gleitEndlich a = true) :
    -9218868437227405312 < floatKey a ∧ floatKey a < 9218868437227405312 := by
  have he : a.bexp ≠ 2047 := by
    intro he
    unfold gleitEndlich klasse at hf
    simp only [show f64.bexpMax = 2047 from rfl, he, ↓reduceIte] at hf
    by_cases hz : a.frac = 0 <;> simp only [hz, ↓reduceIte] at hf <;> cases hf
  have hb : a.bexp ≤ 2047 := hw.1
  have hfrac : a.frac < 4503599627370496 := hw.2
  unfold floatKey floatMag
  cases a.sign <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem float_infinity_key {a : GFloat} (hc : klasse f64 a = .unendlich) :
    floatKey a = if a.sign then -9218868437227405312 else 9218868437227405312 := by
  obtain ⟨he, hf⟩ := float_infinity_fields hc
  unfold floatKey floatMag
  rw [he, hf]
  rfl

theorem float_notfinite_infinity {a : GFloat} (ha : klasse f64 a ≠ .nan)
    (hf : gleitEndlich a ≠ true) : klasse f64 a = .unendlich := by
  unfold gleitEndlich at hf
  cases hc : klasse f64 a <;> simp_all

/-- The same signed key orders finite values and infinities, but never admits NaN. -/
theorem float_lt_key_not_nan {a b : GFloat} (ha : wf f64 a) (hb : wf f64 b)
    (an : klasse f64 a ≠ .nan) (bn : klasse f64 b ≠ .nan) :
    gleitLt a b = decide (floatKey a < floatKey b) := by
  by_cases af : gleitEndlich a = true
  · by_cases bf : gleitEndlich b = true
    · exact float_lt_key ha hb af bf
    · have bi := float_notfinite_infinity bn bf
      rw [gleitLt, flt_unendlich_rechts af bi, float_infinity_key bi]
      have ar := float_finite_key_bound ha af
      cases b.sign <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; simp_all <;> omega
  · have ai := float_notfinite_infinity an af
    by_cases bf : gleitEndlich b = true
    · rw [gleitLt, flt_unendlich_links ai bf, float_infinity_key ai]
      have br := float_finite_key_bound hb bf
      cases a.sign <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; simp_all <;> omega
    · have bi := float_notfinite_infinity bn bf
      rw [gleitLt, flt, ai, bi, float_infinity_key ai, float_infinity_key bi]
      cases a.sign <;> cases b.sign <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> decide

end Gabbro.Stage0.Senke
