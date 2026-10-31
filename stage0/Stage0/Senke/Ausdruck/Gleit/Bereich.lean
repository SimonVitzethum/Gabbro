/- Range checks reuse strict comparisons; NaN endpoints always select the fallback. -/
import Stage0.Senke.Ausdruck.Gleit.Fall
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik

/-- The outside flag shared by the branch code and the model's range match. -/
def floatOutside (lo hi : Int × Int) (x : GFloat) : Bool :=
  gleitLt x (bruch lo) || gleitLt (bruch hi) x

theorem floatOutside_none {lo hi : Int × Int} {x : GFloat}
    (hl : Gleitkomma.klasse Gleitkomma.f64 (bruch lo) ≠ .nan)
    (hh : Gleitkomma.klasse Gleitkomma.f64 (bruch hi) ≠ .nan)
    (hx : gleitEndlich x = true) :
    gleitPasst lo hi x = none ↔ floatOutside lo hi x = true := by
  have hlc := fle_flt hl (endlich_nicht_nan hx)
  have hhc := fle_flt (endlich_nicht_nan hx) hh
  have hc : (gleitEndlich x = true ∧ gleitLe (bruch lo) x = true ∧ gleitLe x (bruch hi) = true) ↔
      floatOutside lo hi x = false := by
    unfold floatOutside gleitLe gleitLt
    rw [hx, hlc, hhc]
    cases Gleitkomma.flt Gleitkomma.f64 x (bruch lo) <;>
      cases Gleitkomma.flt Gleitkomma.f64 (bruch hi) x <;> simp
  unfold gleitPasst
  split
  · next h => have hf := hc.mp h; simp [hf]
  · next h =>
    have hf : floatOutside lo hi x = true := by
      cases H : floatOutside lo hi x <;> simp_all
    simp [hf]

/-- A NaN endpoint makes the target type empty; narrowing always selects the fallback. -/
theorem floatPasst_nan_bound {lo hi : Int × Int} (x : GFloat)
    (hn : Gleitkomma.klasse Gleitkomma.f64 (bruch lo) = .nan ∨
      Gleitkomma.klasse Gleitkomma.f64 (bruch hi) = .nan) : gleitPasst lo hi x = none := by
  unfold gleitPasst
  split
  · next h =>
    rcases hn with hn | hn
    · have hh := h.2.1
      rw [gleitLe, fle_nan_links hn] at hh
      cases hh
    · have hh := h.2.2
      rw [gleitLe, fle_nan_rechts hn] at hh
      cases hh
  · rfl

theorem floatPasst_x {lo hi : Int × Int} {x : GFloat} {v : Gleit lo hi}
    (h : gleitPasst lo hi x = some v) : v.x = x := by
  unfold gleitPasst at h
  split at h <;> cases h
  rfl

/-- Canonical signed-key decision, including unordered endpoints. This is the
    source range check: rounding has already happened before this decision. -/
def floatRangeReject (lo hi : Int × Int) (x : GFloat) : Bool :=
  if Gleitkomma.klasse Gleitkomma.f64 (bruch lo) = .nan ∨
      Gleitkomma.klasse Gleitkomma.f64 (bruch hi) = .nan then true
  else decide (floatKey x < floatKey (bruch lo)) ||
    decide (floatKey (bruch hi) < floatKey x)

/-- Exact rejection criterion for the source's range failure (Stop 107),
    including infinite, reversed and NaN bounds. -/
theorem floatRangeReject_none {lo hi : Int × Int} {x : GFloat}
    (hw : Gleitkomma.wf Gleitkomma.f64 x) (hf : gleitEndlich x = true) :
    gleitPasst lo hi x = none ↔ floatRangeReject lo hi x = true := by
  by_cases hn : Gleitkomma.klasse Gleitkomma.f64 (bruch lo) = .nan ∨
      Gleitkomma.klasse Gleitkomma.f64 (bruch hi) = .nan
  · rw [floatPasst_nan_bound x hn]
    simp [floatRangeReject, hn]
  · have hl : Gleitkomma.klasse Gleitkomma.f64 (bruch lo) ≠ .nan :=
      fun h => hn (Or.inl h)
    have hh : Gleitkomma.klasse Gleitkomma.f64 (bruch hi) ≠ .nan :=
      fun h => hn (Or.inr h)
    rw [floatOutside_none hl hh hf]
    unfold floatRangeReject floatOutside
    rw [if_neg hn, float_lt_key_not_nan (a := x) (b := bruch lo) hw (Gleitkomma.rundeBruch_wf _ Gleitkomma.f64_p _)
      (endlich_nicht_nan hf) hl,
      float_lt_key_not_nan (a := bruch hi) (b := x) (Gleitkomma.rundeBruch_wf _ Gleitkomma.f64_p _) hw
        hh (endlich_nicht_nan hf)]

/-- Acceptance provides the actual dependent source value, rather than just a flag. -/
theorem floatRangeReject_accept {lo hi : Int × Int} {x : GFloat}
    (hw : Gleitkomma.wf Gleitkomma.f64 x) (hf : gleitEndlich x = true) :
    floatRangeReject lo hi x = false ↔ ∃ v, gleitPasst lo hi x = some v := by
  have h := floatRangeReject_none (lo := lo) (hi := hi) hw hf
  cases hp : gleitPasst lo hi x with
  | none => simp_all
  | some v =>
    have hn : floatRangeReject lo hi x ≠ true := by
      intro ht
      have := h.mpr ht
      simp [hp] at this
    cases hr : floatRangeReject lo hi x <;> simp_all

#print axioms floatRangeReject_none
#print axioms floatRangeReject_accept
end Gabbro.Stage0.Senke
