/- Finite range checks reuse strict comparisons; NaN bounds are never silently accepted. -/
import Stage0.Senke.Ausdruck.Gleit.Fall
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik

/-- The outside flag shared by the branch code and the model's range match. -/
def floatOutside (lo hi : Int × Int) (x : GFloat) : Bool :=
  gleitLt x (bruch lo) || gleitLt (bruch hi) x

theorem floatOutside_none {lo hi : Int × Int} {x : GFloat}
    (hl : gleitEndlich (bruch lo) = true) (hh : gleitEndlich (bruch hi) = true)
    (hx : gleitEndlich x = true) :
    gleitPasst lo hi x = none ↔ floatOutside lo hi x = true := by
  have hlc := fle_flt (endlich_nicht_nan hl) (endlich_nicht_nan hx)
  have hhc := fle_flt (endlich_nicht_nan hx) (endlich_nicht_nan hh)
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

theorem floatPasst_x {lo hi : Int × Int} {x : GFloat} {v : Gleit lo hi}
    (h : gleitPasst lo hi x = some v) : v.x = x := by
  unfold gleitPasst at h
  split at h <;> cases h
  rfl

end Gabbro.Stage0.Senke
