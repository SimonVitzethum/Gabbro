/- Exact native float range decisions, including unordered endpoints. -/
module
public import Stage0.Senke.Ausdruck.Gleit.Fall
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik

private theorem native_nan_le (a b : Float) (h : a.isNaN = true) : Float.le a b = false := by
  change a.toModel.unpack.isNaN = true at h
  change a.toModel.unpack.le b.toModel.unpack = false
  cases ha : a.toModel.unpack <;>
    simp_all [Float.Model.UnpackedFloat.isNaN, Float.Model.UnpackedFloat.le,
      Float.Model.UnpackedFloat.compare]

private theorem native_le_nan (a b : Float) (h : b.isNaN = true) : Float.le a b = false := by
  change b.toModel.unpack.isNaN = true at h
  change a.toModel.unpack.le b.toModel.unpack = false
  cases hb : b.toModel.unpack <;>
    simp_all [Float.Model.UnpackedFloat.isNaN, Float.Model.UnpackedFloat.le,
      Float.Model.UnpackedFloat.compare]

/-- A NaN endpoint still selects the existing terminating fallback. -/
theorem floatPasst_nan_bound {lo hi : Int × Int} (x : GFloat)
    (hn : (bruch lo).isNaN = true ∨ (bruch hi).isNaN = true) :
    gleitPasst lo hi x = none := by
  rcases hn with hn | hn
  · simp [gleitPasst, gleitLe, native_nan_le _ _ hn]
  · simp [gleitPasst, gleitLe, native_le_nan _ _ hn]

theorem floatPasst_x {lo hi : Int × Int} {x : GFloat} {v : Gleit lo hi}
    (h : gleitPasst lo hi x = some v) : v.x = x := by
  unfold gleitPasst at h
  split at h <;> cases h
  rfl

/-- The emitted Boolean is precisely the existing source failure for every
    native result, including infinities and all NaN representations. -/
theorem floatRangeReject_none {lo hi : Int × Int} {x : GFloat} :
    gleitPasst lo hi x = none ↔ floatRangeReject lo hi x = true := by
  unfold gleitPasst floatRangeReject
  cases hf : gleitEndlich x <;> cases hl : gleitLe (bruch lo) x <;>
    cases hh : gleitLe x (bruch hi) <;> simp [hf, hl, hh]

theorem floatRangeReject_accept {lo hi : Int × Int} {x : GFloat} :
    floatRangeReject lo hi x = false ↔ ∃ v, gleitPasst lo hi x = some v := by
  have equivalent := floatRangeReject_none (lo := lo) (hi := hi) (x := x)
  cases hp : gleitPasst lo hi x <;> cases hr : floatRangeReject lo hi x <;> simp_all

end Gabbro.Stage0.Senke
