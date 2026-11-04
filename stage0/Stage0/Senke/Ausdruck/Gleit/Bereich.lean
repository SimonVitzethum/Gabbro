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
    simp only [ha, Float.Model.UnpackedFloat.isNaN, Bool.false_eq_true] at h
  all_goals rfl

private theorem native_le_nan (a b : Float) (h : b.isNaN = true) : Float.le a b = false := by
  change b.toModel.unpack.isNaN = true at h
  change a.toModel.unpack.le b.toModel.unpack = false
  cases hb : b.toModel.unpack <;>
    simp only [hb, Float.Model.UnpackedFloat.isNaN, Bool.false_eq_true] at h
  all_goals cases a.toModel.unpack <;> rfl

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

private theorem bool_range_rejection (finite lower upper : Bool) :
    (!(finite && (lower && upper)) = true) ↔
      ¬ (finite = true ∧ lower = true ∧ upper = true) := by
  cases finite <;> cases lower <;> cases upper <;> decide

/-- The emitted Boolean is precisely the existing source failure, without
    unfolding any native float operation in this proof. -/
theorem floatRangeReject_none {lo hi : Int × Int} {x : GFloat} :
    gleitPasst lo hi x = none ↔ floatRangeReject lo hi x = true := by
  have rejection : floatRangeReject lo hi x = true ↔
      ¬ (gleitEndlich x = true ∧ gleitLe (bruch lo) x = true ∧ gleitLe x (bruch hi) = true) :=
    bool_range_rejection _ _ _
  unfold gleitPasst
  split
  · next accepted =>
    constructor
    · intro impossible; cases impossible
    · intro rejected
      exact False.elim ((rejection.mp rejected) accepted)
  · next refused =>
    exact ⟨fun _ => rejection.mpr refused, fun _ => rfl⟩

theorem floatRangeReject_accept {lo hi : Int × Int} {x : GFloat} :
    floatRangeReject lo hi x = false ↔ ∃ v, gleitPasst lo hi x = some v := by
  constructor
  · intro accepted
    cases result : gleitPasst lo hi x with
    | none =>
      have rejected := floatRangeReject_none.mp result
      rw [accepted] at rejected
      cases rejected
    | some v => exact ⟨v, rfl⟩
  · rintro ⟨v, result⟩
    apply Bool.eq_false_iff.mpr
    intro rejected
    have refused := floatRangeReject_none.mpr rejected
    rw [result] at refused
    cases refused

end Gabbro.Stage0.Senke
