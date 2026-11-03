/- Representation validity of the exact checked source initialization. -/
module
public import Stage0.Senke.Welt.Initial
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

private theorem valid_cast_back {D : Deklaration} (L : Lay D) {τ σ : Ty}
    (same : τ = σ) (value : Wert D σ) (valid : ValueValid L σ value) :
    ValueValid L τ (Eq.mpr (congrArg (Wert D) same) value) := by
  cases same
  exact valid

/-- A declared global retains the validity of every recursively initialized field. -/
theorem initialWorld_global_valid (u : UProg) (valid : GabbroV.sp0OkB u = true)
    (L : Lay (declOf u)) (g : Fin u.globs.length) :
    ValueValid L ((declOf u).gtyp g) ((initialWorld u valid).globs g) := by
  change ValueValid L ((declOf u).gtyp g)
    (GabbroV.sp0GlobWert u g (GabbroV.sp0OkB_glob u valid g))
  unfold GabbroV.sp0GlobWert
  split
  · apply valid_cast_back L
    trivial
  · apply valid_cast_back L
    trivial
  · next τ ty =>
    have accepted : (GabbroV.konstWert (F := (declOf u).Fn) (P := (declOf u).passt)
        τ (globAt u g).initK).isSome = true := by
      simpa only [GabbroV.sp0GlobOkB, ty] using GabbroV.sp0OkB_glob u valid g
    have hv := initialConstant_valid L τ _ _ (Option.some_get accepted).symm
    exact valid_cast_back L _ _ hv

/-- Table initialization uses the canonical zero constructor only where its source check
    succeeds. In particular this does not invent default fields for products. -/
theorem initialWorld_slot_valid (u : UProg) (valid : GabbroV.sp0OkB u = true)
    (L : Lay (declOf u)) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) (k : Int) :
    ValueValid L ((declOf u).typ t f) ((initialWorld u valid).slots t k f) := by
  have hf := GabbroV.sp0FeldOkB_of u valid t f
  have hw := GabbroV.sp0WertOkB_of u valid t f
  change ValueValid L (typAt u t f) (GabbroV.sp0FeldWert u t f hf hw)
  unfold GabbroV.sp0FeldWert
  split
  · next q entry =>
    split
    · apply valid_cast_back L
      trivial
    · next boolean =>
      split
      · apply valid_cast_back L
        trivial
      · split
        · next τ aggregate =>
          have accepted : (GabbroV.konstWert (F := (declOf u).Fn) (P := (declOf u).passt)
              τ .null).isSome = true := by
            simpa only [GabbroV.sp0WertOkB, aggregate] using hw
          exact valid_cast_back L _ _
            (initialConstant_valid L τ _ _ (Option.some_get accepted).symm)
        · split
          · apply valid_cast_back L
            trivial
          · next denied =>
            have impossible : GabbroV.sp0FeldOkB u t f = false := by
              simp only [GabbroV.sp0FeldOkB, entry, boolean, denied]
            rw [impossible] at hf
            cases hf
  · next entry =>
    have impossible : GabbroV.sp0FeldOkB u t f = false := by
      simp only [GabbroV.sp0FeldOkB, entry]
    rw [impossible] at hf
    cases hf

/-- These are precisely the representation duties later packaged by WeltAt. -/
theorem initialWorld_valid (u : UProg) (valid : GabbroV.sp0OkB u = true) (L : Lay (declOf u)) :
    (∀ t f k, ValueValid L ((declOf u).typ t f) ((initialWorld u valid).slots t k f)) ∧
    (∀ g, ValueValid L ((declOf u).gtyp g) ((initialWorld u valid).globs g)) :=
  ⟨initialWorld_slot_valid u valid L, initialWorld_global_valid u valid L⟩

end Gabbro.Stage0.Senke
