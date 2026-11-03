/- Representation validity of the exact checked source initialization. -/
module
public import Stage0.Senke.Welt.Initial
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

/-- A declared global retains the validity of every recursively initialized field. -/
theorem initialWorld_global_valid (u : UProg) (valid : GabbroV.sp0OkB u = true)
    (L : Lay (declOf u)) (g : Fin u.globs.length) :
    ValueValid L ((declOf u).gtyp g) ((initialWorld u valid).globs g) := by
  change ValueValid L ((globAt u g).ty.toTy)
    (GabbroV.sp0GlobWert u g (GabbroV.sp0OkB_glob u valid g))
  cases ty : (globAt u g).ty with
  | int lo hi => simp only [ty, GTy.toTy, ValueValid]
  | bool => simp only [ty, GTy.toTy, ValueValid]
  | wert τ =>
    have accepted : (GabbroV.konstWert (F := (declOf u).Fn) (P := (declOf u).passt)
        τ (globAt u g).initK).isSome = true := by
      simpa only [GabbroV.sp0GlobOkB, ty] using GabbroV.sp0OkB_glob u valid g
    have hv := initialConstant_valid L τ _ _ (Option.some_get accepted).symm
    simpa only [GabbroV.sp0GlobWert, ty, GTy.toTy] using hv

/-- Table initialization uses the canonical zero constructor only where its source check
    succeeds. In particular this does not invent default fields for products. -/
theorem initialWorld_slot_valid (u : UProg) (valid : GabbroV.sp0OkB u = true)
    (L : Lay (declOf u)) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) (k : Int) :
    ValueValid L ((declOf u).typ t f) ((initialWorld u valid).slots t k f) := by
  have hf := GabbroV.sp0FeldOkB_of u valid t f
  have hw := GabbroV.sp0WertOkB_of u valid t f
  change ValueValid L (typAt u t f) (GabbroV.sp0FeldWert u t f hf hw)
  cases entry : (tabAt u t).cols[f.val]? with
  | none => simp only [GabbroV.sp0FeldOkB, entry, Bool.false_eq_true] at hf
  | some q =>
    cases boolean : (tabAt u t).bools.contains q.1 with
    | true =>
      have hb : boolFeldAt u t f = true := by simp only [boolFeldAt, entry, boolean]
      simp only [typAt, hb, ↓reduceIte, ValueValid]
    | false =>
      have hb : boolFeldAt u t f = false := by simp only [boolFeldAt, entry, boolean]
      cases option : optFeldAt u t f with
      | some n => simp only [typAt, hb, option, Bool.false_eq_true, ↓reduceIte, ValueValid]
      | none =>
        cases aggregate : wertFeldAt u t f with
        | none =>
          have range : fieldRangeO u t f = some q.2 := by simp only [fieldRangeO, entry]
          simp only [typAt, hb, option, aggregate, range, Bool.false_eq_true, ↓reduceIte, ValueValid]
        | some τ =>
          have accepted : (GabbroV.konstWert (F := (declOf u).Fn) (P := (declOf u).passt)
              τ .null).isSome = true := by
            simpa only [GabbroV.sp0WertOkB, aggregate] using hw
          have hv := initialConstant_valid L τ _ _ (Option.some_get accepted).symm
          simpa only [GabbroV.sp0FeldWert, entry, boolean, option, aggregate,
            typAt, hb, Bool.false_eq_true, ↓reduceIte] using hv

/-- These are precisely the representation duties later packaged by WeltAt. -/
theorem initialWorld_valid (u : UProg) (valid : GabbroV.sp0OkB u = true) (L : Lay (declOf u)) :
    (∀ t f k, ValueValid L ((declOf u).typ t f) ((initialWorld u valid).slots t k f)) ∧
    (∀ g, ValueValid L ((declOf u).gtyp g) ((initialWorld u valid).globs g)) :=
  ⟨initialWorld_slot_valid u valid L, initialWorld_global_valid u valid L⟩

end Gabbro.Stage0.Senke
