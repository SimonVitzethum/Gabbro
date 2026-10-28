/-
  File:      Grammatik/Gen/Text/Pruefung.lean
  Subject:   THE TEXT OF A GENERATOR PROGRAM and the decided check that its read-back program has given cells and a
             given verdict (`textCheck`), with the soundness theorem the witness files apply (`textCheck_sound`).
-/
import Grammatik.Gen.Text.Gut

namespace Gabbro.Grammatik.Gen.Text

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser

/-- **The text of a generator program**: the rendered print of its delaboration (empty when it has none). -/
def textVon (z : Spez) (P : Programm z.deklaration) (ws : List z.deklaration.Fn) : String :=
  match delab z P ws with
  | .ok its => renderText (druckItems its)
  | .error _ => ""

/-- The check: the delaboration exists, is printable, and its items read back as a program with the cells `zs` and
    the verdict `g`. -/
def textCheck (z : Spez) (P : Programm z.deklaration) (ws : List z.deklaration.Fn) (zs : List Zelle) (g : Bool) :
    Bool :=
  match delab z P ws with
  | .error _ => false
  | .ok its =>
    itemsGutB its && match ausItems its with
      | .error _ => false
      | .ok e => e.zellen == zs && e.gueltig == g

theorem textCheck_sound (z : Spez) (P : Programm z.deklaration) (ws : List z.deklaration.Fn) (zs : List Zelle)
    (g : Bool) (h : textCheck z P ws zs g = true) :
    ∃ e', ausText (textVon z P ws) = .ok e' ∧ e'.zellen = zs ∧ e'.gueltig = g := by
  cases hd : delab z P ws with
  | error m => simp only [textCheck, hd, Bool.false_eq_true] at h
  | ok its =>
    simp only [textCheck, hd, Bool.and_eq_true] at h
    obtain ⟨hg, h⟩ := h
    simp only [textVon, hd]
    rw [ausText_druckB its hg]
    cases ha : ausItems its with
    | error m => rw [ha] at h; cases h
    | ok e =>
      rw [ha] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨e, rfl, h.1, h.2⟩

end Gabbro.Grammatik.Gen.Text
