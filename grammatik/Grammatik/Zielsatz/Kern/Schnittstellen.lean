/-
  File:      Grammatik/Schnittstellen.lean
  Subject:   THE INTERFACE RESOLUTION OF A UNIT (C08 foundation) -- what the
             checker decides about referenced pointer/foreign signatures, as ONE
             Bool (`schnittstellenB`), proved to decide its field of
             `AkzeptiertSpec` (`schnittstellenB_iff`).

  `SchnittstellenOk P fs`: every foreign item a body calls agrees with its
  canonical signature (parameters, result, channel) and produces no owner --
  the canonical signature produces nothing, so `eigner_nie_erzeugt` holds by
  construction. Origin names, resource stages/multiplicities and
  contract/boundary-clause reads join as their export lands; unresolved origins
  stay refused, never inferred from `fs` alone.
-/
module

public import Grammatik.Kern.Syntax.Syntax.Teil2
public import Grammatik.Logik.Vertraege.Locations.AntwortOrte

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The interface resolution of a unit (C08).** -/
def SchnittstellenOk (P : Programm D) (fs : List D.Fn) : Prop :=
  ∀ f ∈ fs, ∀ a : D.Ax, .inl a ∈ (P.rumpf f).ants →
    (D.asignatur a).params = D.aparams a ∧ (D.asignatur a).erg = D.aerg a ∧
    (D.asignatur a).gruende = D.agruende a ∧ (D.asignatur a).produziert = []

/-- The interface check at one answer site. -/
def schnittstelleB : D.Ax ⊕ D.Reg → Bool
  | .inl a => decide ((D.asignatur a).params = D.aparams a) &&
    decide ((D.asignatur a).erg = D.aerg a) &&
    decide ((D.asignatur a).gruende = D.agruende a) &&
    decide ((D.asignatur a).produziert = [])
  | .inr _ => true

theorem schnittstelleB_inl (a : D.Ax) :
    schnittstelleB (D := D) (.inl a) = (decide ((D.asignatur a).params = D.aparams a) &&
      decide ((D.asignatur a).erg = D.aerg a) &&
      decide ((D.asignatur a).gruende = D.agruende a) &&
      decide ((D.asignatur a).produziert = [])) := rfl

/-- **The interface component**, decided over the finite unit. -/
def schnittstellenB (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (P.rumpf f).ants.all schnittstelleB

theorem schnittstellenB_iff (hvoll : ∀ g : D.Fn, g ∈ fs) :
    schnittstellenB P fs = true ↔ SchnittstellenOk P fs := by
  constructor
  · intro h f hf a ha
    have h1 := (List.all_eq_true.mp h) f hf
    have h2 := (List.all_eq_true.mp h1) _ ha
    rw [schnittstelleB_inl] at h2
    simp only [Bool.and_eq_true] at h2
    obtain ⟨⟨⟨h3, h4⟩, h5⟩, h6⟩ := h2
    exact ⟨of_decide_eq_true h3, of_decide_eq_true h4, of_decide_eq_true h5,
      of_decide_eq_true h6⟩
  · intro h
    refine List.all_eq_true.mpr fun f hf => ?_
    refine List.all_eq_true.mpr fun x hx => ?_
    cases x with
    | inl a =>
      obtain ⟨h3, h4, h5, h6⟩ := h f hf a hx
      rw [schnittstelleB_inl]
      simp [h3, h4, h5, h6]
    | inr _ => rfl

/-- Every unit meets the interface resolution: the canonical signature IS the
    declared shape, by construction. -/
theorem schnittstellen_standard (P : Programm D) (fs : List D.Fn) : SchnittstellenOk P fs :=
  fun _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩

end Gabbro.Grammatik
