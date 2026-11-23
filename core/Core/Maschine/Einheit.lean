/-
  File:      core/Core/Maschine/Einheit.lean
  Subject:   UNITS AT PROVED LINEARISATION POINTS (PERFECT-MODEL §3.4, step M4): the commutation obligation
             of a unit as a structure (`Kommutation`) and the reduction it gives. A step of the unit's
             context BEFORE its linearisation point moves right past every step of the other contexts
             (`RechtsBeweger`), a step AFTER it moves left (`LinksBeweger`); then the unit's private steps
             can be gathered at its linearisation point (`rechts_vorbei`, `links_vorbei`), which is why `I`
             may take the whole unit there. Every source rule of `I` names its units and discharges this
             structure for them (registry, §3.1); nothing here is assumed.
-/
module

public import Mathlib.Logic.Relation

@[expose] public section

namespace Gabbro.Core.Maschine

variable {S : Type}

/-- `a` moves right past `b`: an `a` step followed by a `b` step can be done `b` first. -/
def RechtsBeweger (a b : S → S → Prop) : Prop :=
  ∀ s s1 s2, a s s1 → b s1 s2 → ∃ s1', b s s1' ∧ a s1' s2

/-- `a` moves left past `b`: a `b` step followed by an `a` step can be done `a` first. -/
def LinksBeweger (a b : S → S → Prop) : Prop :=
  ∀ s s1 s2, b s s1 → a s1 s2 → ∃ s1', a s s1' ∧ b s1' s2

/-- **A right mover passes any number of the other steps.** -/
theorem rechts_vorbei {a b : S → S → Prop} (h : RechtsBeweger a b) {s s1 s2 : S} (ha : a s s1)
    (hb : Relation.ReflTransGen b s1 s2) : ∃ s', Relation.ReflTransGen b s s' ∧ a s' s2 := by
  induction hb with
  | refl => exact ⟨s, .refl, ha⟩
  | tail _ hlast ih =>
    obtain ⟨s', hs', ha'⟩ := ih
    obtain ⟨s'', hb'', ha''⟩ := h _ _ _ ha' hlast
    exact ⟨s'', hs'.tail hb'', ha''⟩

/-- **A left mover passes any number of the other steps.** -/
theorem links_vorbei {a b : S → S → Prop} (h : LinksBeweger a b) {s s1 s2 : S}
    (hb : Relation.ReflTransGen b s s1) (ha : a s1 s2) :
    ∃ s', a s s' ∧ Relation.ReflTransGen b s' s2 := by
  induction hb generalizing s2 with
  | refl => exact ⟨s2, ha, .refl⟩
  | tail _ hlast ih =>
    obtain ⟨s', ha', hb'⟩ := h _ _ _ hlast ha
    obtain ⟨s'', ha'', hb''⟩ := ih ha'
    exact ⟨s'', ha'', hb''.tail hb'⟩

/-- **The commutation obligation of a unit** of context-step relation `vor` (its steps before the
    linearisation point) and `nach` (after it) against the steps `andere` of every other context. -/
structure Kommutation (vor nach andere : S → S → Prop) : Prop where
  vor_rechts : RechtsBeweger vor andere
  nach_links : LinksBeweger nach andere

/-- Satisfiability: steps that touch disjoint parts of a product state commute both ways. -/
theorem kommutation_erfuellbar {A B : Type} (f : A → A) (g : B → B) :
    Kommutation (S := A × B) (fun s s' => s' = (f s.1, s.2)) (fun s s' => s' = (f s.1, s.2))
      (fun s s' => s' = (s.1, g s.2)) :=
  ⟨fun s _ _ h1 h2 => ⟨(s.1, g s.2), rfl, by rw [h2, h1]⟩,
    fun s _ _ h1 h2 => ⟨(f s.1, s.2), rfl, by rw [h2, h1]⟩⟩

end Gabbro.Core.Maschine
