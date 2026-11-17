module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Snapshot.Decision

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.ReductionWitness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt
open Invarianten.Frag.Symbolic Reduce

/-- Two immutable aliases preserve the source-state value through a write. -/
def original : LProp Nat := .all 1 (.imp (.eq (.var 1) (.var 0))
  (.all 2 (.imp (.eq (.var 2) (.var 1)) (.eq (.var 2) (.var 0)))))

theorem normalize_zeuge (values : Assignment Nat) :
    (normalize 8 original).val = .tru ∧
      ((normalize 8 original).val.denote values ↔ original.denote values) :=
  ⟨rfl, (normalize 8 original).property values⟩

theorem substitute_zeuge (values : Assignment Nat) :
    ∃ replaced, substitute 1 (.var 0) (.all 2 (.eq (.var 2) (.var 1))) = some replaced ∧
      (replaced.val.denote values ↔
        (LProp.all 2 (.eq (.var 2) (.var 1))).denote (values.bind 1 (values 0))) :=
  ⟨_, rfl, (substitute 1 (.var 0) (.all 2 (.eq (.var 2) (.var 1)))).get (by rfl) |>.property values⟩

theorem substitution_capture_refused_zeuge :
    substitute 1 (.var 0) (.all 0 (.eq (.var 0) (.var 1))) = none := rfl

theorem term_bind_absent_zeuge (values : Assignment Nat) (value : Int) :
    (LTerm.add (.var 0) (.konst 7)).denote (values.bind 1 value) = values 0 + 7 :=
  term_bind_absent _ 1 (by decide) values value

theorem bind_commute_zeuge (values : Assignment Nat) (first last : Int) :
    (values.bind 1 first).bind 2 last = (values.bind 2 last).bind 1 first :=
  bind_commute values 1 2 (by decide) first last

/-- Contradictory call postconditions remain vacuous; no inhabitant is assumed. -/
def contradictory : LProp Nat := .all 1 (.imp
  (.and (.eq (.var 1) (.konst 0)) (.eq (.var 1) (.konst 1))) .fls)

theorem contradictory_guard_zeuge (values : Assignment Nat) :
    (normalize 8 contradictory).val = .tru ∧ contradictory.denote values := by
  have shape : (normalize 8 contradictory).val = .tru := rfl
  exact ⟨shape, ((normalize 8 contradictory).property values).mp (by rw [shape]; trivial)⟩

theorem prepared_sound_zeuge (values : Assignment Nat) : original.denote values :=
  Snapshot.prepared_sound original (by
    have shape : (Snapshot.prepared original).val = .tru := rfl
    rw [shape]; trivial) values

theorem metered_sound_zeuge : (LProp.eq (.konst 7) (.konst 7) : LProp Nat).denote (fun _ => 0) :=
  Snapshot.metered_sound _ 128 (by rfl)

/-- Sampling cannot certify the true universal range claim, and cannot refute
    the false existential claim. Both remain unknown for the real decision. -/
theorem evaluate_universal_unknown_zeuge :
    evaluate (.all 0 (.eq (.var 0) (.konst 0)) : LProp Nat) (fun _ => 0) = .unknown := rfl

theorem evaluate_existential_unknown_zeuge :
    evaluate (.ex 0 (.eq (.var 0) (.konst 1)) : LProp Nat) (fun _ => 0) = .unknown := rfl

end Gabbro.Grammatik.Vertraege.Pruefer.ReductionWitness
