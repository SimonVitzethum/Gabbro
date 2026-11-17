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

theorem metered_sound_zeuge : (LProp.all 0 (.le (.var 0) (.var 0)) : LProp Nat).denote (fun _ => 0) :=
  Snapshot.metered_sound _ 1000000 (by rfl)

theorem conjunct_zeuge (values : Assignment Nat) :
    ∃ proof, conjunct (.and (.le (.konst 0) (.var 0)) (.le (.var 0) (.konst (2 ^ 32 - 1))))
      (.le (.var 0) (.konst (2 ^ 32 - 1))) = some proof ∧
      ((0 ≤ values 0 ∧ values 0 ≤ 2 ^ 32 - 1) → values 0 ≤ 2 ^ 32 - 1) := by
  exact ⟨_, rfl, fun valid => valid.2⟩

/-- Truth at one sampled value cannot certify a universal claim, and falsehood
    at one sampled value cannot refute an existential claim. Both remain unknown for the real decision. -/
theorem evaluate_universal_unknown_zeuge :
    evaluate (.all 0 (.eq (.var 0) (.konst 0)) : LProp Nat) (fun _ => 0) = .unknown := rfl

theorem evaluate_existential_unknown_zeuge :
    evaluate (.ex 0 (.eq (.var 0) (.konst 1)) : LProp Nat) (fun _ => 0) = .unknown := rfl

theorem termKeys_eq_variables_zeuge :
    VC.termKeys (LTerm.add (.var (0 : Nat)) (.scale 7 (.var 1))) =
      (LTerm.add (.var (0 : Nat)) (.scale 7 (.var 1))).variables := termKeys_eq_variables _

theorem truth_denote_zeuge (values : Assignment Nat) :
    (Reduce.truth true : LProp Nat).denote values ↔ true = true := Reduce.truth_denote true values

theorem evaluate_true_zeuge (values : Assignment Nat) :
    ∃ proof, evaluate (normalize 8 original).val values = .yes proof :=
  evaluate_true _ _ (normalize_zeuge values).1

theorem closure_of_valid_zeuge (values : Assignment Nat) :
    (Modell.universalClosure [0] original).denote values :=
  Snapshot.closure_of_valid [0] original prepared_sound_zeuge values

theorem prepared_of_valid_zeuge (values : Assignment Nat) :
    (Snapshot.prepared original).val.denote values :=
  Snapshot.prepared_of_valid original prepared_sound_zeuge values

end Gabbro.Grammatik.Vertraege.Pruefer.ReductionWitness
