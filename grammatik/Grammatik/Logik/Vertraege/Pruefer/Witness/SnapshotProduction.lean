module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.Selection
public import Grammatik.Logik.Vertraege.Pruefer.Witness.Control

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.SnapshotProductionWitness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Frag.Symbolic Pruefer.Symbolic SelectionWitness

attribute [local implicit_reducible] Witness.u32Declaration

abbrev u32 : Ty := .int 0 (2 ^ 32 - 1)
abbrev declaration : Deklaration :=
  { Witness.u32Declaration with
    Fn := Unit
    Glob := Bool
    sig := fun _ => 0
    passt := fun _ _ => false
    sigNr := fun _ =>
      { params := [u32], erg := some u32, gruende := 0
        haelt := [], schreibt := fun _ => false, gschreibt := fun name => !name
        konsumiert := [], produziert := [] }
    passt_ok := fun _ _ impossible => by cases impossible
    invarianten_gehalten := fun _ item => nomatch item }

def access (name : declaration.Glob) : gdarf declaration name [] := fun _ member => nomatch member

def initializer (valid : Bool) : Expr declaration [u32] [] (.int 0 10) :=
  if valid then .glob false (access false)
  else .widen (by decide) (by decide) (.lit 9)

def body (valid : Bool) : Endblock declaration (vertragVon declaration ()) false [u32] [] :=
  .cons (.assignGlob false (initializer valid) rfl (access false))
    (.ret (.val (.var .here)) (List.Perm.refl _))

/-- A nondegenerate full-width argument, a real mutable global, and an old/new
    relation. The invalid variant writes nine under the same declared contract. -/
def program (valid : Bool) : Programm declaration where
  invariante := fun item => nomatch item
  requires := fun _ => .lt (.glob false (access false)) (.lit 10)
  ensures := fun _ => .eq (.glob false (access false)) (.oldG false (access false))
  rumpf := fun _ => body valid

abbrev symbols : SymEnv declaration Nat (declaration.params ()) := .cons (.integer (.var 0)) .nil
def bounded : symbols.Bounded 1 :=
  ⟨fun key member => by have same := List.mem_singleton.mp member; subst key; decide, trivial⟩
def futureBounded : symbols.Bounded 2 := symbols.bounded_mono bounded (by decide)
def region : Snapshot.Region declaration 2 := ⟨1, [.glob false], by decide⟩
abbrev budget : VCBudget := { expansion := 0 }

def basePolicy (valid : Bool) := requiresPolicy (program valid) (entryContext symbols bounded)
def policy (valid : Bool) := (basePolicy valid).refine (by decide : 1 ≤ 2)
  (entryContext symbols futureBounded (some region)) (fun _ _ present => present.1)

def invariants (valid : Bool) : InvariantFormula (program valid) (declaration.invs.filter (schuldet ())) :=
  (invariantFormula (program valid) (declaration.invs.filter (schuldet ()))).toOption.get (by rfl)

def compiled (valid : Bool) := ending (policy valid)
  (Invarianten.Pruefer.lockFormula (SperrInv.leer declaration) (fun _ => none)) budget none 128
  (body valid) symbols futureBounded (contractGoals (program valid) () symbols futureBounded (invariants valid) (some region))

theorem compiled_present (valid : Bool) : (compiled valid).toOption.isSome = true := by
  cases valid <;> with_unfolding_all rfl

def certificate (valid : Bool) := (compiled valid).toOption.get (compiled_present valid)

theorem compiled_result (valid : Bool) : compiled valid = .ok (certificate valid) := by
  have present := compiled_present valid
  cases checked : compiled valid with
  | error cause => rw [checked] at present; cases present
  | ok value => simp only [certificate, checked, Except.toOption, Option.get_some]

abbrev memory : LTerm (Key declaration Nat) := .var (.inl (.glob false))
abbrev saved : LTerm (Key declaration Nat) := .var (.inr 1)
def postFormula (stored : LTerm (Key declaration Nat)) : LProp (Key declaration Nat) :=
  .and (.eq stored saved) .tru

def validFormula : LProp (Key declaration Nat) :=
  let selected : LTerm (Key declaration Nat) := .var (.inr 2)
  .all (.inr 2) (.imp (.and
    (.and (.le (.konst 0) selected) (.le selected (.konst 10))) (.eq selected memory))
    (.all (.inr 3) (.imp (.eq (.var (.inr 3)) selected) (postFormula (.var (.inr 3))))))

def invalidFormula : LProp (Key declaration Nat) :=
  .all (.inr 2) (.imp (.eq (.var (.inr 2)) (.konst 9)) (postFormula (.var (.inr 2))))

theorem valid_shape : (certificate true).formula = validFormula := by with_unfolding_all rfl
theorem invalid_shape : (certificate false).formula = invalidFormula := by with_unfolding_all rfl

def requirement (valid : Bool) :=
  (Invarianten.Frag.Symbolic.translate ((program valid).requires ()) symbols).toOption.get (by rfl)

def matrix (valid : Bool) : LProp (Key declaration Nat) :=
  entryVC symbols (requirement valid).payload (snapshotGuard (some region) (certificate valid).formula)

theorem original_valid (values : Assignment (Key declaration Nat)) : (matrix true).denote values := by
  unfold matrix
  rw [valid_shape]
  with_unfolding_all
    change ((0 ≤ values (.inl (.glob false)) ∧ values (.inl (.glob false)) ≤ 10) ∧ True) →
      ((0 ≤ values (.inr 0) ∧ values (.inr 0) ≤ 2 ^ 32 - 1) ∧ True) →
      values (.inl (.glob false)) < 10 → (values (.inr 1) = values (.inl (.glob false)) ∧ True) →
      ∀ selected : Int, ((0 ≤ selected ∧ selected ≤ 10) ∧ selected = values (.inl (.glob false))) →
        ∀ stored : Int, stored = selected → stored = values (.inr 1) ∧ True
  intro _ _ _ anchored selected initialized stored same
  exact ⟨same.trans (initialized.2.trans anchored.1.symm), trivial⟩

theorem original_negated_vc_zeuge : ¬ (matrix false).denote (fun _ => 0) := by
  unfold matrix
  rw [invalid_shape]
  with_unfolding_all
    change ¬ (((0 ≤ (0 : Int) ∧ 0 ≤ 10) ∧ True) →
      ((0 ≤ (0 : Int) ∧ 0 ≤ 2 ^ 32 - 1) ∧ True) → (0 : Int) < 10 →
      ((0 : Int) = 0 ∧ True) → ∀ stored : Int, stored = 9 → stored = 0 ∧ True)
  intro valid
  have impossible := valid (by decide) (by decide) (by decide) ⟨rfl, trivial⟩ 9 rfl
  omega

theorem zeroCounterexample_present_zeuge : (Snapshot.zeroCounterexample (matrix false)).isSome = true := by
  rw [show matrix false = entryVC symbols (requirement false).payload
    (snapshotGuard (some region) invalidFormula) by unfold matrix; rw [invalid_shape]]
  rfl

theorem zeroCounterexample_sound_zeuge : ¬ (matrix false).denote (fun _ => 0) :=
  Snapshot.zeroCounterexample_sound _ zeroCounterexample_present_zeuge

theorem rejectCounterexample_sound_zeuge :
    Snapshot.rejectCounterexample true (matrix false) = .error (.invalid Snapshot.counterexampleMessage) ∧
      ¬ (matrix false).denote (fun _ => 0) := by
  have diagnostic : Snapshot.rejectCounterexample true (matrix false) =
      .error (.invalid Snapshot.counterexampleMessage) := by
    have present := zeroCounterexample_present_zeuge
    unfold Snapshot.rejectCounterexample
    cases found : Snapshot.zeroCounterexample (matrix false) with
    | none => rw [found] at present; cases present
    | some proof => rfl
  exact ⟨diagnostic, Snapshot.rejectCounterexample_sound _ diagnostic⟩

theorem prepared_true_zeuge : (Snapshot.prepared (matrix true)).val = .tru := by
  unfold matrix
  rw [valid_shape]
  rfl

theorem rejectCounterexample_of_valid_zeuge :
    Snapshot.rejectCounterexample true (matrix true) = .ok () :=
  Snapshot.rejectCounterexample_of_valid true _ (original_valid _)

section NumericGate

attribute [local irreducible] entryVC certificate environmentDecision lower close decideB

theorem numeric_decided_zeuge :
    decideB (close (lower (matrix true))) (close_closed _) = true := by
  apply (close_decide_true_iff (lower (matrix true))).mpr
  intro values
  exact (lower_denote (matrix true) values).mpr (original_valid values)

theorem environmentDecision_of_decided_zeuge (reason : String) :
    (environmentDecision false (matrix true) reason).toOption.isSome = true :=
  environmentDecision_of_decided (matrix true) reason numeric_decided_zeuge

end NumericGate

attribute [local irreducible] entryVC certificate checkEnvironmentAt
attribute [local implicit_reducible] entryContext

theorem environment_at_success_zeuge :
    (checkEnvironmentAt (program true) (SperrInv.leer declaration) symbols futureBounded (some region)
      (policy true) (fun _ => none) budget none (invariants true)).toOption.isSome = true := by
  apply environment_at_success (program true) (SperrInv.leer declaration) symbols futureBounded
    (some region) (policy true) (fun _ => none) budget none (invariants true)
    (requirement true) (by rfl) (certificate true) (compiled_result true)
  change (Snapshot.decide (matrix true) 1000000 _).toOption.isSome = true
  exact Snapshot.decide_of_prepared_true _ _ _ prepared_true_zeuge

theorem environment_checked :
    (checkEnvironment (program true) (SperrInv.leer declaration) symbols bounded (basePolicy true)
      (fun _ => none) budget none (invariants true)).toOption.isSome = true := by
  apply environment_snapshot_success (program true) (SperrInv.leer declaration) symbols bounded (basePolicy true)
    (fun _ => none) budget none (invariants true) [.glob false] (by rfl)
  exact environment_at_success_zeuge

theorem function_checked :
    (checkFunction (program true) (SperrInv.leer declaration) (fun _ => none) budget none ()).toOption.isSome = true := by
  with_unfolding_all
    apply function_success
    · rfl
    · with_unfolding_all rfl
    · apply execution_success (program true) (SperrInv.leer declaration) (fun _ => none) budget none ()
        (by rfl) (invariants true) (by rfl)
        ((parameters (D := declaration) 0 0 [u32]).toOption.get (by with_unfolding_all rfl)) (by with_unfolding_all rfl)
      · change 1 ≤ 16384; decide
      · rintro ⟨selected, member⟩
        have same : selected = symbols := List.mem_singleton.mp member
        subst selected
        exact environment_checked

/-- Production accepts every u32 argument, with a genuine old/new global post. -/
theorem old_global_accepted_zeuge :
    KontrakteGeprueftB (program true) (SperrInv.leer declaration) [()] (fun _ => none) budget = true := by
  apply contracts_success
  intro f
  cases f
  exact function_checked

end Gabbro.Grammatik.Vertraege.Pruefer.SnapshotProductionWitness
