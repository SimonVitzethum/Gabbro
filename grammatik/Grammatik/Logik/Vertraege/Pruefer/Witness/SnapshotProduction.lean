module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.Selection
public import Grammatik.Logik.Vertraege.Pruefer.Witness.Control

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.SnapshotProductionWitness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Frag.Symbolic Pruefer.Symbolic SelectionWitness

abbrev u32 : Ty := .int 0 (2 ^ 32 - 1)
abbrev declaration : Deklaration :=
  { Witness.u32Declaration with
    sigNr := fun _ =>
      { params := [u32], erg := some u32, gruende := 0
        haelt := [], schreibt := fun _ => false, gschreibt := fun name => !name
        konsumiert := [], produziert := [] }
    passt_ok := fun _ _ impossible => by cases impossible
    invarianten_gehalten := fun _ item => nomatch item }

def access (name : declaration.Glob) : gdarf declaration name [] := fun _ member => nomatch member

def initializer (valid : Bool) : Expr declaration [u32] [] (.int 0 10) :=
  if valid then .eng (.add (.glob false (access false)) (.lit 1)) 0 10 (.glob false (access false))
  else .widen (by decide) (by decide) (.lit 9)

def body (valid : Bool) : Endblock declaration (vertragVon declaration ()) false [u32] [] :=
  .cons (.assignGlob false (initializer valid) rfl (access false))
    (.ret (.val (.var .here)) (List.Perm.refl _))

/-- A nondegenerate full-width argument, a real mutable global, and an old/new
    relation. The invalid variant writes nine under the same declared contract. -/
def program (valid : Bool) : Programm declaration where
  invariante := fun item => nomatch item
  requires := fun _ => .lt (.glob false (access false)) (.lit 10)
  ensures := fun _ => .eq (.glob false (access false)) (.add (.oldG false (access false)) (.lit 1))
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

def invariants (valid : Bool) : InvariantFormula (program valid) [] :=
  (invariantFormula (program valid) []).toOption.get (by rfl)

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
  .and (.eq stored (.add saved (.konst 1))) .tru

def validFormula : LProp (Key declaration Nat) :=
  let source : LTerm (Key declaration Nat) := .add memory (.konst 1)
  let range : LProp (Key declaration Nat) := .and (.le (.konst 0) source) (.le source (.konst 10))
  let selected : LTerm (Key declaration Nat) := .var (.inr 2)
  .all (.inr 2) (.imp
    (.and (.and (.le (.konst 0) selected) (.le selected (.konst 10)))
      (.and (.imp range (.eq selected source)) (.imp (.not range) (.eq selected memory))))
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
      ∀ selected : Int,
        ((0 ≤ selected ∧ selected ≤ 10) ∧
          (((0 ≤ values (.inl (.glob false)) + 1 ∧ values (.inl (.glob false)) + 1 ≤ 10) →
            selected = values (.inl (.glob false)) + 1) ∧
           (¬ (0 ≤ values (.inl (.glob false)) + 1 ∧ values (.inl (.glob false)) + 1 ≤ 10) →
            selected = values (.inl (.glob false))))) →
        ∀ stored : Int, stored = selected → stored = values (.inr 1) + 1 ∧ True
  intro typed _ unfinished anchored selected relation stored same
  have fits : 0 ≤ values (.inl (.glob false)) + 1 ∧ values (.inl (.glob false)) + 1 ≤ 10 := by omega
  have defined := relation.2.1 fits
  exact ⟨by omega, trivial⟩

theorem original_negated_vc_zeuge : ¬ (matrix false).denote (fun _ => 0) := by
  unfold matrix
  rw [invalid_shape]
  with_unfolding_all
    change ¬ (((0 ≤ (0 : Int) ∧ 0 ≤ 10) ∧ True) →
      ((0 ≤ (0 : Int) ∧ 0 ≤ 2 ^ 32 - 1) ∧ True) → (0 : Int) < 10 →
      ((0 : Int) = 0 ∧ True) → ∀ stored : Int, stored = 9 → stored = 0 + 1 ∧ True)
  intro valid
  have impossible := valid (by decide) (by decide) (by decide) ⟨rfl, trivial⟩ 9 rfl
  omega

theorem zeroCounterexample_complete_zeuge :
    (Snapshot.zeroCounterexample (matrix false) (lower (matrix false)) (lower_denote _)).isSome = true :=
  Snapshot.zeroCounterexample_complete _ _ (lower_denote _) original_negated_vc_zeuge

theorem zeroCounterexample_sound_zeuge : ¬ (matrix false).denote (fun _ => 0) :=
  Snapshot.zeroCounterexample_sound _ _ (lower_denote _) zeroCounterexample_complete_zeuge

theorem refusal_counterexample_sound_zeuge :
    Snapshot.refusal (matrix false) (lower (matrix false)) (lower_denote _) "outside the decidable fragment" =
      .invalid Snapshot.counterexampleMessage ∧ ¬ (matrix false).denote (fun _ => 0) := by
  have diagnostic : Snapshot.refusal (matrix false) (lower (matrix false)) (lower_denote _)
      "outside the decidable fragment" = .invalid Snapshot.counterexampleMessage := by
    have present := zeroCounterexample_complete_zeuge
    unfold Snapshot.refusal
    cases found : Snapshot.zeroCounterexample (matrix false) (lower (matrix false)) (lower_denote _) with
    | none => rw [found] at present; cases present
    | some proof => rfl
  exact ⟨diagnostic, Snapshot.refusal_counterexample_sound _ _ (lower_denote _) _ diagnostic⟩

theorem environment_at_success_zeuge :
    (checkEnvironmentAt (program true) (SperrInv.leer declaration) symbols futureBounded (some region)
      (policy true) (fun _ => none) budget none (invariants true)).toOption.isSome = true := by
  apply environment_at_success (program true) (SperrInv.leer declaration) symbols futureBounded
    (some region) (policy true) (fun _ => none) budget none (invariants true)
    (requirement true) (by rfl) (certificate true) (compiled_result true)
  exact (close_decide_true_iff _).mpr (fun values => (lower_denote _ values).mpr (original_valid values))

theorem environment_checked :
    (checkEnvironment (program true) (SperrInv.leer declaration) symbols bounded (basePolicy true)
      (fun _ => none) budget none (invariants true)).toOption.isSome = true := by
  obtain ⟨checked, success⟩ := success_of_isSome _ environment_at_success_zeuge
  unfold checkEnvironment
  have planned : snapshotPlan ((program true).ensures ()) = .ok (some [.glob false]) := rfl
  rw [planned]
  dsimp only [bind, Except.bind]
  rw [success]
  rfl

theorem function_checked :
    (checkFunction (program true) (SperrInv.leer declaration) (fun _ => none) budget none ()).toOption.isSome = true := by
  apply function_success
  · rfl
  · with_unfolding_all rfl
  · apply execution_success (program true) (SperrInv.leer declaration) (fun _ => none) budget none ()
      (by rfl) (invariants true) (by rfl)
      ((parameters (D := declaration) 0 0 [u32]).toOption.get (by rfl)) (by rfl)
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
