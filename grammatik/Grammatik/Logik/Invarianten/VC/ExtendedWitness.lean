module

public import Grammatik.Logik.Invarianten.VC.ExtendedFixtures
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import all Batteries.Data.Except

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

namespace Gabbro.Grammatik.Invarianten.VC.ExtendedWitness

open Frag Elim Elim.Korrekt Modell
open Gabbro.Grammatik.Invarianten.VC.Witness

private def stepTerm : LTerm (Observation declaration) :=
  .add (.var (.glob false)) (.konst 1)

private def stepRange : LProp (Observation declaration) :=
  .and (.le (.konst 0) stepTerm) (.le stepTerm (.konst 10))

private def stepFormula (terminal : QF (Observation declaration)) : QF (Observation declaration) :=
  lower (.and (.imp stepRange (quoteQF (terminal.subst (.glob false) stepTerm)))
    (.imp (.not stepRange) (quoteQF (terminal.subst (.glob false) (.var (.glob false))))))

private def branchFormula (test : LProp (Observation declaration))
    (yes no : QF (Observation declaration)) : QF (Observation declaration) :=
  lower (.and (.imp test (quoteQF yes)) (.imp (.not test) (quoteQF no)))

private def retryFormula (test : LProp (Observation declaration)) : Nat → QF (Observation declaration)
  | 0 => branchFormula test post post
  | count + 1 => branchFormula test post (stepFormula (retryFormula test count))

private def guardFormula : LProp (Observation declaration) :=
  .lt (.var (.glob false)) (.var (.glob true))

private theorem bounded_formula :
    boundedCompiled.formula = retryFormula (.not guardFormula) 2 := rfl

private theorem overflowing_formula :
    overflowingCompiled.formula = retryFormula .fls 2 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem bounded_decided_zeuge :
    decideB (Extended.writerVC boundedCompiled entry .tru) = true := by
  apply (close_decide_true_iff _).mpr
  intro values
  rw [writerMatrix, lower_denote]
  intro _
  rw [quoteQF_denote, lower_denote]
  intro initial
  rw [quoteQF_denote, bounded_formula]
  simp only [retryFormula, branchFormula, stepFormula, lower_denote, LProp.denote,
    quoteQF_denote, subst_denote, post, entry, guardFormula, stepRange, stepTerm,
    LTerm.denote] at *
  simp [Assignment.bind] at * <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem overflow_decided_zeuge :
    decideB (Extended.writerVC overflowingCompiled entry .tru) = false := by
  apply (close_decide_false_iff _).mpr
  refine ⟨assignment counterexampleWorld, ?_⟩
  rw [writerMatrix, lower_denote]
  intro valid
  have step := (quoteQF_denote _ _).mp (valid (typeFacts_sound _ counterexampleWorld))
  rw [lower_denote] at step
  have initial : entry.denote (assignment counterexampleWorld) ∧ True :=
    ⟨by change (4 : Int) ≤ 4; decide, trivial⟩
  have result := (quoteQF_denote _ _).mp (step initial)
  rw [overflowing_formula] at result
  norm_num [retryFormula, branchFormula, stepFormula, lower_denote, quoteQF_denote,
    subst_denote, stepRange, stepTerm, post, entry, LProp.denote, LTerm.denote,
    Assignment.bind, assignment, counterexampleWorld, scalarValue,
    declaration, Frag.Witness.declaration] at result

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem temporary_decided_zeuge :
    decideB (Extended.writerVC temporaryCompiled entry .tru) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem mutable_decided_zeuge :
    decideB (Extended.writerVC mutableCompiled entry .tru) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem traverse_decided_zeuge :
    decideB (Extended.writerVC traverseCompiled entry .tru) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem inductive_decided_zeuge :
    decideB (Extended.writerVC inductiveCompiled entry .tru) = true := by decide +kernel

/-- The false decision has both an extracted arithmetic assignment and an
    actual typed G execution that destroys the invariant. -/
theorem overflow_assignment_zeuge :
    ∃ values : Assignment (Observation declaration),
      Extended.writerCounterexample overflowingCompiled entry .tru = some values :=
  Extended.writerCounterexample_complete overflowingCompiled entry .tru overflow_decided_zeuge

theorem overflow_execution_zeuge :
    (match execEnd oracle 0 calls overflowingWriter counterexampleWorld .nil with
      | .zurueck next _ => eval next invariant next .nil
      | _ => true) = false := by decide +kernel

theorem temporary_execution_zeuge :
    (match execEnd oracle 0 calls temporaryWriter counterexampleWorld .nil with
      | .zurueck next _ => eval next invariant next .nil
      | _ => false) = true := by decide +kernel

/-- An over-budget loop is a definite refusal, not an unchecked fallback. -/
theorem over_budget_refused_zeuge :
    (extendedEnd program noFacts noLockFacts 0 none 64 boundedWriter .nil post).toOption.isNone = true := by
  decide +kernel

theorem boolean_initializer_decided_zeuge :
    decideB (Extended.writerVC booleanCompiled entry .tru) = true := by decide +kernel

theorem conditional_initializer_decided_zeuge :
    decideB (Extended.writerVC (conditionalCompiled true) entry .tru) = true := by decide +kernel

theorem conditional_initializer_refused_zeuge :
    decideB (Extended.writerVC (conditionalCompiled false) entry .tru) = false := by decide +kernel

theorem conditional_initializer_counterexample_zeuge :
    eval counterexampleWorld invariant counterexampleWorld .nil = true ∧
    (match execEnd oracle 0 calls (conditionalWriter false) counterexampleWorld .nil with
      | .zurueck next _ => eval next invariant next .nil
      | _ => true) = false := by decide +kernel

theorem traversal_contract_accepted_zeuge :
    Vertraege.Pruefer.KontrakteGeprueftB (traversalProgram true)
      (SperrInv.leer declaration) [()] = true := by decide +kernel

theorem traversal_contract_refused_zeuge :
    Vertraege.Pruefer.KontrakteGeprueftB (traversalProgram false)
      (SperrInv.leer declaration) [()] = false := by decide +kernel

theorem traversal_logic_stop_zeuge :
    (match execEnd oracle 0 calls ((traversalProgram false).rumpf ()) counterexampleWorld .nil with
      | .logik .schleife => true
      | _ => false) = true := by decide +kernel

end Gabbro.Grammatik.Invarianten.VC.ExtendedWitness
