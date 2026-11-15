module

public import Grammatik.Logik.Invarianten.VC.ExtendedFixtures
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import all Batteries.Data.Except

@[expose] public section

set_option profiler true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000

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
set_option maxHeartbeats 10000 in
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
set_option maxHeartbeats 10000 in
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

end Gabbro.Grammatik.Invarianten.VC.ExtendedWitness
