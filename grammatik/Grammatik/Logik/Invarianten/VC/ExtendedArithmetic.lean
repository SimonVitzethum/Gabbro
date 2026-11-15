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

attribute [local irreducible] lower
attribute [local semireducible] extendedEnd extendedStatement extendedBlock
attribute [local irreducible] freshImplication conj

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

private theorem freshImplication_iff {D : Deklaration} (kind : Ty) (value : Wert D kind)
    (guard : LProp (Observation D)) (post : QF (Observation D))
    (values : Assignment (Observation D)) :
    (freshImplication kind value guard post).denote values ↔
      (guard.denote values → post.denote values) := by
  constructor
  · intro checked selected
    exact freshImplication_sound kind value guard post values checked selected
  · intro implication
    rw [freshImplication, dropLocalQF_denote, lower_denote]
    intro number _
    have projection : (fun key => (Assignment.bind (dropBase values) none number) (some key)) = values := by
      funext key
      simp [Assignment.bind, dropBase]
    change (quoteQF (liftLocalQF (lower guard))).denote _ →
      (quoteQF (liftLocalQF post)).denote _
    rw [quoteQF_denote, liftLocalQF_denote, lower_denote, quoteQF_denote, liftLocalQF_denote]
    simpa only [projection] using implication

private def snapshots {D : Deklaration} {kind : Ty} (items : List (Wert D kind))
    (relation : Wert D kind → LProp (Observation D))
    (continuation : Wert D kind → QF (Observation D)) : QF (Observation D) :=
  items.foldr (fun value rest => conj (freshImplication kind value (relation value)
    (continuation value)) rest) .tru

private theorem snapshots_denote {D : Deklaration} {kind : Ty} (items : List (Wert D kind))
    (relation : Wert D kind → LProp (Observation D))
    (continuation : Wert D kind → QF (Observation D)) (values : Assignment (Observation D)) :
    (snapshots items relation continuation).denote values ↔
      ∀ value ∈ items, (relation value).denote values → (continuation value).denote values := by
  induction items with
  | nil => simp [snapshots, QF.denote]
  | cons value items ih =>
      change (conj (freshImplication kind value (relation value) (continuation value))
        (snapshots items relation continuation)).denote values ↔ _
      rw [conj_denote, freshImplication_iff, ih]
      constructor
      · rintro ⟨head, tail⟩ current member
        rcases List.mem_cons.mp member with same | member
        · subst current; exact head
        · exact tail current member
      · intro all
        exact ⟨all value List.mem_cons_self,
          fun current member => all current (List.mem_cons_of_mem value member)⟩

private def temporaryFormula : QF (Observation declaration) :=
  snapshots (kind := .int 0 10) (integerValues 0 10 11)
    (fun value => .eq (.var (.glob false)) (.konst value.n))
    (fun value => post.subst (.glob false) (.konst value.n))

private theorem temporary_formula : temporaryCompiled.formula = temporaryFormula := rfl

theorem temporary_decided_zeuge :
    decideB (Extended.writerVC temporaryCompiled entry .tru) = true := by
  apply (close_decide_true_iff _).mpr
  intro values
  rw [writerMatrix, lower_denote]
  intro _
  rw [quoteQF_denote, lower_denote]
  intro initial
  rw [quoteQF_denote, temporary_formula, temporaryFormula, snapshots_denote]
  intro value _ selected
  simp only [LProp.denote, LTerm.denote] at selected
  simp only [post, lower_denote, entry, LProp.denote, LTerm.denote] at initial ⊢
  rw [subst_denote]
  simpa [entry, LProp.denote, LTerm.denote, Assignment.bind, ← selected] using initial.1

end Gabbro.Grammatik.Invarianten.VC.ExtendedWitness
