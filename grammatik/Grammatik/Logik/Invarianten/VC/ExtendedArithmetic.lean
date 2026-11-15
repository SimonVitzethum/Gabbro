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
attribute [local semireducible] extendedEnd extendedStatement extendedBlock integerEquality traverseCondition
attribute [local irreducible] freshImplication conj havoc

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

set_option maxHeartbeats 50000 in
private theorem temporary_formula : temporaryCompiled.formula = temporaryFormula := rfl

theorem temporary_decided_zeuge :
    decideB (Extended.writerVC temporaryCompiled entry .tru) = true := by
  apply (close_decide_true_iff _).mpr
  intro values
  rw [writerMatrix, lower_denote]
  intro _
  rw [quoteQF_denote, lower_denote]
  intro initial
  rw [quoteQF_denote, temporary_formula, temporaryFormula]
  apply (snapshots_denote (D := declaration) (kind := .int 0 10) _ _ _ values).mpr
  intro value _ selected
  simp only [LProp.denote, LTerm.denote] at selected
  simp only [post, lower_denote, entry, LProp.denote, LTerm.denote] at initial ⊢
  rw [subst_denote]
  simpa [lower_denote, entry, LProp.denote, LTerm.denote, Assignment.bind, ← selected] using initial.1

private theorem branchFormula_denote (test : LProp (Observation declaration))
    (yes no : QF (Observation declaration)) (values : Assignment (Observation declaration)) :
    (branchFormula test yes no).denote values ↔
      (test.denote values → yes.denote values) ∧ (¬ test.denote values → no.denote values) := by
  simp only [branchFormula, lower_denote, LProp.denote, quoteQF_denote]

private theorem stepFormula_preserves (terminal : QF (Observation declaration))
    (preserved : ∀ values, entry.denote values → terminal.denote values)
    (values : Assignment (Observation declaration))
    (initial : entry.denote values) (guarded : guardFormula.denote values) :
    (stepFormula terminal).denote values := by
  rw [stepFormula, lower_denote]
  constructor
  · intro _
    rw [quoteQF_denote, subst_denote]
    apply preserved
    simp only [entry, guardFormula, LProp.denote, LTerm.denote] at initial guarded
    simpa [entry, LProp.denote, LTerm.denote, Assignment.bind, stepTerm] using
      (show values (.glob false) + 1 ≤ values (.glob true) by omega)
  · intro _
    rw [quoteQF_denote, subst_denote]
    apply preserved
    simpa [entry, LProp.denote, LTerm.denote, Assignment.bind] using initial

private def traverseFormula : Nat → QF (Observation declaration)
  | 0 => branchFormula .tru post .tru
  | count + 1 => branchFormula .tru
      (branchFormula guardFormula (stepFormula (traverseFormula count)) (traverseFormula count)) .tru

set_option maxHeartbeats 50000 in
private theorem traverse_formula : traverseCompiled.formula = traverseFormula 3 := rfl

private theorem traverse_preserves (count : Nat) :
    ∀ values, entry.denote values → (traverseFormula count).denote values := by
  induction count with
  | zero =>
      intro values initial
      simpa [traverseFormula, branchFormula_denote, LProp.denote, QF.denote, post, lower_denote] using initial
  | succ count ih =>
      intro values initial
      rw [traverseFormula, branchFormula_denote]
      refine ⟨fun _ => ?_, fun impossible => (impossible trivial).elim⟩
      rw [branchFormula_denote]
      exact ⟨stepFormula_preserves _ ih values initial, fun _ => ih values initial⟩

theorem traverse_decided_zeuge :
    decideB (Extended.writerVC traverseCompiled entry .tru) = true := by
  apply (close_decide_true_iff _).mpr
  intro values
  rw [writerMatrix, lower_denote]
  intro _
  rw [quoteQF_denote, lower_denote]
  intro initial
  rw [quoteQF_denote, traverse_formula]
  exact traverse_preserves 3 values initial.1

private def inductiveBranch : QF (Observation declaration) :=
  branchFormula (.not guardFormula) post (conj (stepFormula post) post)

private def inductiveCheck : QF (Observation declaration) :=
  lower (.imp (.and (typeFacts (qfKeys post ++ qfKeys inductiveBranch)) (quoteQF post))
    (quoteQF inductiveBranch))

private theorem inductive_formula : inductiveCompiled.formula =
    conj post (conj (havoc (fun _ => true) inductiveCheck) .tru) := rfl

theorem inductive_decided_zeuge :
    decideB (Extended.writerVC inductiveCompiled entry .tru) = true := by
  apply (close_decide_true_iff _).mpr
  intro values
  rw [writerMatrix, lower_denote]
  intro _
  rw [quoteQF_denote, lower_denote]
  intro initial
  rw [quoteQF_denote, inductive_formula, conj_denote, conj_denote]
  refine ⟨(lower_denote _ _).mpr initial.1, ?_, trivial⟩
  apply havoc_of_valid
  intro other
  rw [inductiveCheck, lower_denote]
  intro entry
  have holds := (lower_denote _ _).mp ((quoteQF_denote _ _).mp entry.2)
  rw [quoteQF_denote, inductiveBranch, branchFormula_denote]
  refine ⟨fun _ => (lower_denote _ _).mpr holds, fun guarded => ?_⟩
  rw [conj_denote]
  refine ⟨stepFormula_preserves _ (fun _ valid => (lower_denote _ _).mpr valid) other holds ?_,
    (lower_denote _ _).mpr holds⟩
  simpa only [LProp.denote, not_not] using guarded

private def mutationRelation (captured : Zahl 0 10) (next : Zahl 0 10) : LProp (Observation declaration) :=
  let term : LTerm (Observation declaration) := .add (.konst captured.n) (.konst 1)
  let fits : LProp (Observation declaration) := .and (.le (.konst 0) term) (.le term (.konst 10))
  .and (.imp fits (.eq term (.konst next.n)))
    (.imp (.not fits) (.eq (.konst captured.n) (.konst next.n)))

private def mutationFormula (captured : Zahl 0 10) : QF (Observation declaration) :=
  snapshots (kind := .int 0 10) (integerValues 0 10 11) (mutationRelation captured)
    (fun next => post.subst (.glob false) (.konst next.n))

private def mutableFormula : QF (Observation declaration) :=
  snapshots (kind := .int 0 10) (integerValues 0 10 11)
    (fun value => .eq (.var (.glob false)) (.konst value.n))
    (fun value => branchFormula (.lt (.konst value.n) (.var (.glob true))) (mutationFormula value) post)

set_option maxHeartbeats 50000 in
private theorem mutable_formula : mutableCompiled.formula = mutableFormula := rfl

theorem mutable_decided_zeuge :
    decideB (Extended.writerVC mutableCompiled entry .tru) = true := by
  apply (close_decide_true_iff _).mpr
  intro values
  rw [writerMatrix, lower_denote]
  intro _
  rw [quoteQF_denote, lower_denote]
  intro initial
  rw [quoteQF_denote, mutable_formula, mutableFormula]
  apply (snapshots_denote (kind := .int 0 10) _ _ _ values).mpr
  intro captured _ selected
  rw [branchFormula_denote]
  refine ⟨fun guarded => ?_, fun _ => (lower_denote _ _).mpr initial.1⟩
  unfold mutationFormula
  apply (snapshots_denote (kind := .int 0 10) _ _ _ values).mpr
  intro next _ relation
  simp only [mutationRelation, LProp.denote, LTerm.denote] at relation
  simp only [LProp.denote, LTerm.denote] at selected guarded
  have bound : next.n ≤ values (.glob true) := by
    by_cases fits : 0 ≤ captured.n + 1 ∧ captured.n + 1 ≤ 10
    · have := relation.1 fits
      omega
    · have := relation.2 fits
      omega
  rw [subst_denote, post, lower_denote]
  simpa [entry, LProp.denote, LTerm.denote, Assignment.bind] using bound

private def booleanFormula : QF (Observation declaration) :=
  snapshots (kind := .bool) ([false, true] : List Bool)
    (fun flag => if wahr? flag then guardFormula else .not guardFormula)
    (fun flag => branchFormula (if wahr? flag then .tru else .fls) (stepFormula post) post)

private theorem boolean_formula : booleanCompiled.formula = booleanFormula := rfl

theorem boolean_initializer_decided_zeuge :
    decideB (Extended.writerVC booleanCompiled entry .tru) = true := by
  apply (close_decide_true_iff _).mpr
  intro values
  rw [writerMatrix, lower_denote]
  intro _
  rw [quoteQF_denote, lower_denote]
  intro initial
  rw [quoteQF_denote, boolean_formula, booleanFormula]
  apply (snapshots_denote (kind := .bool) _ _ _ values).mpr
  intro flag _ selected
  cases flag with
  | false =>
      simpa [branchFormula_denote, LProp.denote, post, lower_denote] using initial.1
  | true =>
      rw [branchFormula_denote]
      exact ⟨fun _ => stepFormula_preserves _ (fun _ valid => (lower_denote _ _).mpr valid)
        values initial.1 selected, fun impossible => (impossible trivial).elim⟩

end Gabbro.Grammatik.Invarianten.VC.ExtendedWitness
