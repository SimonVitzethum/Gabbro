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
set_option maxRecDepth 100000 in
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

private def inductiveBranch : QF (Observation declaration) :=
  branchFormula (.not guardFormula) post (conj (stepFormula post) post)

private def inductiveCheck : QF (Observation declaration) :=
  lower (.imp (.and (typeFacts (qfKeys post ++ qfKeys inductiveBranch)) (quoteQF post))
    (quoteQF inductiveBranch))

private theorem inductive_formula : inductiveCompiled.formula =
    conj post (conj (havoc (fun _ => true) inductiveCheck) .tru) := rfl

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

private def booleanFormula : QF (Observation declaration) :=
  snapshots (kind := .bool) ([false, true] : List Bool)
    (fun flag => if wahr? flag then guardFormula else .not guardFormula)
    (fun flag => branchFormula (if wahr? flag then .tru else .fls) (stepFormula post) post)

private theorem boolean_formula : booleanCompiled.formula = booleanFormula := rfl

private def bumpRelation (value : Zahl 0 10) : LProp (Observation declaration) :=
  .and (.imp stepRange (.eq stepTerm (.konst value.n)))
    (.imp (.not stepRange) (.eq (.var (.glob false)) (.konst value.n)))

private def conditionalRelation (preserves : Bool) (value : Zahl 0 10) : LProp (Observation declaration) :=
  let unchanged : LProp (Observation declaration) := .eq (.var (.glob false)) (.konst value.n)
  .and (.imp guardFormula (if preserves then bumpRelation value else unchanged))
    (.imp (.not guardFormula) (if preserves then unchanged else bumpRelation value))

private def conditionalFormula (preserves : Bool) : QF (Observation declaration) :=
  snapshots (kind := .int 0 10) (integerValues 0 10 11) (conditionalRelation preserves)
    (fun value => post.subst (.glob false) (.konst value.n))

set_option maxHeartbeats 50000 in
private theorem conditional_formula (preserves : Bool) :
    (conditionalCompiled preserves).formula = conditionalFormula preserves := by
  cases preserves <;> rfl

end Gabbro.Grammatik.Invarianten.VC.ExtendedWitness
