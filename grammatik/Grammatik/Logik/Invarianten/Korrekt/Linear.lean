module

public import Grammatik.Logik.Invarianten.Elim.Formula
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

public section

namespace Gabbro.Grammatik.Invarianten.Elim.Korrekt

open Frag

theorem foldTerm_denote (term : LTerm α) (values : Assignment α) :
    (foldTerm term).denote values = term.denote values := by
  unfold foldTerm
  cases h : term.constant? with
  | none => rfl
  | some value => exact (LTerm.constant?_sound h values).symm

theorem addTerm_denote (left right : LTerm α) (values : Assignment α) :
    (addTerm left right).denote values = left.denote values + right.denote values :=
  foldTerm_denote (.add left right) values

theorem subTerm_denote (left right : LTerm α) (values : Assignment α) :
    (subTerm left right).denote values = left.denote values - right.denote values :=
  foldTerm_denote (.sub left right) values

theorem scaleTerm_denote (coefficient : Int) (term : LTerm α) (values : Assignment α) :
    (scaleTerm coefficient term).denote values = coefficient * term.denote values := by
  by_cases h : coefficient = 0
  · simp [scaleTerm, h, LTerm.denote]
  · simp [scaleTerm, h, foldTerm_denote, LTerm.denote]

theorem splitVar_denote [DecidableEq α] (name : α) (term : LTerm α)
    (values : Assignment α) :
    term.denote values = (splitVar name term).1 * values name +
      (splitVar name term).2.denote values := by
  induction term with
  | var other =>
      by_cases h : other = name <;> simp [splitVar, h, LTerm.denote]
  | konst value => simp [splitVar, LTerm.denote]
  | add left right ihLeft ihRight =>
      simp only [splitVar, LTerm.denote, addTerm_denote]
      rw [ihLeft, ihRight]
      ring
  | sub left right ihLeft ihRight =>
      simp only [splitVar, LTerm.denote, subTerm_denote]
      rw [ihLeft, ihRight]
      ring
  | scale coefficient term ih =>
      simp only [splitVar, LTerm.denote, scaleTerm_denote]
      rw [ih]
      ring

theorem substTerm_denote [DecidableEq α] (name : α) (replacement term : LTerm α)
    (values : Assignment α) :
    (substTerm name replacement term).denote values =
      term.denote (values.bind name (replacement.denote values)) := by
  induction term with
  | var other =>
      by_cases h : other = name <;>
        simp [substTerm, h, LTerm.denote, Assignment.bind]
  | konst value => rfl
  | add left right ihLeft ihRight =>
      simp [substTerm, addTerm_denote, LTerm.denote, ihLeft, ihRight]
  | sub left right ihLeft ihRight =>
      simp [substTerm, subTerm_denote, LTerm.denote, ihLeft, ihRight]
  | scale coefficient term ih =>
      simp [substTerm, scaleTerm_denote, LTerm.denote, ih]

theorem relation_eval (relation : Relation) (value : Int) :
    relation.eval value = true ↔ relation.denote value := by
  cases relation <;> simp [Relation.eval, Relation.denote, Int.dvd_iff_emod_eq_zero]

theorem qf_eval (formula : QF α) (values : Assignment α) :
    formula.eval values = true ↔ formula.denote values := by
  induction formula <;> simp_all [QF.eval, QF.denote, relation_eval]

theorem truth_denote (value : Bool) (values : Assignment α) :
    (truth value : QF α).denote values ↔ value = true := by
  cases value <;> simp [truth, QF.denote]

theorem atom_denote (relation : Relation) (term : LTerm α) (values : Assignment α) :
    (atom relation term).denote values ↔ relation.denote (term.denote values) := by
  unfold atom
  cases h : term.constant? with
  | none => rfl
  | some value =>
      rw [truth_denote, relation_eval, LTerm.constant?_sound h values]

theorem conj_denote (left right : QF α) (values : Assignment α) :
    (conj left right).denote values ↔ left.denote values ∧ right.denote values := by
  cases left <;> cases right <;> simp [conj, QF.denote]

theorem disj_denote (left right : QF α) (values : Assignment α) :
    (disj left right).denote values ↔ left.denote values ∨ right.denote values := by
  cases left <;> cases right <;> simp [disj, QF.denote]

theorem neg_denote (formula : QF α) (values : Assignment α) :
    formula.neg.denote values ↔ ¬ formula.denote values := by
  classical
  induction formula with
  | tru => simp [QF.neg, QF.denote]
  | fls => simp [QF.neg, QF.denote]
  | atom relation term =>
      cases relation <;>
        simp [QF.neg, atom_denote, QF.denote, Relation.denote,
          subTerm_denote, scaleTerm_denote, LTerm.denote] <;> omega
  | conj left right ihLeft ihRight =>
      simp only [QF.neg, disj_denote, QF.denote, ihLeft, ihRight]
      tauto
  | disj left right ihLeft ihRight =>
      simp only [QF.neg, conj_denote, QF.denote, ihLeft, ihRight]
      tauto

theorem subst_denote [DecidableEq α] (name : α) (replacement : LTerm α)
    (formula : QF α) (values : Assignment α) :
    (formula.subst name replacement).denote values ↔
      formula.denote (values.bind name (replacement.denote values)) := by
  induction formula <;>
    simp_all [QF.subst, QF.denote, atom_denote, conj_denote, disj_denote, substTerm_denote]

theorem equalZero_denote (term : LTerm α) (values : Assignment α) :
    (equalZero term).denote values ↔ term.denote values = 0 := by
  simp only [equalZero, conj_denote, atom_denote, Relation.denote,
    subTerm_denote, scaleTerm_denote, LTerm.denote]
  omega

end Gabbro.Grammatik.Invarianten.Elim.Korrekt
