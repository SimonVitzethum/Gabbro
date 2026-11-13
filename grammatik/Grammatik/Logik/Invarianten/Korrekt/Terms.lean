module

public import Grammatik.Logik.Invarianten.Korrekt.Linear

public section

namespace Gabbro.Grammatik.Invarianten.Elim.Korrekt

open Frag

@[simp] theorem bind_same [DecidableEq α] (values : Assignment α) (name : α) (x : Int) :
    values.bind name x name = x := by simp [Assignment.bind]

@[simp] theorem bind_bind [DecidableEq α] (values : Assignment α) (name : α) (x y : Int) :
    (values.bind name x).bind name y = values.bind name y := by
  funext other
  by_cases h : other = name <;> simp [Assignment.bind, h]

/-- A constant term has zero coefficient, even before constant folding. -/
theorem constant_coefficient [DecidableEq α] (name : α) (term : LTerm α)
    {value : Int} (h : term.constant? = some value) : (splitVar name term).1 = 0 := by
  induction term generalizing value with
  | var other => simp [LTerm.constant?] at h
  | konst value => rfl
  | add left right ihLeft ihRight =>
      cases hl : left.constant? <;> cases hr : right.constant? <;>
        simp [LTerm.constant?, hl, hr] at h
      simp [splitVar, ihLeft hl, ihRight hr]
  | sub left right ihLeft ihRight =>
      cases hl : left.constant? <;> cases hr : right.constant? <;>
        simp [LTerm.constant?, hl, hr] at h
      simp [splitVar, ihLeft hl, ihRight hr]
  | scale coefficient term ih =>
      cases ht : term.constant? <;> simp [LTerm.constant?, ht] at h
      simp [splitVar, ih ht]

@[simp] theorem foldTerm_coefficient [DecidableEq α] (name : α) (term : LTerm α) :
    (splitVar name (foldTerm term)).1 = (splitVar name term).1 := by
  unfold foldTerm
  cases h : term.constant? with
  | none => rfl
  | some value => simp [splitVar, constant_coefficient name term h]

@[simp] theorem addTerm_coefficient [DecidableEq α] (name : α) (left right : LTerm α) :
    (splitVar name (addTerm left right)).1 =
      (splitVar name left).1 + (splitVar name right).1 := by
  simp [addTerm, splitVar]

@[simp] theorem subTerm_coefficient [DecidableEq α] (name : α) (left right : LTerm α) :
    (splitVar name (subTerm left right)).1 =
      (splitVar name left).1 - (splitVar name right).1 := by
  simp [subTerm, splitVar]

@[simp] theorem scaleTerm_coefficient [DecidableEq α] (name : α) (k : Int) (term : LTerm α) :
    (splitVar name (scaleTerm k term)).1 = k * (splitVar name term).1 := by
  by_cases h : k = 0 <;> simp [scaleTerm, h, splitVar]

@[simp] theorem remainder_coefficient [DecidableEq α] (name : α) (term : LTerm α) :
    (splitVar name (splitVar name term).2).1 = 0 := by
  induction term with
  | var other =>
      by_cases h : other = name <;> simp [splitVar, h]
  | konst value => rfl
  | add left right ihLeft ihRight => simp [splitVar, ihLeft, ihRight]
  | sub left right ihLeft ihRight => simp [splitVar, ihLeft, ihRight]
  | scale k term ih => simp [splitVar, ih]

/-- The remainder is independent of the eliminated variable, including cancelled
    occurrences. This is stronger than syntactic absence of that variable. -/
theorem remainder_bind [DecidableEq α] (name : α) (term : LTerm α)
    (values : Assignment α) (x : Int) :
    (splitVar name term).2.denote (values.bind name x) =
      (splitVar name term).2.denote values := by
  induction term with
  | var other =>
      by_cases h : other = name <;> simp [splitVar, h, LTerm.denote, Assignment.bind]
  | konst value => rfl
  | add left right ihLeft ihRight => simp [splitVar, addTerm_denote, ihLeft, ihRight]
  | sub left right ihLeft ihRight => simp [splitVar, subTerm_denote, ihLeft, ihRight]
  | scale k term ih => simp [splitVar, scaleTerm_denote, ih]

theorem term_bind [DecidableEq α] (name : α) (term : LTerm α)
    (values : Assignment α) (x : Int) :
    term.denote (values.bind name x) =
      (splitVar name term).1 * x + (splitVar name term).2.denote values := by
  rw [splitVar_denote name term (values.bind name x), bind_same, remainder_bind]

/-- Every atomic coefficient is zero or a unit, including divisibility atoms.
    This is the normal form computed by coefficient normalization. -/
@[expose]
def UnitCoefficients [DecidableEq α] (name : α) : QF α → Prop
  | .tru | .fls => True
  | .atom _ term =>
      (splitVar name term).1 = 0 ∨ (splitVar name term).1 = 1 ∨ (splitVar name term).1 = -1
  | .conj left right | .disj left right => UnitCoefficients name left ∧ UnitCoefficients name right

theorem unit_truth [DecidableEq α] (name : α) (value : Bool) :
    UnitCoefficients name (truth value : QF α) := by cases value <;> trivial

theorem unit_atom [DecidableEq α] (name : α) (relation : Relation) (term : LTerm α)
    (h : UnitCoefficients name (.atom relation term)) : UnitCoefficients name (atom relation term) := by
  unfold atom
  cases term.constant? with
  | none => exact h
  | some value => exact unit_truth name _

theorem unit_conj [DecidableEq α] (name : α) (left right : QF α)
    (hl : UnitCoefficients name left) (hr : UnitCoefficients name right) :
    UnitCoefficients name (conj left right) := by
  cases left <;> cases right <;> simp_all [conj, UnitCoefficients]

theorem unit_disj [DecidableEq α] (name : α) (left right : QF α)
    (hl : UnitCoefficients name left) (hr : UnitCoefficients name right) :
    UnitCoefficients name (disj left right) := by
  cases left <;> cases right <;> simp_all [disj, UnitCoefficients]

end Gabbro.Grammatik.Invarianten.Elim.Korrekt
