module

public import Grammatik.Logik.Invarianten.Elim.Linear

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Elim

open Frag

/-- A divisibility constructor stores the predecessor of its positive modulus.
    Thus zero divisors cannot enter Cooper's period calculation. Source `0 ∣ t`
    is represented as `t = 0`, and negative divisors use their absolute value. -/
inductive Relation where
  | lt
  | dvd (modulusPred : Nat)
  | ndvd (modulusPred : Nat)
  deriving DecidableEq, Repr

def Relation.denote (value : Int) : Relation → Prop
  | .lt => value < 0
  | .dvd k => ((k + 1 : Nat) : Int) ∣ value
  | .ndvd k => ¬ ((k + 1 : Nat) : Int) ∣ value

def Relation.eval (value : Int) : Relation → Bool
  | .lt => decide (value < 0)
  | .dvd k => decide (value % ((k + 1 : Nat) : Int) = 0)
  | .ndvd k => !decide (value % ((k + 1 : Nat) : Int) = 0)

/-- Negation normal form. All inequalities are strict comparisons with zero;
    all moduli are positive. No quantified or implicational case remains here. -/
inductive QF (α : Type) where
  | tru
  | fls
  | atom (relation : Relation) (term : LTerm α)
  | conj (left right : QF α)
  | disj (left right : QF α)
  deriving DecidableEq, Repr

def QF.denote (values : Assignment α) : QF α → Prop
  | .tru => True
  | .fls => False
  | .atom relation term => relation.denote (term.denote values)
  | .conj left right => left.denote values ∧ right.denote values
  | .disj left right => left.denote values ∨ right.denote values

def QF.eval (values : Assignment α) : QF α → Bool
  | .tru => true
  | .fls => false
  | .atom relation term => relation.eval (term.denote values)
  | .conj left right => left.eval values && right.eval values
  | .disj left right => left.eval values || right.eval values

def truth (value : Bool) : QF α := if value then .tru else .fls

def atom (relation : Relation) (term : LTerm α) : QF α :=
  match term.constant? with
  | some value => truth (relation.eval value)
  | none => .atom relation term

def conj : QF α → QF α → QF α
  | .fls, _ | _, .fls => .fls
  | .tru, right => right
  | left, .tru => left
  | left, right => .conj left right

def disj : QF α → QF α → QF α
  | .tru, _ | _, .tru => .tru
  | .fls, right => right
  | left, .fls => left
  | left, right => .disj left right

/-- `¬(t < 0)` is `-t-1 < 0` over integers. -/
def QF.neg : QF α → QF α
  | .tru => .fls
  | .fls => .tru
  | .atom .lt term => atom .lt (subTerm (scaleTerm (-1) term) (.konst 1))
  | .atom (.dvd k) term => atom (.ndvd k) term
  | .atom (.ndvd k) term => atom (.dvd k) term
  | .conj left right => disj left.neg right.neg
  | .disj left right => conj left.neg right.neg

def equalZero (term : LTerm α) : QF α :=
  conj (atom .lt (subTerm term (.konst 1)))
    (atom .lt (subTerm (scaleTerm (-1) term) (.konst 1)))

def divides (divisor : Int) (term : LTerm α) : QF α :=
  match divisor.natAbs with
  | 0 => equalZero term
  | n + 1 => atom (.dvd n) term

def QF.subst [DecidableEq α] (name : α) (replacement : LTerm α) : QF α → QF α
  | .tru => .tru
  | .fls => .fls
  | .atom relation term => atom relation (substTerm name replacement term)
  | .conj left right => conj (left.subst name replacement) (right.subst name replacement)
  | .disj left right => disj (left.subst name replacement) (right.subst name replacement)

def QF.size : QF α → Nat
  | .tru | .fls => 1
  | .atom _ term => termSize term + 1
  | .conj left right | .disj left right => left.size + right.size + 1

/-- Folding keeps constant projections small; the list order is deterministic. -/
def anyOf (formulas : List (QF α)) : QF α := formulas.foldr disj .fls

end Gabbro.Grammatik.Invarianten.Elim
