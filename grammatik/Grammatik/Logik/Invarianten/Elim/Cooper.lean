module

public import Grammatik.Logik.Invarianten.Elim.Formula
public import Mathlib.Data.Int.GCD

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Elim

open Frag

/-- LCM of all nonzero coefficients of the variable being eliminated.
    Including divisibility atoms makes every dependent atom have coefficient ±1
    after the change of variable `y = multiple*x`. Zero coefficients contribute 1. -/
def coefficientLcm [DecidableEq α] (name : α) : QF α → Nat
  | .tru | .fls => 1
  | .atom _ term =>
      let coefficient := (splitVar name term).1
      if coefficient = 0 then 1 else coefficient.natAbs
  | .conj left right | .disj left right =>
      Int.lcm (coefficientLcm name left : Int) (coefficientLcm name right : Int)

/-- Multiplying `d ∣ a*x+r` by positive `f = multiple/|a|` yields
    `d*f ∣ sign(a)*y+f*r`. A negated divisibility atom uses the same scaling. -/
def normalizeAtom [DecidableEq α] (name : α) (multiple : Nat)
    (relation : Relation) (term : LTerm α) : QF α :=
  let parts := splitVar name term
  if parts.1 = 0 then atom relation parts.2
  else
    let factor := multiple / parts.1.natAbs
    let signed := scaleTerm (if parts.1 < 0 then -1 else 1) (.var name)
    let result := addTerm signed (scaleTerm (factor : Int) parts.2)
    match relation with
    | .lt => atom .lt result
    | .dvd k => atom (.dvd ((k + 1) * factor - 1)) result
    | .ndvd k => atom (.ndvd ((k + 1) * factor - 1)) result

def normalizeCoefficients [DecidableEq α] (name : α) (multiple : Nat) : QF α → QF α
  | .tru => .tru
  | .fls => .fls
  | .atom relation term => normalizeAtom name multiple relation term
  | .conj left right =>
      conj (normalizeCoefficients name multiple left) (normalizeCoefficients name multiple right)
  | .disj left right =>
      disj (normalizeCoefficients name multiple left) (normalizeCoefficients name multiple right)

/-- The extra divisibility conjunct restricts the new variable to the image of
    multiplication by the LCM. Omitting it would accept `∃ x, 2*x = 3`. -/
def normalize [DecidableEq α] (name : α) (body : QF α) : QF α :=
  let multiple := coefficientLcm name body
  conj (atom (.dvd (multiple - 1)) (.var name))
    (normalizeCoefficients name multiple body)

/-- Lower-bound thresholds: `-x+r < 0` changes from false to true at `r+1`.
    Cooper's candidates are `r+j` for `1 ≤ j ≤ period`. Both branches of every
    Boolean connective contribute; no conversion to DNF is needed. -/
def lowerBounds [DecidableEq α] (name : α) : QF α → List (LTerm α)
  | .atom .lt term =>
      let parts := splitVar name term
      if parts.1 = -1 then [parts.2] else []
  | .conj left right | .disj left right => lowerBounds name left ++ lowerBounds name right
  | _ => []

/-- Far towards negative infinity, positive-coefficient inequalities hold and
    negative-coefficient inequalities fail. Divisibility remains periodic. -/
def minusInfinity [DecidableEq α] (name : α) : QF α → QF α
  | .tru => .tru
  | .fls => .fls
  | .atom .lt term =>
      let parts := splitVar name term
      if parts.1 = 0 then atom .lt parts.2 else truth (decide (0 < parts.1))
  | .atom relation term => atom relation term
  | .conj left right => conj (minusInfinity name left) (minusInfinity name right)
  | .disj left right => disj (minusInfinity name left) (minusInfinity name right)

/-- A positive common period. Atoms independent of `name` contribute 1. -/
def period [DecidableEq α] (name : α) : QF α → Nat
  | .tru | .fls | .atom .lt _ => 1
  | .atom (.dvd k) term | .atom (.ndvd k) term =>
      if (splitVar name term).1 = 0 then 1 else k + 1
  | .conj left right | .disj left right =>
      Int.lcm (period name left : Int) (period name right : Int)

/-- Retained data for proof decomposition and later counterexample reconstruction.
    This is a computed elimination plan, with no supplied validity certificate. -/
structure CooperStep (α : Type) where
  multiple : Nat
  body : QF α
  modulus : Nat
  boundaries : List (LTerm α)
  infinity : QF α

def prepare [DecidableEq α] (name : α) (body : QF α) : CooperStep α :=
  let normalized := normalize name body
  { multiple := coefficientLcm name body
    body := normalized
    modulus := period name normalized
    boundaries := lowerBounds name normalized
    infinity := minusInfinity name normalized }

/-- Finite disjunction in Cooper's theorem. The infinity branch represents a
    residue class arbitrarily far to the left, not the concrete point `j` in the
    original formula. Boundary branches are actual witnesses in normalized units. -/
def project [DecidableEq α] (name : α) (step : CooperStep α) : QF α :=
  let residues := List.range step.modulus
  let below := anyOf (residues.map fun j => step.infinity.subst name (.konst ((j + 1 : Nat) : Int)))
  let above := anyOf (step.boundaries.map fun boundary =>
    anyOf (residues.map fun j =>
      step.body.subst name (addTerm boundary (.konst ((j + 1 : Nat) : Int)))))
  disj below above

def eliminateOne [DecidableEq α] (name : α) (body : QF α) : QF α :=
  project name (prepare name body)

end Gabbro.Grammatik.Invarianten.Elim
