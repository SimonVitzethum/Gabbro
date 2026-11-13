module

public import Grammatik.Logik.Invarianten.Elim.Cooper

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Elim

open Frag

inductive Refusal where
  | budgetExceeded (spent requested limit : Nat)
  | freeVariables
  deriving DecidableEq, Repr

def Refusal.message : Refusal → String
  | .budgetExceeded spent requested limit =>
      "invariant elimination exceeds budget " ++ toString limit ++
        " (used " ++ toString spent ++ ", next charge " ++ toString requested ++ ")"
  | .freeVariables => "invariant decision needs a closed formula; quantify its state variables"

/-- Engineering work units, not a wall-clock promise. Integer arithmetic is exact.
    A finite allowance is checked before normalization, negation, or expansion.
    `none` is used only for the total unbounded procedure and the exact bound. -/
structure Meter where
  limit : Option Nat
  spent : Nat := 0

abbrev Work (α : Type) := StateT Meter (Except Refusal) α

def charge (amount : Nat) : Work Unit := StateT.mk fun meter =>
  let next := meter.spent + amount
  match meter.limit with
  | some limit =>
      if next ≤ limit then .ok ((), { meter with spent := next })
      else .error (.budgetExceeded meter.spent amount limit)
  | none => .ok ((), { meter with spent := next })

/-- Charge visits before traversing either the old or the generated term trees.
    This overestimates node work; arbitrary-precision integer bit costs are not
    counted. The period multiplication itself does not allocate the residue list. -/
def eliminateMetered [DecidableEq α] (name : α) (body : QF α) : Work (QF α) := do
  charge (8 * (body.size + 1) ^ 2)
  let step := prepare name body
  let boundarySize := step.boundaries.foldr (fun term rest => termSize term + rest) 0
  charge ((step.modulus + 1) * (step.body.size + step.infinity.size + 1) *
    (boundarySize + step.boundaries.length + 1))
  return project name step

def negateMetered (body : QF α) : Work (QF α) := do
  charge (4 * body.size + 1)
  return body.neg

/-- Structural recursion on SOURCE syntax proves logical termination, independently
    of the allowance. Inner quantifiers disappear before their enclosing binder;
    this also handles alternating prefixes and repeated shadowing names. -/
def compile [DecidableEq α] : LProp α → Work (QF α)
  | .tru => do
      charge 1
      return .tru
  | .fls => do
      charge 1
      return .fls
  | .le left right => do
      charge (termSize left + termSize right + 2)
      return atom .lt (subTerm (subTerm left right) (.konst 1))
  | .lt left right => do
      charge (termSize left + termSize right + 1)
      return atom .lt (subTerm left right)
  | .eq left right => do
      charge (2 * (termSize left + termSize right + 2))
      return equalZero (subTerm left right)
  | .dvd divisor term => do
      charge (2 * termSize term + 2)
      return divides divisor term
  | .not body => do
      let result ← compile body
      negateMetered result
  | .and left right => do
      charge 1
      let a ← compile left
      let b ← compile right
      return conj a b
  | .or left right => do
      charge 1
      let a ← compile left
      let b ← compile right
      return disj a b
  | .imp left right => do
      charge 1
      let a ← compile left
      let b ← compile right
      let negative ← negateMetered a
      return disj negative b
  | .ex name body => do
      let result ← compile body
      eliminateMetered name result
  | .all name body => do
      let result ← compile body
      let negative ← negateMetered result
      let eliminated ← eliminateMetered name negative
      negateMetered eliminated

/-- Unbounded Cooper elimination and the charges of that very execution. The
    error branch is unreachable with `limit = none`; no logical fuel is used. -/
def elimination [DecidableEq α] (formula : LProp α) : QF α × Nat :=
  match (compile formula).run { limit := none } with
  | .ok (result, meter) => (result, meter.spent)
  | .error _ => (.fls, 0)

/-- Exact engineering allowance of the unbounded run, rather than a search bound
    on integer values. Computing this bound performs elimination; production
    callers should supply their own finite allowance to `decideWithBudget`. -/
def Budget [DecidableEq α] (formula : LProp α) : Nat := (elimination formula).2

/-- The total Boolean decision on CLOSED formulas. For open syntax, this only
    evaluates the remaining free variables at zero; use the refusing entry point
    below whenever closedness is not already guaranteed by construction.
    `Korrekt.Decision` proves both answers correct under syntactic closedness. -/
def decideB [DecidableEq α] (formula : LProp α) : Bool :=
  (elimination formula).1.eval (fun _ => 0)

/-- Declaration-time resource and closedness refusals are distinct from a false
    logical answer. In particular, an exhausted allowance never yields `.ok false`.
    The later P17 layer reconstructs concrete states from false closed VCs. -/
def decideWithBudget [DecidableEq α] (formula : LProp α) (fuel : Nat) : Except Refusal Bool :=
  if closedUnderB [] formula then do
    let (result, _) ← (compile formula).run { limit := some fuel }
    return result.eval (fun _ => 0)
  else .error .freeVariables

end Gabbro.Grammatik.Invarianten.Elim
