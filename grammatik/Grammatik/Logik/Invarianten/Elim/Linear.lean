module

public import Grammatik.Logik.Invarianten.Frag.Syntax

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Elim

open Frag

/-- Constant folding only; no arithmetic identity is assumed by the algorithm. -/
def foldTerm (term : LTerm α) : LTerm α :=
  match term.constant? with
  | some value => .konst value
  | none => term

def addTerm (left right : LTerm α) : LTerm α := foldTerm (.add left right)

def subTerm (left right : LTerm α) : LTerm α := foldTerm (.sub left right)

def scaleTerm (coefficient : Int) (term : LTerm α) : LTerm α :=
  if coefficient = 0 then .konst 0 else foldTerm (.scale coefficient term)

/-- `splitVar x t = (a,r)` represents `t = a*x+r`; `r` contains no `x`.
    Cancellation is handled by integer addition of coefficients, not by searching
    the surface tree for a first occurrence. -/
def splitVar [DecidableEq α] (name : α) : LTerm α → Int × LTerm α
  | .var other => if other = name then (1, .konst 0) else (0, .var other)
  | .konst value => (0, .konst value)
  | .add left right =>
      let a := splitVar name left
      let b := splitVar name right
      (a.1 + b.1, addTerm a.2 b.2)
  | .sub left right =>
      let a := splitVar name left
      let b := splitVar name right
      (a.1 - b.1, subTerm a.2 b.2)
  | .scale coefficient term =>
      let a := splitVar name term
      (coefficient * a.1, scaleTerm coefficient a.2)

/-- Quantifier-free substitution; binders are eliminated before this is called. -/
def substTerm [DecidableEq α] (name : α) (replacement : LTerm α) : LTerm α → LTerm α
  | .var other => if other = name then replacement else .var other
  | .konst value => .konst value
  | .add left right => addTerm (substTerm name replacement left) (substTerm name replacement right)
  | .sub left right => subTerm (substTerm name replacement left) (substTerm name replacement right)
  | .scale coefficient term => scaleTerm coefficient (substTerm name replacement term)

def termSize : LTerm α → Nat
  | .var _ | .konst _ => 1
  | .add left right | .sub left right => termSize left + termSize right + 1
  | .scale _ term => termSize term + 1

def termClosedB [DecidableEq α] (bound : List α) : LTerm α → Bool
  | .var name => decide (name ∈ bound)
  | .konst _ => true
  | .add left right | .sub left right => termClosedB bound left && termClosedB bound right
  | .scale _ term => termClosedB bound term

/-- Syntactic closedness respects named shadowing; no finite enumeration of `α`
    is needed. Open VCs must be explicitly universally closed by their caller. -/
def closedUnderB [DecidableEq α] (bound : List α) : LProp α → Bool
  | .tru | .fls => true
  | .le left right | .lt left right | .eq left right =>
      termClosedB bound left && termClosedB bound right
  | .dvd _ term => termClosedB bound term
  | .not body => closedUnderB bound body
  | .and left right | .or left right | .imp left right =>
      closedUnderB bound left && closedUnderB bound right
  | .ex name body | .all name body => closedUnderB (name :: bound) body

end Gabbro.Grammatik.Invarianten.Elim
