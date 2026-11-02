module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- A transition place retains its identity until capture. Relative fields
    require a checked use-site specialization; they are not guessed globals. -/
inductive UTransitionPlace where
  | slot (table field : String) (index : UIdx)
  | glob (name : String)
  | relative (field : String)
  deriving DecidableEq, Repr

/-- Source endpoint expressions, in declaration order, before capture. -/
structure UTransitionWrite where
  place : UTransitionPlace
  source : USide
  target : USide
  deriving DecidableEq, Repr

/-- One named clause. Distinct clauses are never identified by their edges.
    Effects are permissions; no effect introduces an executable action. -/
structure UTransition where
  name : String
  writes : List UTransitionWrite
  clause : UEns
  held : List String
  puts : List String
  gputs : List String
  primitive : Bool
  deriving DecidableEq, Repr

/-- A clause-bearing declaration that is exactly one finite constant edge of a table
    field: its generated function ends in the primitive shift, under a requires
    that makes the entry legal. Every other clause declaration generates stores. -/
@[expose] def uTransitionShift (tr : UTransition) : Bool :=
  !tr.primitive && match tr.writes with
    | [w] =>
      match w.place, w.source, w.target with
      | .slot .., .lit _, .lit _ => true
      | _, _, _ => false
    | _ => false

/-- State identity, first-occurrence symbolic numbering, the primitive
    constant-edge projection, and the complete named transition declarations. -/
structure UZustand where
  name : String
  stufen : List String
  paare : List (Int × Int)
  transitions : List UTransition := []
  deriving DecidableEq, Repr

end Gabbro.Grammatik.Parser.Uebersetze
