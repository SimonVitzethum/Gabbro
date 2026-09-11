/-
  GAP-15 `path` (G-NAME) -- LESESTELLE probe, p21 (odd).
  Registry: messung/SYNTAX-PARSER-ENTWURF.md, fifteenth LESESTELLE row.
  EBNF (dokumente/SYNTAX.md, Lexis): path = pathseg { "::" pathseg }.

  MAPPING RULE (tree vs token). `path` has no constructor as a term: it is the
  qualified NAME argument of declarations, calls and `fnref`. The parser
  resolves the segment list against the declared names -- a declared `Fn`, a
  declared `Tab`, or a generated table operation (`T::insert`,
  `messung/OPS-RUFFORM.md`) -- and hands the RESOLVED entity to the
  constructor (e.g. the `D.Fn` argument of `Stmt.call`). The segment spelling,
  including the `::` separators, is erased; an unresolvable path is a refusal,
  not a term.

  MINIMAL PARSE WITNESS. Surface `T::insert` resolves against the generated
  operations of table `T` to that operation -- the tree keeps the `D.Fn`,
  not the two segments. The model below is the lookup step over the declared
  qualified names.
-/
import Grammatik.Syntax

namespace P21.Gap15Path

/-- Resolution: position of the qualified name among the declared operations. -/
def lookupOp (ops : List String) (p : String) : Option Nat :=
  ops.findIdx? (· == p)

/-- Reassembly is only the surface spelling; the tree keeps the resolved entity. -/
def spellPath (segs : List String) : String := String.intercalate "::" segs

-- Surface `T::insert`: declared first among the generated operations of `T`.
example : lookupOp ["T::insert", "T::remove"] "T::insert" = some 0 := rfl
-- Surface `T::remove`: second.
example : lookupOp ["T::insert", "T::remove"] "T::remove" = some 1 := rfl
-- Surface `T::relabel`: no body, no call form (G-RELABEL) -- unresolvable here.
example : lookupOp ["T::insert", "T::remove"] "T::relabel" = none := rfl
-- The spelling the tree forgets.
example : spellPath ["T", "insert"] = "T::insert" := rfl

-- Carrier link: the resolved `D.Fn` is the call argument; segments do not occur.
open Gabbro.Grammatik in
#check @Stmt.call

end P21.Gap15Path
