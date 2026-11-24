module

public import Core.Ast.ProgramHeader

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def discardName : Identifier :=
  ⟨['_'], '_', [], rfl, Or.inr rfl, fun _ member => (List.not_mem_nil member).elim⟩

def patternNamePieces (name : Option Identifier) : List PrintedToken :=
  [(name.getD discardName).print]

def TuplePattern.printPieces (pattern : TuplePattern) : List PrintedToken :=
  printOpen :: commaSeparated (pattern.names.map patternNamePieces) ++ [printClose]

def tupleAnnotationPieces : Option WrittenType → List PrintedToken
  | none => []
  | some annotation => printColon :: annotation.printPieces

inductive PatternNameReads : List Token → Option Identifier → List Token → Prop where
  | discard : PatternNameReads (.word ['_'] :: rest) none rest
  | name (name : Identifier) (use : name.val ≠ ['_']) :
      PatternNameReads (.word name.val :: rest) (some name) rest

inductive PatternTailReads : List Token → List (Option Identifier) → List Token → Prop where
  | close : PatternTailReads (closeParen :: rest) [] rest
  | next : PatternNameReads input name more → PatternTailReads more names rest →
      PatternTailReads (comma :: input) (name :: names) rest

inductive TuplePatternReads : List Token → TuplePattern → List Token → Prop where
  | tuple : PatternNameReads input first (comma :: next) →
      PatternNameReads next second more → PatternTailReads more tail rest →
      TuplePatternReads (openParen :: input) ⟨first, second, tail⟩ rest

/-- This relation consumes the assignment token, so absence and presence cannot overlap. -/
inductive TupleAnnotationReads (scope : Scope) : List Token → Option WrittenType → List Token → Prop where
  | absent : TupleAnnotationReads scope (assignment :: rest) none rest
  | written : TypeReads scope input type (assignment :: rest) →
      TupleAnnotationReads scope (colon :: input) (some type) rest

end Gabbro.Core.Ast
