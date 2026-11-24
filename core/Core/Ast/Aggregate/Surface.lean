module

public import Core.Ast.ProgramSurface

@[expose] public section

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text

structure ArrayValueArgs (scope : Scope) where
  types : List (Ty .value)
  element : Ty .value
  items : ExprItems scope types
  principal : arrayElement types = some element
  fits : ∀ i : Fin types.length, Fits (types.get i) element

def ArrayValueArgs.expression (args : ArrayValueArgs scope) :
    Expr scope (.array args.element args.types.length) :=
  .arrayValue args.items args.principal args.fits

/-- SYNTAX §1, a bracketed literal in source evaluation order. -/
def arrayValue (scope : Scope) : Rule (.expression scope) (ArrayValueArgs scope) where
  tree := fun a => a.expression.typed
  production := fun args tokens =>
    ∃ input, tokens = openBracket :: input ∧ ItemsRead scope closeBracket input args.items []

structure ArrayIndexArgs (scope : Scope) where
  element : Ty .value
  count : Nat
  lo : Int
  hi : Int
  base : Expr scope (.array element count)
  offset : Expr scope (.int lo hi)
  lower : 0 ≤ lo
  upper : hi < (count : Int)

def ArrayIndexArgs.expression (args : ArrayIndexArgs scope) : Expr scope args.element :=
  .arrayIndex args.base args.offset args.lower args.upper

/-- A complete postfix spelling may be written directly or grouped for printing. -/
def postfixProduction (body : List Token → List Token → Prop) (tokens : List Token) : Prop :=
  body tokens [] ∨ ∃ inside, tokens = openParen :: inside ∧ body inside [closeParen]

/-- SYNTAX §4, the expression in brackets selects one array element. -/
def arrayIndex (scope : Scope) : Rule (.expression scope) (ArrayIndexArgs scope) where
  tree := fun a => a.expression.typed
  production := fun args => postfixProduction fun input rest =>
    ∃ indexInput, ExprReads scope 8 input args.base (openBracket :: indexInput) ∧
      ExprReads scope 0 indexInput args.offset (closeBracket :: rest)

structure TupleValueArgs (scope : Scope) where
  firstType : Ty .value
  secondType : Ty .value
  tailTypes : List (Ty .value)
  first : Expr scope firstType
  second : Expr scope secondType
  tail : ExprItems scope tailTypes

def TupleValueArgs.types (args : TupleValueArgs scope) : List (Ty .value) :=
  args.firstType :: args.secondType :: args.tailTypes

def TupleValueArgs.expression (args : TupleValueArgs scope) : Expr scope (tupleType args.types) :=
  .tupleValue args.first args.second args.tail

/-- SYNTAX §4, comma distinguishes a positional product from grouping. -/
def tupleValue (scope : Scope) : Rule (.expression scope) (TupleValueArgs scope) where
  tree := fun a => a.expression.typed
  production := fun args tokens =>
    ∃ input secondInput more, tokens = openParen :: input ∧
      ExprReads scope 0 input args.first (comma :: secondInput) ∧
      ExprReads scope 0 secondInput args.second more ∧ ItemsTail scope closeParen more args.tail []

structure TupleFieldArgs (scope : Scope) where
  first : Ty .value
  second : Ty .value
  tail : List (Ty .value)
  base : Expr scope (tupleType (first :: second :: tail))
  index : Fin (first :: second :: tail).length

def TupleFieldArgs.types (args : TupleFieldArgs scope) : List (Ty .value) :=
  args.first :: args.second :: args.tail

def TupleFieldArgs.expression (args : TupleFieldArgs scope) : Expr scope (args.types.get args.index) :=
  .tupleField args.base args.index

/-- SYNTAX §4, the numeral after a dot is a zero-based position. -/
def tupleField (scope : Scope) : Rule (.expression scope) (TupleFieldArgs scope) where
  tree := fun a => a.expression.typed
  production := fun args => postfixProduction fun input rest =>
    ExprReads scope 8 input args.base (dot :: .natural args.index.val :: rest)

end Gabbro.Core.Ast.Surface
