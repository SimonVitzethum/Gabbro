module

public import Core.Text.Lexeme

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

/-- A written name. Contextual keyword exclusions belong to the production that binds it. -/
def Identifier := { name : RawText // ∃ c rest, name = c :: rest ∧
  isNameStart c ∧ ∀ a ∈ rest, isNamePart a }

/-- Kinds separate value types from other type-level forms as they are introduced. -/
inductive Kind where
  | value

inductive Ty : Kind → Type where
  /-- The unbounded integer domain of unsuffixed source numerals and their arithmetic.
      Elaboration will supply the contextual machine type. -/
  | integer : Ty .value

structure Binding where
  name : Identifier
  type : Ty .value
  mutable : Bool

abbrev Scope := List Binding

/-- Newest binder first. Uses carry a typed de Bruijn index; resolution of a written
    name must select the nearest binding under the applicable scope rules. -/
inductive Local : Scope → Ty .value → Type where
  | here : Local (binding :: outer) binding.type
  | there : Local outer type → Local (binding :: outer) type

/-- Concrete binary operators sharing one surface production family. -/
inductive Arith where
  | add
  | mul
  deriving DecidableEq

inductive Expr : Scope → Ty .value → Type where
  /-- An unsigned spelling of an unsuffixed integer literal. -/
  | lit (value : Nat) : Expr scope .integer
  /-- Left-associative arithmetic. Both operands must have the operator's input type. -/
  | binary (op : Arith) (left right : Expr scope .integer) : Expr scope .integer

inductive Stmt : Scope → Scope → Type where
  /-- `let name = value;`. The name enters scope after the initializer. -/
  | letValue (name : Identifier) (ordinary : name.val ≠ "mut".toList)
      (value : Expr scope .integer) : Stmt scope (⟨name, .integer, false⟩ :: scope)

/-- Sequential scope composition. The block production decides where its locals
    leave scope. The output index is the scope at the end of the body. -/
inductive Block : Scope → Scope → Type where
  | done : Block scope scope
  | step : Stmt before middle → Block middle after → Block before after

/-- Declarations add bindings to the unit's scope. Declaration forms are admitted by M6. -/
inductive Decl : Scope → Scope → Type where

/-- A source unit is an ordered sequence of declarations, initially in the empty scope. -/
inductive UnitBody : Scope → Scope → Type where
  | done : UnitBody scope scope
  | step : Decl before middle → UnitBody middle after → UnitBody before after

abbrev Unit := (after : Scope) × UnitBody [] after

abbrev Statement (before : Scope) := (after : Scope) × Stmt before after
abbrev Statements (before : Scope) := (after : Scope) × Block before after

end Gabbro.Core.Ast
