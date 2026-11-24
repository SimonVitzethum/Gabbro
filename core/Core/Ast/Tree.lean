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
  /-- Integers with inclusive, architecture-independent bounds. -/
  | int (lo hi : Int) : Ty .value
  | bool : Ty .value

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

/-- The exact interval of addition and the four-corner hull of multiplication. -/
def Arith.bounds : Arith → Int → Int → Int → Int → Int × Int
  | .add, lo₁, hi₁, lo₂, hi₂ => (lo₁ + lo₂, hi₁ + hi₂)
  | .mul, lo₁, hi₁, lo₂, hi₂ =>
    (min (min (lo₁ * lo₂) (lo₁ * hi₂)) (min (hi₁ * lo₂) (hi₁ * hi₂)),
     max (max (lo₁ * lo₂) (lo₁ * hi₂)) (max (hi₁ * lo₂) (hi₁ * hi₂)))

def Arith.result (op : Arith) (lo₁ hi₁ lo₂ hi₂ : Int) : Ty .value :=
  let (lo, hi) := op.bounds lo₁ hi₁ lo₂ hi₂
  .int lo hi

inductive Expr : Scope → Ty .value → Type where
  /-- An unsigned spelling of an unsuffixed integer literal. -/
  | lit (value : Nat) : Expr scope (.int value value)
  /-- Left-associative arithmetic computes the interval of its two operands. -/
  | binary (op : Arith) (left : Expr scope (.int lo₁ hi₁))
      (right : Expr scope (.int lo₂ hi₂)) : Expr scope (op.result lo₁ hi₁ lo₂ hi₂)

abbrev TypedExpr (scope : Scope) := (type : Ty .value) × Expr scope type

def Expr.typed (tree : Expr scope type) : TypedExpr scope := ⟨type, tree⟩

inductive Stmt : Scope → Scope → Type where
  /-- `let name = value;`. The name enters scope after the initializer. -/
  | letValue (name : Identifier) (ordinary : name.val ≠ "mut".toList)
      (value : Expr scope type) : Stmt scope (⟨name, type, false⟩ :: scope)

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
