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

def Local.binding : Local scope type → Binding
  | @here binding _ => binding
  | .there ref => ref.binding

def Local.index : Local scope type → Nat
  | .here => 0
  | .there ref => ref.index + 1

/-- A written occurrence may only refer to the nearest binding with that spelling. -/
def Local.visible : Local scope type → Prop
  | .here => True
  | @there _ _ binding ref => binding.name.val ≠ ref.binding.name.val ∧ ref.visible

/-- Concrete binary operators sharing one surface production family. -/
inductive Arith where
  | add
  | mul
  | sub
  deriving DecidableEq

/-- The exact interval of addition and the four-corner hull of multiplication. -/
def Arith.bounds : Arith → Int → Int → Int → Int → Int × Int
  | .add, lo₁, hi₁, lo₂, hi₂ => (lo₁ + lo₂, hi₁ + hi₂)
  | .mul, lo₁, hi₁, lo₂, hi₂ =>
    (min (min (lo₁ * lo₂) (lo₁ * hi₂)) (min (hi₁ * lo₂) (hi₁ * hi₂)),
     max (max (lo₁ * lo₂) (lo₁ * hi₂)) (max (hi₁ * lo₂) (hi₁ * hi₂)))
  | .sub, lo₁, hi₁, lo₂, hi₂ => (lo₁ - hi₂, hi₁ - lo₂)

def Arith.result (op : Arith) (lo₁ hi₁ lo₂ hi₂ : Int) : Ty .value :=
  let (lo, hi) := op.bounds lo₁ hi₁ lo₂ hi₂
  .int lo hi

inductive Compare where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq

inductive Logic where
  | and | or
  deriving DecidableEq

def Divisor (lo hi : Int) : Prop := 1 ≤ lo ∨ hi ≤ -1

def quotientBounds (lo hi divisorLo : Int) : Int × Int :=
  if 0 ≤ lo ∧ 1 ≤ divisorLo then (0, hi)
  else
    let magnitude : Int := max lo.natAbs hi.natAbs
    (-magnitude, magnitude)

def quotientType (lo hi divisorLo : Int) : Ty .value :=
  .int (quotientBounds lo hi divisorLo).1 (quotientBounds lo hi divisorLo).2

def ordinaryLocal (name : Identifier) : Prop :=
  name.val ≠ "true".toList ∧ name.val ≠ "false".toList

/-- The implicit widening at a typed destination is inclusion of the source interval. -/
def Fits : Ty .value → Ty .value → Prop
  | .int lo hi, .int lower upper => lower ≤ lo ∧ hi ≤ upper
  | .bool, .bool => True
  | _, _ => False

inductive Expr : Scope → Ty .value → Type where
  /-- An unsigned spelling of an unsuffixed integer literal. -/
  | lit (value : Nat) : Expr scope (.int value value)
  /-- Left-associative arithmetic computes the interval of its two operands. -/
  | binary (op : Arith) (left : Expr scope (.int lo₁ hi₁))
      (right : Expr scope (.int lo₂ hi₂)) : Expr scope (op.result lo₁ hi₁ lo₂ hi₂)
  /-- Inventory key `surface.SExpr.tru`. -/
  | trueLit : Expr scope .bool
  /-- Inventory key `surface.SExpr.fls`. -/
  | falseLit : Expr scope .bool
  /-- Inventory key `surface.SExpr.variable`, resolved as a plain local. -/
  | variable (ref : Local scope type) (visible : ref.visible)
      (ordinary : ordinaryLocal ref.binding.name) : Expr scope type
  /-- A minus directly before a numeral is a negative literal. -/
  | negativeLit (magnitude : Nat) : Expr scope (.int (-(magnitude : Int)) (-(magnitude : Int)))
  /-- Inventory key `surface.SExpr.un`, signed interval negation. -/
  | neg (operand : Expr scope (.int lo hi)) : Expr scope (.int (-hi) (-lo))
  /-- Inventory key `surface.SExpr.un`, Boolean negation. -/
  | not (operand : Expr scope .bool) : Expr scope .bool
  /-- Inventory key `surface.SExpr.bin`, truncating integer division. -/
  | div (left : Expr scope (.int lo₁ hi₁)) (right : Expr scope (.int lo₂ hi₂))
      (nonzero : Divisor lo₂ hi₂) : Expr scope (quotientType lo₁ hi₁ lo₂)
  /-- Inventory key `surface.SExpr.bin`, integer comparison. -/
  | compare (op : Compare) (left : Expr scope (.int lo₁ hi₁))
      (right : Expr scope (.int lo₂ hi₂)) : Expr scope .bool
  /-- Inventory key `surface.SExpr.bin`, left-associative Boolean operators. -/
  | logic (op : Logic) (left right : Expr scope .bool) : Expr scope .bool

abbrev TypedExpr (scope : Scope) := (type : Ty .value) × Expr scope type

def Expr.typed (tree : Expr scope type) : TypedExpr scope := ⟨type, tree⟩

mutual

/-- The enclosing function's result is available in each statement and branch. -/
inductive Stmt (result : Option (Ty .value)) : Scope → Scope → Type where
  /-- `let name = value;`. The name enters scope after the initializer. -/
  | letValue (name : Identifier) (ordinary : name.val ≠ "mut".toList)
      (value : Expr scope type) : Stmt result scope (⟨name, type, false⟩ :: scope)
  /-- Assignment to a mutable range local, with SG-1 interval containment. -/
  | assignVar (ref : Local scope (.int lo hi)) (visible : ref.visible)
      (writable : ref.binding.mutable = true) (value : Expr scope (.int valueLo valueHi))
      (fits : Fits (.int valueLo valueHi) (.int lo hi)) : Stmt result scope scope
  /-- The returned expression fits the declared result type of this function. -/
  | ret (declared : result = some expected) (value : Expr scope type)
      (fits : Fits type expected) : Stmt result scope scope
  /-- Only the selected branch runs. Its new bindings are scoped to that branch. -/
  | ite (condition : Expr scope .bool) (yes no : BracedBlock result scope) : Stmt result scope scope

/-- Sequential scope composition inside a pair of braces. -/
inductive Block (result : Option (Ty .value)) : Scope → Scope → Type where
  | done : Block result scope scope
  | step : Stmt result before middle → Block result middle after → Block result before after

/-- Written braces delimit the lifetime and visibility of the body's new locals. -/
inductive BracedBlock (result : Option (Ty .value)) : Scope → Type where
  | braces (body : Block result before after) : BracedBlock result before

end

/-- Declarations add bindings to the unit's scope. Declaration forms are admitted by M6. -/
inductive Decl : Scope → Scope → Type where

/-- A source unit is an ordered sequence of declarations, initially in the empty scope. -/
inductive UnitBody : Scope → Scope → Type where
  | done : UnitBody scope scope
  | step : Decl before middle → UnitBody middle after → UnitBody before after

abbrev Unit := (after : Scope) × UnitBody [] after

abbrev Statement (result : Option (Ty .value)) (before : Scope) :=
  (after : Scope) × Stmt result before after

abbrev Statements (result : Option (Ty .value)) (before : Scope) :=
  (after : Scope) × Block result before after

end Gabbro.Core.Ast
