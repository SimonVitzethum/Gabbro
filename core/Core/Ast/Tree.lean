module

public import Core.Ast.Aggregate.ModelTypes
public import Core.Katalog.FirmwareNamen

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

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
  | .array _ 0, .array _ 0 => True
  | a, b => a = b

mutual

inductive Expr (scope : Scope) : Ty .value → Type where
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
  /-- The bracketed literal has one element type and its exact number of elements. -/
  | arrayValue (items : ExprItems scope types) (principal : arrayElement types = some element)
      (fits : ∀ i : Fin types.length, Fits (types.get i) element) :
      Expr scope (.array element types.length)
  /-- The endpoints of the inferred index interval imply the pinned index guard. -/
  | arrayIndex (base : Expr scope (.array element count)) (index : Expr scope (.int lo hi))
      (lower : 0 ≤ lo) (upper : hi < count) : Expr scope element
  /-- Two or more positional elements elaborate to a generated product. -/
  | tupleValue (first : Expr scope firstType) (second : Expr scope secondType)
      (rest : ExprItems scope types) : Expr scope (tupleType (firstType :: secondType :: types))
  /-- A written numeric projection selects a field of the positional product. -/
  | tupleField (base : Expr scope (tupleType (first :: second :: types)))
      (index : Fin (first :: second :: types).length) : Expr scope ((first :: second :: types).get index)
  /-- Labelled construction retains the declaration identity and evaluates actuals in source order. -/
  | recordValue (ref : RecordRef scope labels types) (args : LabeledItems scope actualLabels actualTypes)
      (fields : RecordArguments labels types actualLabels actualTypes)
      (fits : ∀ i, Fits (actualTypes.get (fields.slot i)) (types.get i)) :
      Expr scope (recordValueType ref.name.val labels types)
  /-- A field is selected by a checked offset in the ordered nominal schema. -/
  | recordField (base : Expr scope (recordValueType name labels types))
      (field : Identifier) (index : Fin types.length) (written : RecordFieldAt labels field index.val) :
      Expr scope (types.get index)
  /-- The selected tag determines whether its one payload expression is required. -/
  | variantValue (ref : VariantRef scope labels payloads) (label : Identifier)
      (index : Fin payloads.length) (written : labels[index.val]? = some label)
      (ordinary : ordinaryLocal label) (available : availableCase scope label)
      (payload : CasePayload scope (payloads.get index)) :
      Expr scope (variantValueType ref.name.val labels payloads)

/-- A sequence of expressions with the exact sequence of inferred operand types. -/
inductive ExprItems (scope : Scope) : List (Ty .value) → Type where
  | empty : ExprItems scope []
  | next : Expr scope type → ExprItems scope types → ExprItems scope (type :: types)

inductive LabeledItems (scope : Scope) : List Identifier → List (Ty .value) → Type where
  | empty : LabeledItems scope [] []
  | next (label : Identifier) : Expr scope type → LabeledItems scope labels types →
      LabeledItems scope (label :: labels) (type :: types)

inductive CasePayload (scope : Scope) : Option (Ty .value) → Type where
  | nullary (parenthesized : Bool) : CasePayload scope none
  | value (expression : Expr scope type) : CasePayload scope (some type)

end

abbrev TypedExpr (scope : Scope) := (type : Ty .value) × Expr scope type

def Expr.typed (tree : Expr scope type) : TypedExpr scope := ⟨type, tree⟩

mutual

/-- Static evaluation may read only bindings introduced by const declarations. -/
def Expr.static : Expr scope type → Prop
  | .variable ref _ _ => ref.binding.constant = true
  | .binary _ a b | .div a b _ | .compare _ a b => a.static ∧ b.static
  | .logic _ a b => a.static ∧ b.static
  | .neg a | .not a => a.static
  | .arrayValue items _ _ => items.static
  | .arrayIndex base index _ _ => base.static ∧ index.static
  | .tupleValue first second tail => first.static ∧ second.static ∧ tail.static
  | .tupleField base _ => base.static
  | .recordValue _ items _ _ => items.static
  | .recordField base _ _ _ => base.static
  | .variantValue _ _ _ _ _ _ payload => payload.static
  | _ => True

def ExprItems.static : ExprItems scope types → Prop
  | .empty => True
  | .next head tail => head.static ∧ tail.static

def LabeledItems.static : LabeledItems scope labels types → Prop
  | .empty => True
  | .next _ head tail => head.static ∧ tail.static

def CasePayload.static : CasePayload scope type → Prop
  | .nullary _ => True
  | .value expression => expression.static

end

mutual

/-- The scalar type spelling retains the signedness and width selected in the source.
    A missing explicit interval denotes the complete range of that width. -/
inductive WrittenType where
  | bool
  | integer (signed : Bool) (width : Nat) (interval : Option (Int × Int))
  | array (element : WrittenType) (count : Nat)
  | tuple (first second : WrittenType) (rest : WrittenTypes)
  | address (space : LowLevel.AddressSpace)
  | ownedRegion

inductive WrittenTypes where
  | empty
  | next (head : WrittenType) (tail : WrittenTypes)

end

def WrittenType.storage (signed : Bool) (width : Nat) : Int × Int :=
  if signed then (-(2 ^ (width - 1) : Int), 2 ^ (width - 1) - 1)
  else (0, 2 ^ width - 1)

mutual

def WrittenType.type : WrittenType → Ty .value
  | .bool => .bool
  | .integer signed width range =>
    let (lo, hi) := range.getD (WrittenType.storage signed width)
    .int lo hi
  | .array element count => .array element.type count
  | .tuple first second rest => tupleType (first.type :: second.type :: rest.types)
  | .address space => .address space
  | .ownedRegion => .ownedRegion

def WrittenTypes.types : WrittenTypes → List (Ty .value)
  | .empty => []
  | .next head tail => head.type :: tail.types

end

mutual

def WrittenType.valid : WrittenType → Prop
  | .bool => True
  | .integer signed width range =>
    let (minimum, maximum) := WrittenType.storage signed width
    let (lo, hi) := range.getD (minimum, maximum)
    1 ≤ width ∧ width ≤ 64 ∧ minimum ≤ lo ∧ lo ≤ hi ∧ hi ≤ maximum
  | .array element _ => element.valid
  | .tuple first second rest => first.valid ∧ second.valid ∧ rest.valid
  | .address _ | .ownedRegion => True

def WrittenTypes.valid : WrittenTypes → Prop
  | .empty => True
  | .next head tail => head.valid ∧ tail.valid

end

/-- Region work occurs at the binding instruction. The ordinary expression
    grammar cannot duplicate an owned region or a typed view. -/
inductive RegionInitializer where
  | address
  | view (written : WrittenType) (valid : written.valid)

def RegionInitializer.type : RegionInitializer → Ty .value
  | .address => .address .physical
  | .view written _ => .regionView written.type

structure Parameter where

  name : Identifier
  written : WrittenType
  valid : written.valid
  ordinary : ordinaryLocal name

def Parameter.binding (p : Parameter) : Binding := ⟨p.name, p.written.type, false, false⟩

def functionScope (outer : Scope) (parameters : List Parameter) : Scope :=
  (parameters.map Parameter.binding).reverse ++ outer

def directName (name : Identifier) : Prop :=
  ordinaryLocal name ∧ name.val ∉
    ["let", "if", "return", "while", "for", "leave", "next", "match"].map String.toList

structure DirectCall (scope : Scope) where
  name : Identifier
  ordinary : directName name
  args : List (TypedExpr scope)

/-- A finite recursion measure evaluated at function entry in the parameter scope. -/
structure Measure (scope : Scope) where
  lo : Int
  hi : Int
  expression : Expr scope (.int lo hi)
  lower : 0 ≤ lo

def rangeType (lo hi : Int) : Ty .value := .int (min lo hi) (max lo hi)

def rangeBinding (name : Identifier) (lo hi : Int) : Binding :=
  ⟨name, rangeType lo hi, true, false⟩

/-- The written pattern has at least two positions. A blank position introduces no local. -/
structure TuplePattern where
  first : Option Identifier
  second : Option Identifier
  rest : List (Option Identifier)

def TuplePattern.names (pattern : TuplePattern) : List (Option Identifier) :=
  pattern.first :: pattern.second :: pattern.rest

def TuplePattern.bindings (pattern : TuplePattern) (types : List (Ty .value)) : Scope :=
  ((pattern.names.zip types).filterMap fun (name, type) =>
    name.map fun id => ⟨id, type, false, false⟩).reverse

def TuplePattern.valid (pattern : TuplePattern) (annotation : Option WrittenType)
    (types : List (Ty .value)) : Prop :=
  pattern.names.length = types.length ∧
    ((pattern.names.filterMap id).map Subtype.val).Nodup ∧
    (∀ name ∈ pattern.names.filterMap id, name.val ≠ ['_'] ∧ ordinaryLocal name) ∧
    ∀ written ∈ annotation.toList, written.valid ∧ written.type = tupleType types

def payloadBinding (name : Identifier) (type : Ty .value) : Binding :=
  ⟨name, type, false, false⟩

mutual

/-- The enclosing function's result is available in each statement and branch. -/
inductive Stmt (result : Option (Ty .value)) : Scope → Scope → Type where
  /-- `let name = value;`. The name enters scope after the initializer. -/
  | letValue (name : Identifier) (ordinary : name.val ≠ "mut".toList)
      (value : Expr scope type) : Stmt result scope (⟨name, type, false, false⟩ :: scope)
  /-- Assignment to a mutable range local, with SG-1 interval containment. -/
  | assignVar (ref : Local scope (.int lo hi)) (visible : ref.visible)
      (writable : ref.binding.mutable = true) (value : Expr scope (.int valueLo valueHi))
      (fits : Fits (.int valueLo valueHi) (.int lo hi)) : Stmt result scope scope
  /-- The returned expression fits the declared result type of this function. -/
  | ret (declared : result = some expected) (value : Expr scope type)
      (fits : Fits type expected) : Stmt result scope scope
  /-- Only the selected branch runs. Its new bindings are scoped to that branch. -/
  | ite (condition : Expr scope .bool) (yes no : BracedBlock result scope) : Stmt result scope scope
  /-- SYNTAX §6, fallthrough and the explicit void return. -/
  | retVoid (declared : result = none) : Stmt result scope scope
  /-- SYNTAX §7, a scalar mutable local with a written type. -/
  | letMutable (name : Identifier) (ordinary : ordinaryLocal name)
      (written : WrittenType) (valid : written.valid) (value : Expr scope type)
      (fits : Fits type written.type) : Stmt result scope (⟨name, written.type, true, false⟩ :: scope)
  /-- SYNTAX §6, direct call whose ordinary result is discarded. -/
  | directCall (call : DirectCall scope) : Stmt result scope scope
  /-- SYNTAX §7, direct call with a written result-binding type. -/
  | bindDirect (name : Identifier) (ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name)
      (written : WrittenType) (valid : written.valid) (call : DirectCall scope) :
      Stmt result scope (⟨name, written.type, false, false⟩ :: scope)
  /-- SYNTAX §8, O18. The operation spelling bounds passes and the condition is retested. -/
  | whileBounded (condition : Expr scope .bool)
      (bound : Expr scope (.int lo hi)) (staticBound : bound.static) (nonnegative : 0 ≤ lo)
      (overflow : Identifier) (body : BracedBlock result scope) : Stmt result scope scope
  /-- SYNTAX §8, O18. Static endpoints and a body-local mutable index. -/
  | forRange (name : Identifier) (ordinary : ordinaryLocal name)
      (lo : Expr scope (.int low lowHi)) (hi : Expr scope (.int highLo high))
      (staticBounds : lo.static ∧ hi.static)
      (overflow : Option Identifier)
      (body : BracedBlock result (rangeBinding name low high :: scope)) : Stmt result scope scope
  /-- SYNTAX §7, bind a positional product once, in left-to-right pattern order. -/
  | tupleBind (pattern : TuplePattern) (annotation : Option WrittenType)
      (checked : pattern.valid annotation (first :: second :: types))
      (value : Expr scope (tupleType (first :: second :: types))) :
      Stmt result scope (pattern.bindings (first :: second :: types) ++ scope)
  /-- Field assignment updates exactly one position of a writable record local. -/
  | assignField (ref : Local scope (recordValueType name labels types)) (visible : ref.visible)
      (writable : ref.binding.mutable = true) (field : Identifier) (index : Fin types.length)
      (written : RecordFieldAt labels field index.val) (value : Expr scope source)
      (fits : Fits source (types.get index)) : Stmt result scope scope
  /-- The inferred mutable binding uses the initializer's exact type. -/
  | letMutableValue (name : Identifier) (ordinary : ordinaryLocal name)
      (value : Expr scope type) : Stmt result scope (⟨name, type, true, false⟩ :: scope)
  /-- Each arm consumes exactly the next declared tag and payload shape. -/
  | variantMatch (value : Expr scope (variantValueType name labels payloads))
      (arms : VariantArms result scope false labels payloads) : Stmt result scope scope

  /-- Bind an inert address or a typed, non-copyable view. -/
  | letRegion (name : Identifier) (ordinary : name.val ≠ "mut".toList)
      (region : Local scope .ownedRegion) (visible : region.nameVisible)
      (initializer : RegionInitializer) :
      Stmt result scope (⟨name, initializer.type, false, false⟩ :: scope)

/-- Sequential scope composition inside a pair of braces. -/
inductive Block (result : Option (Ty .value)) : Scope → Scope → Type where
  | done : Block result scope scope
  | step : Stmt result before middle → Block result middle after → Block result before after

/-- Written braces delimit the lifetime and visibility of the body's new locals. -/
inductive BracedBlock (result : Option (Ty .value)) : Scope → Type where
  | braces (body : Block result before after) : BracedBlock result before

/-- Exhaustiveness is the index of an arm sequence. The optional final wildcard
    consumes every remaining declared case without binding a payload. -/
inductive VariantArms (result : Option (Ty .value)) : Scope → Bool →
    List Identifier → List (Option (Ty .value)) → Type where
  | done : VariantArms result scope allowWildcard [] []
  | nullary (label : Identifier) (caseName : label.val ≠ ['_']) (body : BracedBlock result scope)
      (rest : VariantArms result scope true labels payloads) :
      VariantArms result scope allowWildcard (label :: labels) (none :: payloads)
  | payload (label binder : Identifier) (ordinary : ordinaryLocal binder)
      (body : BracedBlock result (payloadBinding binder type :: scope))
      (rest : VariantArms result scope true labels payloads) :
      VariantArms result scope allowWildcard (label :: labels) (some type :: payloads)
  | wildcard (body : BracedBlock result scope) (nonempty : labels ≠ [])
      (shape : labels.length = payloads.length) : VariantArms result scope true labels payloads

end

mutual
def Stmt.returns : Stmt result before after → Bool
  | .ret .. | .retVoid .. => true
  | .ite _ yes no => yes.returns && no.returns
  | .variantMatch _ arms => arms.returns
  | _ => false

def Block.returns : Block result before after → Bool
  | .done => false
  | .step first rest => first.returns || rest.returns

def BracedBlock.returns : BracedBlock result before → Bool
  | .braces body => body.returns

def VariantArms.returns : VariantArms result scope allowed labels payloads → Bool
  | .done => true
  | .nullary _ _ body rest | .payload _ _ _ body rest => body.returns && rest.returns
  | .wildcard body _ _ => body.returns
end

/-- The return spelling determines the body's return index. -/
def writtenResult (result : Option WrittenType) : Option (Ty .value) := result.map WrittenType.type

structure RecordMember where
  name : Identifier
  written : WrittenType

def recordLabels (fields : List RecordMember) : List Identifier := fields.map RecordMember.name

def recordTypes (fields : List RecordMember) : List (Ty .value) :=
  fields.map (fun field => field.written.type)

def recordBinding (name : Identifier) (fields : List RecordMember) : Binding :=
  ⟨name, recordSchemaType name.val (recordLabels fields) (recordTypes fields), false, true⟩

structure VariantMember where
  label : Identifier
  payload : Option WrittenType

def variantLabels (cases : List VariantMember) : List Identifier := cases.map VariantMember.label

def variantPayloads (cases : List VariantMember) : List (Option (Ty .value)) :=
  cases.map (fun member => member.payload.map WrittenType.type)

def variantBinding (name : Identifier) (cases : List VariantMember) : Binding :=
  ⟨name, variantSchemaType name.val (variantLabels cases) (variantPayloads cases), false, true⟩

def VariantMember.valid (member : VariantMember) : Prop :=
  ordinaryLocal member.label ∧ member.label.val ≠ ['_'] ∧ ∀ type ∈ member.payload.toList, type.valid

/-- Constant values can enter the declaration scope. Function signatures are resolved
    across the whole unit, allowing forward calls and checked recursive cycles. -/
inductive Decl : Scope → Scope → Type where
  | constant (name : Identifier) (ordinary : ordinaryLocal name) (written : WrittenType)
      (valid : written.valid) (value : Expr before type) (staticValue : value.static) (fits : Fits type written.type) :
      Decl before (⟨name, written.type, false, true⟩ :: before)
  | function (name : Identifier) (ordinary : directName name) (parameters : List Parameter)
      (result : Option WrittenType) (valid : ∀ t ∈ result.toList, WrittenType.valid t)
      (decreases : Option (Measure (functionScope before parameters)))
      (body : BracedBlock (writtenResult result) (functionScope before parameters))
      (distinct : (parameters.map (fun p => p.name.val)).Nodup)
      (returns : result.isSome = true → body.returns = true) :
      Decl before before
  /-- The ordinary record declaration installs its nominal schema in the declaration scope. -/
  | record (exported : Bool) (name : Identifier) (fields : List RecordMember)
      (valid : ∀ member ∈ fields, member.written.valid)
      (distinct : ((recordLabels fields).map Subtype.val).Nodup) :
      Decl before (recordBinding name fields :: before)
  /-- The declared tag order determines the closed sum and its exhaustive matches. -/
  | tagged (exported : Bool) (name : Identifier) (first : VariantMember) (tail : List VariantMember)
      (valid : ∀ member ∈ first :: tail, member.valid)
      (distinct : ((variantLabels (first :: tail)).map Subtype.val).Nodup) :
      Decl before (variantBinding name (first :: tail) :: before)
  /-- A name for a firmware interface whose contract comes from the selected catalogue. -/
  | environment (name : Identifier) (abi : Katalog.DienstAbi) (row : Katalog.FirmwareZeile) :
      Decl before before

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
