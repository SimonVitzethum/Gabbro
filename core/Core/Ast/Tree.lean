module

public import Core.Ast.Aggregate.Types.Model

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

/-- The implicit widening at a typed destination is inclusion of the source interval. -/
def Fits : Ty .value → Ty .value → Prop
  | .int lo hi, .int lower upper => lower ≤ lo ∧ hi ≤ upper
  | .bool, .bool => True
  | .text source, .text target => source ≤ target
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
  | textLiteral (decoded : List Char) : Expr scope (.text (sourceUtf8 decoded).size)
  | textConcat (left : Expr scope (.text a)) (right : Expr scope (.text b)) : Expr scope (.text (a + b))
  | textIndex (base : Expr scope (.text capacity)) (offset : Expr scope (.int lo hi)) :
      Expr scope (.int 0 255)
  | substring (base : Expr scope (.text capacity)) (first : Expr scope (.int lo₁ hi₁))
      (last : Expr scope (.int lo₂ hi₂)) : Expr scope (.text capacity)
  | textLength (base : Expr scope (.text capacity)) : Expr scope (.int 0 capacity)
  | optionIsSome (ref : Local scope (indexOptionType count)) (visible : ref.visible)
      (ordinary : ordinaryLocal ref.binding.name) : Expr scope .bool

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
  | .textConcat left right => left.static ∧ right.static
  | .textIndex base offset => base.static ∧ offset.static
  | .substring base first last => base.static ∧ first.static ∧ last.static
  | .textLength base => base.static
  | .optionIsSome ref _ _ => ref.binding.constant = true
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
  | text (capacity : Nat)
  | index (carrier : Identifier) (count : Nat)
  | indexOption (carrier : Identifier) (count : Nat)
  | address (space : LowLevel.AddressSpace)
  | ownedRegion
  /-- `ptr<space, recht> referent`: a checked capability. Execute rights and
      owner marks are refused at the surface (no `x`, no `own`). -/
  | ptr (space : LowLevel.AddressSpace) (recht : PtrRecht) (referent : WrittenType)

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
  | .text capacity => .text capacity
  | .index _ count => indexType count
  | .indexOption _ count => indexOptionType count
  | .address space => .address space
  | .ownedRegion => .ownedRegion
  | .ptr space recht referent => .ptr space recht referent.type

def WrittenTypes.types : WrittenTypes → List (Ty .value)
  | .empty => []
  | .next head tail => head.type :: tail.types

end

mutual

def WrittenType.valid (scope : Scope) : WrittenType → Prop
  | .bool => True
  | .integer signed width range =>
    let (minimum, maximum) := WrittenType.storage signed width
    let (lo, hi) := range.getD (minimum, maximum)
    1 ≤ width ∧ width ≤ 64 ∧ minimum ≤ lo ∧ lo ≤ hi ∧ hi ≤ maximum
  | .array element _count => element.valid scope
  | .tuple first second rest => first.valid scope ∧ second.valid scope ∧ rest.valid scope
  | .text _capacity => True
  | .index carrier count | .indexOption carrier count => scope.carrierCount carrier = some count
  | .address _ | .ownedRegion => True
  | .ptr _ _ referent => referent.valid scope

def WrittenTypes.valid (scope : Scope) : WrittenTypes → Prop
  | .empty => True
  | .next head tail => head.valid scope ∧ tail.valid scope

end

/-- Region work occurs at the binding instruction. The ordinary expression
    grammar cannot duplicate an owned region or a typed view. -/
inductive RegionInitializer where
  | address
  | view (written : WrittenType) (valid : written.valid [])

def RegionInitializer.type : RegionInitializer → Ty .value
  | .address => .address .physical
  | .view written _ => .regionView written.type

structure Parameter (scope : Scope) where
  name : Identifier
  written : WrittenType
  valid : written.valid scope
  ordinary : ordinaryLocal name

def Parameter.binding (p : Parameter scope) : Binding := ⟨p.name, p.written.type, false, false⟩

def functionScope (outer : Scope) (parameters : List (Parameter outer)) : Scope :=
  (parameters.map Parameter.binding).reverse ++ outer

def directName (name : Identifier) : Prop :=
  ordinaryLocal name ∧ name.val ∉
    ["let", "if", "return", "while", "for", "leave", "next", "match", "forever", "mem"].map String.toList

theorem directName_of_singleton (spelling : name.val = [c]) : directName name := by
  simp only [directName, ordinaryLocal, ordinaryAtomWord, spelling, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals first | (intro same; cases same; done) | skip
  · rintro (same | same | same | same | same | same | same | same | same | same) <;> cases same

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

def TuplePattern.valid (pattern : TuplePattern) (scope : Scope) (annotation : Option WrittenType)
    (types : List (Ty .value)) : Prop :=
  pattern.names.length = types.length ∧
    ((pattern.names.filterMap id).map Subtype.val).Nodup ∧
    (∀ name ∈ pattern.names.filterMap id, name.val ≠ ['_'] ∧ ordinaryLocal name) ∧
    ∀ written ∈ annotation.toList, written.valid scope ∧ written.type = tupleType types

def payloadBinding (name : Identifier) (type : Ty .value) : Binding :=
  ⟨name, type, false, false⟩

/-- The destination supplies the carrier count for both option constructors. -/
inductive OptionInitializer (scope : Scope) (count : Nat) where
  | absent
  | present (value : Expr scope (.int lo hi)) (fits : Fits (.int lo hi) (indexType count))

def optionLetHead (mutable : Bool) (name : Identifier) : List Token :=
  .word "let".toList :: (if mutable then [.word "mut".toList] else []) ++
    [.word name.val, .punctuation [':']]

/-- **The memory order of a source access**: the four modes of the memory model (`Speicher.Modus`). `na` is the plain
    access, `rlx` the relaxed atomic, `ra` the release-acquire atomic and `sc` the sequentially consistent one. -/
inductive AccessMode where
  | na
  | rlx
  | ra
  | sc
  deriving DecidableEq

/-- **The access forms of the source (MK-04b)**: one cell of an owned region is read or written in a memory order.
    The region is named by its owner local, the cell by an index expression. Each form elaborates to ONE access
    instruction (`Befehl.zugriff`), whose step the memory model decides: a load binds the value it read, a store binds
    nothing. A later form (an exchange, a compare-and-swap, a fetch-and-add, the confirming observation, the
    publication) is a new constructor at the END of this inductive, not of `Stmt`. -/
inductive Access : Scope → Scope → Type where
  /-- `mem load name : T = region, index, mode;` binds the value read at the written type. -/
  | load (name : Identifier) (ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name)
      (written : WrittenType) (valid : written.valid scope)
      (region : Local scope .ownedRegion) (visible : region.nameVisible)
      (receiverOrdinary : ordinaryLocal region.binding.name)
      (index : Expr scope (.int lo hi)) (mode : AccessMode) :
      Access scope (⟨name, written.type, false, false⟩ :: scope)
  /-- `mem store region, index, value, mode;` writes the value into the cell. -/
  | store (region : Local scope .ownedRegion) (visible : region.nameVisible)
      (receiverOrdinary : ordinaryLocal region.binding.name)
      (index : Expr scope (.int lo hi)) (value : Expr scope (.int valueLo valueHi)) (mode : AccessMode) :
      Access scope scope

end Gabbro.Core.Ast
