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

namespace LowLevel

/-- The space indexes inert address data. Arithmetic and executable operands
    have separate rules; this index never carries authority. -/
inductive AddressSpace where
  | physical
  | virtual
  | port
  | guestPhysical
  | ioVirtual
  deriving DecidableEq, Repr

def AddressSpace.name : AddressSpace → String
  | .physical => "physical"
  | .virtual => "virtual"
  | .port => "port"
  | .guestPhysical => "guest_physical"
  | .ioVirtual => "io_virtual"

end LowLevel

inductive Ty : Kind → Type where
  /-- Integers with inclusive, architecture-independent bounds. -/
  | int (lo hi : Int) : Ty .value
  | bool : Ty .value
  | array (element : Ty .value) (count : Nat) : Ty .value
  | productEnd : Ty .value
  | product (head tail : Ty .value) : Ty .value
  | record (name : List Char) (labels : List (List Char)) (layout : Ty .value) : Ty .value
  | recordSchema (name : List Char) (labels : List (List Char)) (layout : Ty .value) : Ty .value
  | sumEnd : Ty .value
  | sum (head tail : Ty .value) : Ty .value
  | variant (name : List Char) (labels : List (List Char)) (hasPayload : List Bool) (layout : Ty .value) : Ty .value
  | variantSchema (name : List Char) (labels : List (List Char)) (hasPayload : List Bool) (layout : Ty .value) : Ty .value
  | address (space : LowLevel.AddressSpace) : Ty .value
  | ownedRegion : Ty .value
  | regionView (element : Ty .value) : Ty .value
  deriving DecidableEq

/-- A positional product has a right-associated, explicitly terminated representation. -/
def tupleType : List (Ty .value) → Ty .value
  | [] => .productEnd
  | head :: tail => .product head (tupleType tail)

/-- The principal element type of a homogeneous literal. Integer elements use their interval hull. -/
def arrayJoin : Ty .value → Ty .value → Option (Ty .value)
  | .int lo hi, .int lower upper => some (.int (min lo lower) (max hi upper))
  | a, b => if a = b then some a else none

def arrayElement : List (Ty .value) → Option (Ty .value)
  | [] => some .productEnd
  | [type] => some type
  | head :: next :: tail => (arrayElement (next :: tail)).bind (arrayJoin head)

structure Binding where
  name : Identifier
  type : Ty .value
  mutable : Bool
  constant : Bool

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

/-- A written occurrence resolves to the nearest binding with that spelling. -/
def Local.nameVisible : Local scope type → Prop
  | .here => True
  | @there _ _ binding ref => binding.name.val ≠ ref.binding.name.val ∧ ref.nameVisible

def Ty.valueBinding : Ty .value → Prop
  | .recordSchema .. | .variantSchema .. | .ownedRegion | .regionView _ => False
  | _ => True

def Local.visible (ref : Local scope type) : Prop :=
  type.valueBinding ∧ ref.nameVisible

def recordValueType (name : List Char) (labels : List Identifier) (types : List (Ty .value)) :
    Ty .value :=
  .record name (labels.map Subtype.val) (tupleType types)

def recordSchemaType (name : List Char) (labels : List Identifier) (types : List (Ty .value)) :
    Ty .value :=
  .recordSchema name (labels.map Subtype.val) (tupleType types)

/-- Resolving a field at a program point requires an unambiguous declared label. -/
def RecordFieldAt (labels : List Identifier) (field : Identifier) (index : Nat) : Prop :=
  (labels.map Subtype.val).Nodup ∧ labels[index]? = some field

structure RecordRef (scope : Scope) (labels : List Identifier) (types : List (Ty .value)) where
  name : Identifier
  schema : Local scope (recordSchemaType name.val labels types)
  visible : schema.nameVisible
  spelled : schema.binding.name.val = name.val
  shape : labels.length = types.length
  distinct : (labels.map Subtype.val).Nodup

/-- Actuals can be supplied in source order. Each declared field selects one distinct actual. -/
structure RecordArguments (labels : List Identifier) (types : List (Ty .value))
    (actualLabels : List Identifier) (actualTypes : List (Ty .value)) where
  arity : types.length = actualTypes.length
  distinct : (actualLabels.map Subtype.val).Nodup
  slot : Fin types.length → Fin actualTypes.length
  label : ∀ i, labels[i.val]? = actualLabels[(slot i).val]?

def variantLayout : List (Option (Ty .value)) → Ty .value
  | [] => .sumEnd
  | head :: tail => .sum (head.getD .productEnd) (variantLayout tail)

def variantValueType (name : List Char) (labels : List Identifier) (payloads : List (Option (Ty .value))) : Ty .value :=
  .variant name (labels.map Subtype.val) (payloads.map Option.isSome) (variantLayout payloads)

def variantSchemaType (name : List Char) (labels : List Identifier) (payloads : List (Option (Ty .value))) : Ty .value :=
  .variantSchema name (labels.map Subtype.val) (payloads.map Option.isSome) (variantLayout payloads)

def Ty.variantLabels : Ty .value → List (List Char)
  | .variantSchema _ labels _ _ => labels
  | _ => []

def availableCase (scope : Scope) (label : Identifier) : Prop :=
  ((scope.flatMap fun binding => binding.type.variantLabels).count label.val = 1) ∧
    ∀ binding ∈ scope, binding.name.val ≠ label.val

structure VariantRef (scope : Scope) (labels : List Identifier) (payloads : List (Option (Ty .value))) where
  name : Identifier
  schema : Local scope (variantSchemaType name.val labels payloads)
  visible : schema.nameVisible
  spelled : schema.binding.name.val = name.val
  shape : labels.length = payloads.length
  distinct : (labels.map Subtype.val).Nodup

end Gabbro.Core.Ast
