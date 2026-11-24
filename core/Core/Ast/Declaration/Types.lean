module

public import Core.Ast.Aggregate.Carrier.Effects.Resolution
public import Core.Katalog.FirmwareNamen

@[expose] public section

namespace Gabbro.Core.Ast

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

def carrierBinding (name : Identifier) (count : Nat) (fields : List RecordMember) (exported : Bool) : Binding :=
  ⟨name, .carrierSchema count ((recordLabels fields).map Subtype.val)
    (tupleType (recordTypes fields)) exported, false, true⟩

/-- The count is available while the declared slot fields themselves are read. -/
def carrierFieldScope (before : Scope) (name : Identifier) (count : Nat) : Scope :=
  carrierBinding name count [] false :: before

structure TableDeclaration (before : Scope) where
  exported : Bool
  name : Identifier
  count : Nat
  fields : List RecordMember
  valid : ∀ field ∈ fields, field.written.valid (carrierFieldScope before name count)
  distinct : ((recordLabels fields).map Subtype.val).Nodup

def TableDeclaration.binding (table : TableDeclaration before) : Binding :=
  carrierBinding table.name table.count table.fields table.exported

structure VariantMember where
  label : Identifier
  payload : Option WrittenType

def variantLabels (cases : List VariantMember) : List Identifier := cases.map VariantMember.label

def variantPayloads (cases : List VariantMember) : List (Option (Ty .value)) :=
  cases.map (fun member => member.payload.map WrittenType.type)

def variantBinding (name : Identifier) (cases : List VariantMember) : Binding :=
  ⟨name, variantSchemaType name.val (variantLabels cases) (variantPayloads cases), false, true⟩

def VariantMember.valid (member : VariantMember) (scope : Scope) : Prop :=
  ordinaryLocal member.label ∧ member.label.val ≠ ['_'] ∧ ∀ type ∈ member.payload.toList, type.valid scope

/-- Constant values can enter the declaration scope. Function signatures are resolved
    across the whole unit, allowing forward calls and checked recursive cycles. -/
inductive Decl : Scope → Scope → Type where
  | constant (name : Identifier) (ordinary : ordinaryLocal name) (written : WrittenType)
      (valid : written.valid before) (value : Expr before type) (staticValue : value.static) (fits : Fits type written.type) :
      Decl before (⟨name, written.type, false, true⟩ :: before)
  | function (name : Identifier) (ordinary : directName name) (parameters : List (Parameter before))
      (result : Option WrittenType) (valid : ∀ t ∈ result.toList, WrittenType.valid before t)
      (decreases : Option (Measure (functionScope before parameters)))
      (body : BracedBlock (writtenResult result) (functionScope before parameters))
      (distinct : (parameters.map (fun p => p.name.val)).Nodup)
      (returns : result.isSome = true → body.returns = true)
      (effects : Option (EffectClause before parameters)) :
      Decl before before
  /-- The ordinary record declaration installs its nominal schema in the declaration scope. -/
  | record (exported : Bool) (name : Identifier) (fields : List RecordMember)
      (valid : ∀ member ∈ fields, member.written.valid before)
      (distinct : ((recordLabels fields).map Subtype.val).Nodup) :
      Decl before (recordBinding name fields :: before)
  /-- The declared tag order determines the closed sum and its exhaustive matches. -/
  | tagged (exported : Bool) (name : Identifier) (first : VariantMember) (tail : List VariantMember)
      (valid : ∀ member ∈ first :: tail, member.valid before)
      (distinct : ((variantLabels (first :: tail)).map Subtype.val).Nodup) :
      Decl before (variantBinding name (first :: tail) :: before)
  | table (item : TableDeclaration before) : Decl before (item.binding :: before)
  | effectGroup (item : EffectGroupDeclaration before) : Decl before (item.binding :: before)

  /-- A firmware interface whose contract comes from the selected catalogue. -/
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
