module

public import Core.Ast.Aggregate.Surface

@[expose] public section

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text

structure RecordDeclArgs (scope : Scope) where
  exported : Bool
  name : Identifier
  members : List RecordMember
  valid : ∀ member ∈ members, member.written.valid scope
  distinct : ((recordLabels members).map Subtype.val).Nodup

def recordDecl (scope : Scope) : Rule (.declaration scope) (RecordDeclArgs scope) where
  tree := fun a => ⟨_, .record a.exported a.name a.members a.valid a.distinct⟩
  production := fun a tokens =>
    ∃ input, tokens = recordDeclarationPrefix a.exported ++ [.word a.name.val, assignment, openBrace] ++ input ∧
      RecordMembersRead scope input a.members [semicolon]

structure RecordValueArgs (scope : Scope) where
  labels : List Identifier
  types : List (Ty .value)
  ref : RecordRef scope labels types
  actualLabels : List Identifier
  actualTypes : List (Ty .value)
  args : LabeledItems scope actualLabels actualTypes
  fields : RecordArguments labels types actualLabels actualTypes
  fits : ∀ i, Fits (actualTypes.get (fields.slot i)) (types.get i)

def RecordValueArgs.expression (args : RecordValueArgs scope) :
    Expr scope (recordValueType args.ref.name.val args.labels args.types) :=
  .recordValue args.ref args.args args.fields args.fits

def recordValue (scope : Scope) : Rule (.expression scope) (RecordValueArgs scope) where
  tree := fun a => a.expression.typed
  production := fun a tokens =>
    ∃ input, tokens = .word a.ref.name.val :: openParen :: input ∧ LabeledItemsRead scope input a.args []

structure RecordFieldArgs (scope : Scope) where
  name : List Char
  labels : List Identifier
  types : List (Ty .value)
  base : Expr scope (recordValueType name labels types)
  field : Identifier
  index : Fin types.length
  written : RecordFieldAt labels field index.val

def RecordFieldArgs.expression (a : RecordFieldArgs scope) : Expr scope (a.types.get a.index) :=
  .recordField a.base a.field a.index a.written

def recordField (scope : Scope) : Rule (.expression scope) (RecordFieldArgs scope) where
  tree := fun a => a.expression.typed
  production := fun a => postfixProduction fun input rest =>
    ExprReads scope 8 input a.base (dot :: .word a.field.val :: rest)

structure AssignFieldArgs (scope : Scope) where
  name : List Char
  labels : List Identifier
  types : List (Ty .value)
  ref : Local scope (recordValueType name labels types)
  visible : ref.visible
  writable : ref.binding.mutable = true
  field : Identifier
  index : Fin types.length
  written : RecordFieldAt labels field index.val
  source : Ty .value
  value : Expr scope source
  fits : Fits source (types.get index)

def assignField (ctx : Scope × Option (Ty .value)) : Rule (.statement ctx.1 ctx.2) (AssignFieldArgs ctx.1) where
  tree := fun a => ⟨_, .assignField a.ref a.visible a.writable a.field a.index a.written a.value a.fits⟩
  production := fun a tokens => ∃ input,
    tokens = .word a.ref.binding.name.val :: dot :: .word a.field.val :: assignment :: input ∧
      ExprReads ctx.1 0 input a.value [semicolon]

structure MutableValueArgs (scope : Scope) where
  name : Identifier
  ordinary : ordinaryLocal name
  type : Ty .value
  value : Expr scope type

def mutableValue (ctx : Scope × Option (Ty .value)) : Rule (.statement ctx.1 ctx.2) (MutableValueArgs ctx.1) where
  tree := fun a => ⟨_, .letMutableValue a.name a.ordinary a.value⟩
  production := fun a tokens => ∃ input,
    tokens = letKeyword :: keyword "mut" :: .word a.name.val :: assignment :: input ∧
      ExprReads ctx.1 0 input a.value [semicolon]

structure TupleBindArgs (scope : Scope) where
  first : Ty .value
  second : Ty .value
  tail : List (Ty .value)
  pattern : TuplePattern
  annotation : Option WrittenType
  checked : pattern.valid ctx.1 annotation (first :: second :: tail)
  value : Expr scope (tupleType (first :: second :: tail))

def TupleBindArgs.types (a : TupleBindArgs scope) : List (Ty .value) :=
  a.first :: a.second :: a.tail

def tupleBind (ctx : Scope × Option (Ty .value)) : Rule (.statement ctx.1 ctx.2) (TupleBindArgs ctx.1) where
  tree := fun a => ⟨_, .tupleBind a.pattern a.annotation a.checked a.value⟩
  production := fun a tokens => ∃ input more rhs,
    tokens = letKeyword :: input ∧ TuplePatternReads input a.pattern more ∧
      TupleAnnotationReads ctx.1 more a.annotation rhs ∧ ExprReads ctx.1 0 rhs a.value [semicolon]

end Gabbro.Core.Ast.Surface
