module

public import Core.Ast.Aggregate.Records.RecordSurface

@[expose] public section

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text

def RecordDeclInversionAussage : Prop :=
  ∀ {scope input tree rest} (exported : Bool) (name : Identifier),
    DeclReads scope (recordDeclarationPrefix exported ++ [.word name.val, assignment, openBrace] ++ input)
      tree rest →
    ∃ a : RecordDeclArgs scope, a.exported = exported ∧ a.name = name ∧
      RecordMembersRead scope input a.members (semicolon :: rest) ∧ tree = (recordDecl scope).tree a

def RecordDeclSuffixAussage : Prop :=
  ∀ {scope input fields rest}, RecordMembersRead scope input fields (semicolon :: rest) → rest <:+ input

def RecordDeclDerivationAussage : Prop :=
  ∀ scope, (recordDecl scope).Entry

def RecordValueInversionAussage : Prop :=
  ∀ {scope labels types input type} (ref : RecordRef scope labels types) {tree : Expr scope type} {rest},
    AtomReads scope (.word ref.name.val :: openParen :: input) tree rest →
    ∃ a : RecordValueArgs scope, a.ref.name = ref.name ∧
      LabeledItemsRead scope input a.args rest ∧ tree.typed = a.expression.typed

def RecordValueSuffixAussage : Prop :=
  ∀ {scope input labels types} {items : LabeledItems scope labels types} {rest},
    LabeledItemsRead scope input items rest → rest <:+ input

def RecordValueDerivationAussage : Prop :=
  ∀ scope, Nonempty (RecordValueArgs scope) → (recordValue scope).Entry

def RecordFieldInversionAussage : Prop :=
  ∀ {scope name labels types minimum input type}
    {base : Expr scope (recordValueType name labels types)} {tree : Expr scope type} {rest}
    (field : Identifier),
    minimum ≤ Infix.projection.precedence →
    ExprTail scope minimum base (dot :: .word field.val :: input) tree rest →
    ∃ (i : Fin types.length) (checked : RecordFieldAt labels field i.val),
      ExprTail scope minimum (.recordField base field i checked) input tree rest

def RecordFieldSuffixAussage : Prop :=
  ∀ {scope name labels types minimum input type field}
    {base : Expr scope (recordValueType name labels types)} {tree : Expr scope type} {rest},
    minimum ≤ Infix.projection.precedence →
    ExprTail scope minimum base (dot :: .word field :: input) tree rest → rest <:+ input

def RecordFieldDerivationAussage : Prop :=
  ∀ scope, Nonempty (RecordFieldArgs scope) → (recordField scope).Entry

def AssignFieldInversionAussage : Prop :=
  ∀ {scope result name field input tree rest},
    StmtReads result scope (.word name :: dot :: .word field :: assignment :: input) tree rest →
    ∃ a : AssignFieldArgs scope, a.ref.binding.name.val = name ∧ a.field.val = field ∧
      ExprReads scope 0 input a.value (semicolon :: rest) ∧ tree = (assignField (scope, result)).tree a

def AssignFieldSuffixAussage : Prop :=
  ∀ {scope result name field input tree rest},
    StmtReads result scope (.word name :: dot :: .word field :: assignment :: input) tree rest →
    rest <:+ input

def AssignFieldDerivationAussage : Prop :=
  ∀ ctx, Nonempty (AssignFieldArgs ctx.1) → (assignField ctx).Entry

def MutableValueInversionAussage : Prop :=
  ∀ {scope result name input tree rest},
    StmtReads result scope (letKeyword :: keyword "mut" :: .word name :: assignment :: input) tree rest →
    ∃ a : MutableValueArgs scope, a.name.val = name ∧
      ExprReads scope 0 input a.value (semicolon :: rest) ∧ tree = (mutableValue (scope, result)).tree a

def MutableValueSuffixAussage : Prop :=
  ∀ {scope result name input tree rest},
    StmtReads result scope (letKeyword :: keyword "mut" :: .word name :: assignment :: input) tree rest →
    rest <:+ input

def MutableValueDerivationAussage : Prop :=
  ∀ ctx, (mutableValue ctx).Entry

def TupleBindInversionAussage : Prop :=
  ∀ {scope result input tree rest},
    StmtReads result scope (letKeyword :: openParen :: input) tree rest →
    ∃ (a : TupleBindArgs scope) (more rhs : List Token), TuplePatternReads (openParen :: input) a.pattern more ∧
      TupleAnnotationReads scope more a.annotation rhs ∧ ExprReads scope 0 rhs a.value (semicolon :: rest) ∧
      tree = (tupleBind (scope, result)).tree a

def TupleBindSuffixAussage : Prop :=
  ∀ {scope result input tree rest},
    StmtReads result scope (letKeyword :: openParen :: input) tree rest → rest <:+ input

def TupleBindDerivationAussage : Prop :=
  ∀ ctx, (tupleBind ctx).Entry

end Gabbro.Core.Ast.Surface
