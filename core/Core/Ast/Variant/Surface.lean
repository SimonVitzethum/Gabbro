module

public import Core.Ast.Aggregate.RecordSurface

@[expose] public section

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text

structure TaggedDeclArgs where
  exported : Bool
  name : Identifier
  first : VariantMember
  tail : List VariantMember
  valid : ∀ member ∈ first :: tail, member.valid
  distinct : ((variantLabels (first :: tail)).map Subtype.val).Nodup

def TaggedDeclArgs.cases (a : TaggedDeclArgs) : List VariantMember := a.first :: a.tail

def taggedDecl (scope : Scope) : Rule (.declaration scope) TaggedDeclArgs where
  tree := fun a => ⟨_, .tagged a.exported a.name a.first a.tail a.valid a.distinct⟩
  production := fun a tokens =>
    ∃ input more, tokens = taggedDeclarationPrefix a.exported ++ [.word a.name.val, assignment, openBrace] ++ input ∧
      VariantMemberRead input a.first more ∧ VariantMembersTailRead more a.tail [semicolon]

structure VariantValueArgs (scope : Scope) where
  labels : List Identifier
  payloads : List (Option (Ty .value))
  ref : VariantRef scope labels payloads
  label : Identifier
  index : Fin payloads.length
  written : labels[index.val]? = some label
  ordinary : ordinaryLocal label
  available : availableCase scope label
  payload : CasePayload scope (payloads.get index)

def VariantValueArgs.expression (a : VariantValueArgs scope) :
    Expr scope (variantValueType a.ref.name.val a.labels a.payloads) :=
  .variantValue a.ref a.label a.index a.written a.ordinary a.available a.payload

def variantValue (scope : Scope) : Rule (.expression scope) (VariantValueArgs scope) where
  tree := fun a => a.expression.typed
  production := fun a tokens =>
    ∃ input, tokens = .word a.label.val :: input ∧ CasePayloadRead scope input a.payload []

structure VariantMatchArgs (ctx : Scope × Option (Ty .value)) where
  name : List Char
  labels : List Identifier
  payloads : List (Option (Ty .value))
  value : Expr ctx.1 (variantValueType name labels payloads)
  arms : VariantArms ctx.2 ctx.1 labels payloads

def variantMatch (ctx : Scope × Option (Ty .value)) :
    Rule (.statement ctx.1 ctx.2) (VariantMatchArgs ctx) where
  tree := fun a => ⟨_, .variantMatch a.value a.arms⟩
  production := fun a tokens =>
    ∃ input arms, tokens = keyword "match" :: input ∧
      ExprReads ctx.1 0 input a.value (openBrace :: arms) ∧ VariantArmsRead ctx.2 ctx.1 arms a.arms []

def TaggedDeclInversionAussage : Prop :=
  ∀ {scope input tree rest} (exported : Bool) (name : Identifier),
    DeclReads scope (taggedDeclarationPrefix exported ++ [.word name.val, assignment, openBrace] ++ input)
      tree rest →
    ∃ (a : TaggedDeclArgs) (more : List Token), a.exported = exported ∧ a.name = name ∧
      VariantMemberRead input a.first more ∧ VariantMembersTailRead more a.tail (semicolon :: rest) ∧
      tree = (taggedDecl scope).tree a

def TaggedDeclSuffixAussage : Prop :=
  ∀ {input variants rest}, VariantMembersTailRead input variants (semicolon :: rest) → rest <:+ input

def TaggedDeclDerivationAussage : Prop :=
  ∀ scope, (taggedDecl scope).Entry

def VariantValueInversionAussage : Prop :=
  ∀ {scope input type} {tree : Expr scope type} {rest} (caseName : Identifier),
    ordinaryLocal caseName → availableCase scope caseName →
    AtomReads scope (.word caseName.val :: input) tree rest →
    ∃ a : VariantValueArgs scope, a.label = caseName ∧ CasePayloadRead scope input a.payload rest ∧
      tree.typed = a.expression.typed

def VariantValueSuffixAussage : Prop :=
  ∀ {scope input type} {payload : CasePayload scope type} {rest},
    CasePayloadRead scope input payload rest → rest <:+ input

def VariantValueDerivationAussage : Prop :=
  ∀ scope, (variantValue scope).Entry

def VariantMatchInversionAussage : Prop :=
  ∀ {scope result input tree rest}, StmtReads result scope (keyword "match" :: input) tree rest →
    ∃ (a : VariantMatchArgs (scope, result)) (arms : List Token),
      ExprReads scope 0 input a.value (openBrace :: arms) ∧ VariantArmsRead result scope arms a.arms rest ∧
      tree = (variantMatch (scope, result)).tree a

def VariantMatchSuffixAussage : Prop :=
  ∀ {scope result labels payloads input rest} {arms : VariantArms result scope labels payloads},
    VariantArmsRead result scope input arms rest → rest <:+ input

def VariantMatchDerivationAussage : Prop :=
  ∀ ctx, (variantMatch ctx).Entry

end Gabbro.Core.Ast.Surface
