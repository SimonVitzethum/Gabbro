module

public import Core.Ast.Block
public import Core.Ast.LowLevel.Syntax
public import Core.Ast.Aggregate.Carrier.Grammar
public import Core.Ast.Aggregate.Carrier.Effects.Grammar

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

abbrev Declaration (before : Scope) := (after : Scope) × Decl before after

inductive ResultReads (before : Scope) : List Token → Option WrittenType → List Token → Prop where
  | absent (closed : ∀ tail, rest ≠ arrow :: tail) : ResultReads before rest none rest
  | typed : TypeReads before input written rest → ResultReads before (arrow :: input) (some written) rest

inductive MeasureReads (scope : Scope) : List Token → Option (Measure scope) → List Token → Prop where
  | absent (closed : ∀ tail, rest ≠ keyword "decreases" :: tail) :
      MeasureReads scope rest none rest
  | present (m : Measure scope) : ExprReads scope 0 input m.expression rest →
      MeasureReads scope (keyword "decreases" :: input) (some m) rest

inductive DeclReads (before : Scope) : List Token → Declaration before → List Token → Prop where
  | constant (name : Identifier) (ordinary : ordinaryLocal name) (written : WrittenType) (valid : written.valid before)
      (value : Expr before type) (staticValue : value.static) (fits : Fits type written.type) :
      TypeReads before input written (assignment :: rhs) →
      ExprReads before 0 rhs value (semicolon :: rest) →
      DeclReads before (keyword "const" :: .word name.val :: colon :: input)
        ⟨_, .constant name ordinary written valid value staticValue fits⟩ rest
  | function (name : Identifier) (ordinary : directName name) (result : Option WrittenType)
      (valid : ∀ t ∈ result.toList, WrittenType.valid before t) (parameters : List (Parameter before))
      (measure : Option (Measure (functionScope before parameters)))
      (body : BracedBlock (writtenResult result) (functionScope before parameters))
      (distinct : (parameters.map (fun p => p.name.val)).Nodup)
      (returns : result.isSome = true → body.returns = true)
      (effects : Option (EffectClause before parameters)) :
      ParamsRead before input parameters afterParams →
      ResultReads before afterParams result afterResult →
      EffectClauseReads before parameters afterResult effects afterEffects →
      MeasureReads (functionScope before parameters) afterEffects measure afterMeasure →
      BlockReads (writtenResult result) (functionScope before parameters) afterMeasure body rest →
      DeclReads before (keyword "fn" :: .word name.val :: openParen :: input)
        ⟨before, .function name ordinary parameters result valid measure body distinct returns effects⟩ rest
  | record (exported : Bool) (name : Identifier) (valid : ∀ member ∈ fields, member.written.valid before)
      (distinct : ((recordLabels fields).map Subtype.val).Nodup) :
      RecordMembersRead before input fields (semicolon :: rest) →
      DeclReads before
        (recordDeclarationPrefix exported ++ [.word name.val, assignment, openBrace] ++ input)
        ⟨_, .record exported name fields valid distinct⟩ rest
  | tagged (exported : Bool) (name : Identifier) (valid : ∀ member ∈ first :: tail, member.valid before)
      (distinct : ((variantLabels (first :: tail)).map Subtype.val).Nodup) :
      VariantMemberRead before input first more → VariantMembersTailRead before more tail (semicolon :: rest) →
      DeclReads before
        (taggedDeclarationPrefix exported ++ [.word name.val, assignment, openBrace] ++ input)
        ⟨_, .tagged exported name first tail valid distinct⟩ rest
  | table (item : TableDeclaration before) :
      TableFieldsRead (carrierFieldScope before item.name item.count) input item.fields (closeBrace :: rest) →
      DeclReads before (item.header.map PrintedToken.value ++ input) ⟨_, .table item⟩ rest
  | effectGroup (item : EffectGroupDeclaration before) :
      EffectListReads CarrierEffectReads input item.written (semicolon :: rest) →
      DeclReads before (item.header.map PrintedToken.value ++ input) ⟨_, .effectGroup item⟩ rest

  | environment (name : Identifier) (abi : Katalog.DienstAbi) (row : Katalog.FirmwareZeile) :
      DeclReads before (LowLevel.environmentTokens name abi row ++ rest)
        ⟨before, .environment name abi row⟩ rest

def resultPieces : Option WrittenType → List PrintedToken
  | none => []
  | some written => printArrow :: written.printPieces

def measurePieces : Option (Measure scope) → List PrintedToken
  | none => []
  | some m => printDecreases :: m.expression.printPieces

def Decl.printPieces : Decl before after → List PrintedToken
  | .constant name _ written _ value _ _ =>
    [printConst, name.print, printColon] ++ written.printPieces ++ [printAssignment] ++
      value.printPieces ++ [printSemicolon]
  | .function name _ parameters result _ measure body _ _ effects =>
    [printFn, name.print, printOpen] ++ commaSeparated (parameters.map Parameter.printPieces) ++
      [printClose] ++ resultPieces result ++ effectClausePieces effects ++ measurePieces measure ++ body.printPieces
  | .record exported name fields _ _ =>
    recordDeclarationHead exported ++ [name.print, printAssignment, printOpenBrace] ++
      fields.flatMap RecordMember.printPieces ++ [printCloseBrace, printSemicolon]
  | .tagged exported name first tail _ _ =>
    taggedDeclarationHead exported ++ [name.print, printAssignment, printOpenBrace] ++
      commaSeparated ((first :: tail).map VariantMember.printPieces) ++ [printCloseBrace, printSemicolon]
  | .table item =>
    item.header ++ item.fields.flatMap RecordMember.printPieces ++ [printCloseBrace, printCloseBrace]
  | .effectGroup item =>
    item.header ++ commaSeparated (item.written.map WrittenCarrierEffect.printPieces) ++
      [printCloseBrace, printSemicolon]
  | .environment name abi row => (LowLevel.Tree.environment name abi row).printPieces

end Gabbro.Core.Ast
