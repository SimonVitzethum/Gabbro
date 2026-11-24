module

public import Core.Ast.Block
public import Core.Ast.Aggregate.RecordGrammar
public import Core.Ast.LowLevel.Syntax

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

abbrev Declaration (before : Scope) := (after : Scope) × Decl before after

inductive ResultReads : List Token → Option WrittenType → List Token → Prop where
  | absent (closed : ∀ tail, rest ≠ arrow :: tail) : ResultReads rest none rest
  | typed : TypeReads input written rest → ResultReads (arrow :: input) (some written) rest

inductive MeasureReads (scope : Scope) : List Token → Option (Measure scope) → List Token → Prop where
  | absent (closed : ∀ tail, rest ≠ keyword "decreases" :: tail) :
      MeasureReads scope rest none rest
  | present (m : Measure scope) : ExprReads scope 0 input m.expression rest →
      MeasureReads scope (keyword "decreases" :: input) (some m) rest

inductive DeclReads (before : Scope) : List Token → Declaration before → List Token → Prop where
  | constant (name : Identifier) (ordinary : ordinaryLocal name) (written : WrittenType) (valid : written.valid)
      (value : Expr before type) (staticValue : value.static) (fits : Fits type written.type) :
      TypeReads input written (assignment :: rhs) →
      ExprReads before 0 rhs value (semicolon :: rest) →
      DeclReads before (keyword "const" :: .word name.val :: colon :: input)
        ⟨_, .constant name ordinary written valid value staticValue fits⟩ rest
  | function (name : Identifier) (ordinary : directName name) (result : Option WrittenType)
      (valid : ∀ t ∈ result.toList, WrittenType.valid t) (parameters : List Parameter)
      (measure : Option (Measure (functionScope before parameters)))
      (body : BracedBlock (writtenResult result) (functionScope before parameters))
      (distinct : (parameters.map (fun p => p.name.val)).Nodup)
      (returns : result.isSome = true → body.returns = true) :
      ParamsRead input parameters afterParams →
      ResultReads afterParams result afterResult →
      MeasureReads (functionScope before parameters) afterResult measure afterMeasure →
      BlockReads (writtenResult result) (functionScope before parameters) afterMeasure body rest →
      DeclReads before (keyword "fn" :: .word name.val :: openParen :: input)
        ⟨before, .function name ordinary parameters result valid measure body distinct returns⟩ rest
  | record (exported : Bool) (name : Identifier) (valid : ∀ member ∈ fields, member.written.valid)
      (distinct : ((recordLabels fields).map Subtype.val).Nodup) :
      RecordMembersRead input fields (semicolon :: rest) →
      DeclReads before
        (recordDeclarationPrefix exported ++ [.word name.val, assignment, openBrace] ++ input)
        ⟨_, .record exported name fields valid distinct⟩ rest
  | tagged (exported : Bool) (name : Identifier) (valid : ∀ member ∈ first :: tail, member.valid)
      (distinct : ((variantLabels (first :: tail)).map Subtype.val).Nodup) :
      VariantMemberRead input first more → VariantMembersTailRead more tail (semicolon :: rest) →
      DeclReads before
        (taggedDeclarationPrefix exported ++ [.word name.val, assignment, openBrace] ++ input)
        ⟨_, .tagged exported name first tail valid distinct⟩ rest
  | environment (name : Identifier) (abi : Katalog.DienstAbi) (row : Katalog.FirmwareZeile) :
      DeclReads before
        (keyword "environment" :: .word name.val :: keyword "abi" :: keyword abi.name ::
          assignment :: keyword "catalogue" :: keyword row.name :: semicolon :: rest)
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
  | .function name _ parameters result _ measure body _ _ =>
    [printFn, name.print, printOpen] ++ commaSeparated (parameters.map Parameter.printPieces) ++
      [printClose] ++ resultPieces result ++ measurePieces measure ++ body.printPieces
  | .record exported name fields _ _ =>
    recordDeclarationHead exported ++ [name.print, printAssignment, printOpenBrace] ++
      fields.flatMap RecordMember.printPieces ++ [printCloseBrace, printSemicolon]
  | .tagged exported name first tail _ _ =>
    taggedDeclarationHead exported ++ [name.print, printAssignment, printOpenBrace] ++
      commaSeparated ((first :: tail).map VariantMember.printPieces) ++ [printCloseBrace, printSemicolon]
  | .environment name abi row => (LowLevel.Tree.environment name abi row).printPieces

-- Mirror StmtReads.assign_inversion with the written type and const initializer.
theorem DeclReads.constant_inversion
    (read : DeclReads before (keyword "const" :: .word spelling :: colon :: input) tree rest) :
    ∃ (name : Identifier) (ordinary : ordinaryLocal name) (written : WrittenType) (valid : written.valid)
      (type : Ty .value) (value : Expr before type) (staticValue : value.static) (fits : Fits type written.type) (rhs : List Token),
      name.val = spelling ∧ TypeReads input written (assignment :: rhs) ∧
      ExprReads before 0 rhs value (semicolon :: rest) ∧
      tree = ⟨_, .constant name ordinary written valid value staticValue fits⟩ := by
  sorry

-- Mirror BlockReads.braced_inversion and keep every header derivation in token order.
theorem DeclReads.function_inversion
    (read : DeclReads before (keyword "fn" :: .word spelling :: openParen :: input) tree rest) :
    ∃ (name : Identifier) (ordinary : directName name) (ps : List Parameter)
      (result : Option WrittenType) (valid : ∀ t ∈ result.toList, WrittenType.valid t)
      (measure : Option (Measure (functionScope before ps)))
      (body : BracedBlock (writtenResult result) (functionScope before ps))
      (distinct : (ps.map (fun p => p.name.val)).Nodup)
      (returns : result.isSome = true → body.returns = true)
      (afterParams afterResult afterMeasure : List Token),
      name.val = spelling ∧ ParamsRead input ps afterParams ∧
      ResultReads afterParams result afterResult ∧
      MeasureReads (functionScope before ps) afterResult measure afterMeasure ∧
      BlockReads (writtenResult result) (functionScope before ps) afterMeasure body rest ∧
      tree = ⟨before, .function name ordinary ps result valid measure body distinct returns⟩ := by
  sorry

-- Mirror StmtReads.deterministic, using the header and body derivations in order.
theorem DeclReads.deterministic (left : DeclReads before input a rest)
    (right : DeclReads before input b rest') : a = b ∧ rest = rest' := by
  sorry

-- Mirror StmtReads.disjoint_closeBrace using the nonempty declaration prefix.
theorem DeclReads.disjoint_end : ¬ DeclReads before [] tree rest := by
  sorry

-- Mirror StmtReads.consumes using the type, expression and block suffixes.
theorem DeclReads.consumes (read : DeclReads before input tree rest) : rest <:+ input := by
  sorry

-- Mirror BracedBlock.printReads using ParamsRead.printReads for the function header.
theorem Decl.printReads (tree : Decl before after) (rest : List Token) :
    DeclReads before (tree.printPieces.map PrintedToken.value ++ rest) ⟨after, tree⟩ rest := by
  sorry

end Gabbro.Core.Ast
