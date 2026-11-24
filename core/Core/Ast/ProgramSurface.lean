module

public import Core.Ast.Program.SurfaceForms

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def OptionLetReadAt (result : Option (Ty .value)) (scope : Scope) (mutable : Bool)
    (spelling : RawText) (input : List Token) (tree : Statement result scope) (rest : List Token) : Prop :=
  ∃ (name carrier : Identifier) (count : Nat)
    (ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name)
    (resolved : scope.carrierCount carrier = some count) (value : OptionInitializer scope count) (rhs : List Token),
    name.val = spelling ∧ TypeReads scope input (.indexOption carrier count) (assignment :: rhs) ∧
    OptionInitializerReads scope count rhs value (semicolon :: rest) ∧
    tree = ⟨_, .letOption mutable name ordinary carrier resolved value⟩

private theorem directHead_not_reserved (ordinary : directName name) (keywordName : String)
    (reserved : keywordName ∈ ["let", "if", "return", "while", "for", "leave", "next", "match"])
    (same : Token.word name.val :: first = keyword keywordName :: second) : False :=
  ordinary.2 (List.mem_map.mpr ⟨keywordName, reserved, (Token.word.inj (List.cons.inj same).1).symm⟩)

local macro "reject_statement_prefix" equality:ident : tactic =>
  `(tactic|
    (exfalso
     first
     | (cases (List.cons.inj $equality).1; done)
     | (cases (List.cons.inj (List.cons.inj $equality).2).1; done)
     | (cases (List.cons.inj (List.cons.inj (List.cons.inj $equality).2).2).1; done)
     | cases (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj $equality).2).2).2).1))

-- Mirror StmtReads.ret_inversion using the semicolon discriminator.
theorem StmtReads.returnVoid_inversion
    (read : StmtReads result scope (returnKeyword :: semicolon :: input) tree rest) :
    ∃ (a : Surface.ReturnVoidArgs scope result),
      tree = (Surface.returnVoid scope result).tree a ∧ rest = input := by
  generalize h : (returnKeyword :: semicolon :: input) = tokens at read
  cases read with
  | retVoid declared =>
    exact ⟨⟨declared⟩, rfl, (List.cons.inj (List.cons.inj h).2).2.symm⟩
  | ret _ _ valueRead =>
    rw [← (List.cons.inj h).2] at valueRead
    cases valueRead with
    | atom atomRead _ => cases atomRead
  | retOption _ valueRead =>
    rw [← (List.cons.inj h).2] at valueRead
    cases valueRead
  | directCall callRead => cases callRead; reject_statement_prefix h
  | letOption mutable _ _ _ _ _ _ => cases mutable <;> reject_statement_prefix h
  | _ => reject_statement_prefix h

-- Mirror StmtReads.let_header using the mutable annotated header.
theorem StmtReads.mutableLocal_inversion
    (read : StmtReads result scope (letKeyword :: keyword "mut" :: .word spelling :: colon :: input)
      tree rest) :
    (∃ (a : Surface.MutableLocalArgs scope result) (rhs : List Token),
      a.name.val = spelling ∧ TypeReads scope input a.written (assignment :: rhs) ∧
      ExprReads scope 0 rhs a.value (semicolon :: rest) ∧
      tree = (Surface.mutableLocal scope result).tree a) ∨
    OptionLetReadAt result scope true spelling input tree rest := by
  generalize h : (letKeyword :: keyword "mut" :: Token.word spelling :: colon :: input) = tokens at read
  cases read with
  | letMutable name ordinary written valid fits typeRead valueRead =>
    have tail := (List.cons.inj (List.cons.inj h).2).2
    have nameEq := Token.word.inj (List.cons.inj tail).1
    cases (List.cons.inj (List.cons.inj tail).2).2
    exact .inl ⟨⟨name, ordinary, written, valid, _, _, fits⟩, _, nameEq.symm, typeRead, valueRead, rfl⟩
  | letOption mutable name ordinary carrier resolved typeRead valueRead =>
    cases mutable with
    | false => reject_statement_prefix h
    | true =>
      have tail := (List.cons.inj (List.cons.inj h).2).2
      have nameEq := Token.word.inj (List.cons.inj tail).1
      cases (List.cons.inj (List.cons.inj tail).2).2
      exact .inr ⟨name, carrier, _, ordinary, resolved, _, _, nameEq.symm, typeRead, valueRead, rfl⟩
  | tupleBind _ patternRead _ _ => cases patternRead; reject_statement_prefix h
  | directCall callRead => cases callRead; reject_statement_prefix h
  | _ => reject_statement_prefix h

-- Mirror CallReads.inversion after disambiguating the reserved statement heads.
theorem StmtReads.directCall_inversion (name : Identifier) (ordinary : directName name)
    (read : StmtReads result scope (.word name.val :: openParen :: input) tree rest) :
    ∃ (a : Surface.DirectCallArgs scope result),
      a.name = name ∧ ArgsRead scope input a.args (semicolon :: rest) ∧
      tree = (Surface.directCall scope result).tree a := by
  generalize h : (Token.word name.val :: openParen :: input) = tokens at read
  cases read with
  | directCall callRead =>
    cases callRead with
    | applied call argsRead =>
      have nameEq := Token.word.inj (List.cons.inj h).1
      cases (List.cons.inj (List.cons.inj h).2).2
      exact ⟨call, Subtype.ext nameEq.symm, argsRead, rfl⟩
  | ret _ _ _ => exact (directHead_not_reserved ordinary "return" (by decide) h).elim
  | retVoid _ => exact (directHead_not_reserved ordinary "return" (by decide) h).elim
  | retOption _ _ => exact (directHead_not_reserved ordinary "return" (by decide) h).elim
  | ite _ _ _ => exact (directHead_not_reserved ordinary "if" (by decide) h).elim
  | whileBounded _ _ _ _ _ _ _ => exact (directHead_not_reserved ordinary "while" (by decide) h).elim
  | variantMatch _ _ => exact (directHead_not_reserved ordinary "match" (by decide) h).elim
  | tupleBind _ _ _ _ => exact (directHead_not_reserved ordinary "let" (by decide) h).elim
  | letOption mutable _ _ _ _ _ _ => cases mutable <;> reject_statement_prefix h
  | _ => reject_statement_prefix h

-- Mirror StmtReads.let_header with the written type and the call's argument derivation.
theorem StmtReads.bindDirect_inversion
    (read : StmtReads result scope (letKeyword :: .word spelling :: colon :: input) tree rest) :
    (∃ (a : Surface.BindDirectArgs scope result) (rhs : List Token),
      a.name.val = spelling ∧ TypeReads scope input a.written (assignment :: rhs) ∧
      CallReads scope rhs a.call (semicolon :: rest) ∧
      tree = (Surface.bindDirect scope result).tree a) ∨
    OptionLetReadAt result scope false spelling input tree rest := by
  generalize h : (letKeyword :: Token.word spelling :: colon :: input) = tokens at read
  cases read with
  | bindDirect name ordinary written valid typeRead callRead =>
    have tail := (List.cons.inj h).2
    have nameEq := Token.word.inj (List.cons.inj tail).1
    cases (List.cons.inj (List.cons.inj tail).2).2
    exact .inl ⟨⟨name, ordinary, written, valid, _⟩, _, nameEq.symm, typeRead, callRead, rfl⟩
  | letOption mutable name ordinary carrier resolved typeRead valueRead =>
    cases mutable with
    | false =>
      have tail := (List.cons.inj h).2
      have nameEq := Token.word.inj (List.cons.inj tail).1
      cases (List.cons.inj (List.cons.inj tail).2).2
      exact .inr ⟨name, carrier, _, ordinary, resolved, _, _, nameEq.symm, typeRead, valueRead, rfl⟩
    | true => reject_statement_prefix h
  | tupleBind _ patternRead _ _ => cases patternRead; reject_statement_prefix h
  | directCall callRead => cases callRead; reject_statement_prefix h
  | _ => reject_statement_prefix h

-- Mirror StmtReads.ite_inversion and retain the distinct bound and body derivations.
theorem StmtReads.boundedWhile_inversion
    (read : StmtReads result scope (keyword "while" :: input) tree rest) :
    (∃ (a : Surface.BoundedWhileArgs scope result) (boundInput bodyInput : List Token),
      ExprReads scope 0 input a.condition (keyword "bounded" :: boundInput) ∧
      ExprReads scope 0 boundInput a.bound
        (keyword "ops" :: keyword "on_exceeded" :: .word a.overflow.val :: bodyInput) ∧
      BlockReads result scope bodyInput a.body rest ∧
      tree = (Surface.boundedWhile scope result).tree a) ∨
    AssignmentStart input := by
  generalize h : (keyword "while" :: input) = tokens at read
  cases read with
  | whileBounded nonnegative overflow bound staticBound condRead boundRead bodyRead =>
    cases (List.cons.inj h).2
    exact .inl ⟨⟨_, _, _, bound, staticBound, nonnegative, overflow, _⟩, _, _, condRead, boundRead, bodyRead, rfl⟩
  | assignVar _ _ _ _ _ => exact .inr (.inl ⟨_, (List.cons.inj h).2⟩)
  | assignField _ _ _ _ _ _ _ _ => exact .inr (.inr ⟨_, _, (List.cons.inj h).2⟩)
  | directCall callRead =>
    cases callRead with
    | applied call argsRead => exact (directHead_not_reserved call.ordinary "while" (by decide) h.symm).elim
  | letOption mutable _ _ _ _ _ _ => cases mutable <;> reject_statement_prefix h
  | _ => reject_statement_prefix h

-- Mirror StmtReads.boundedWhile_inversion, using the distinct range separator.
theorem StmtReads.forRange_inversion
    (read : StmtReads result scope (keyword "for" :: .word spelling :: keyword "in" :: input) tree rest) :
    ∃ (a : Surface.ForRangeArgs scope result) (highInput handlerInput bodyInput : List Token),
      a.name.val = spelling ∧ ExprReads scope 0 input a.lower (openRange :: highInput) ∧
      ExprReads scope 0 highInput a.upper handlerInput ∧
      OverflowReads handlerInput a.overflow bodyInput ∧
      BlockReads result (rangeBinding a.name a.lo a.hi :: scope) bodyInput a.body rest ∧
      tree = (Surface.forRange scope result).tree a := by
  generalize h : (keyword "for" :: Token.word spelling :: keyword "in" :: input) = tokens at read
  cases read with
  | forRange name ordinary body lower upper staticBounds lowerRead upperRead handlerRead bodyRead =>
    have tail := (List.cons.inj h).2
    have nameEq := Token.word.inj (List.cons.inj tail).1
    cases (List.cons.inj (List.cons.inj tail).2).2
    exact ⟨⟨name, ordinary, _, _, _, _, lower, upper, staticBounds, _, body⟩,
      _, _, _, nameEq.symm, lowerRead, upperRead, handlerRead, bodyRead, rfl⟩
  | directCall callRead => cases callRead; reject_statement_prefix h
  | letOption mutable _ _ _ _ _ _ => cases mutable <;> reject_statement_prefix h
  | _ => reject_statement_prefix h

-- Mirror UnitBody.printReads and recover the first declaration's unconsumed suffix.
theorem UnitReads.program_inversion (a : Surface.ProgramArgs) (read : UnitReads [] tokens a.unit) :
    ∃ rest, DeclReads [] tokens ⟨a.middle, a.first⟩ rest ∧
      UnitReads a.middle rest ⟨a.after, a.rest⟩ := by
  cases a with
  | mk middle after first rest =>
    cases read with | step firstDecl nextRead => exact ⟨_, firstDecl, nextRead⟩

end Gabbro.Core.Ast
