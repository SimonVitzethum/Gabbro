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

-- Mirror StmtReads.ret_inversion using the semicolon discriminator.
theorem StmtReads.returnVoid_inversion
    (read : StmtReads result scope (returnKeyword :: semicolon :: input) tree rest) :
    ∃ (a : Surface.ReturnVoidArgs scope result),
      tree = (Surface.returnVoid scope result).tree a ∧ rest = input := by
  generalize htok : (returnKeyword :: semicolon :: input) = toks at read
  cases read with
  | letBinding _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, trueKeyword, falseKeyword, keyword, assignment, semicolon, colon, openParen, minus, bang, directName] | assignVar _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, trueKeyword, falseKeyword, keyword, assignment, semicolon, colon, openParen, minus, bang, directName]
  | ret _ _ expr =>
      cases expr with
      | atom atomRead _ => cases atomRead <;> simp_all [returnKeyword, letKeyword, ifKeyword, trueKeyword, falseKeyword, keyword, assignment, semicolon, colon, openParen, minus, bang, directName]
  | ite _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, trueKeyword, falseKeyword, keyword, assignment, semicolon, colon, openParen, minus, bang, directName]
  | retVoid declared =>
      injection htok with _ htail
      injection htail with _ hrfl
      subst rest
      exact ⟨⟨declared⟩, rfl, rfl⟩
  | letMutable _ _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, trueKeyword, falseKeyword, keyword, assignment, semicolon, colon, openParen, minus, bang, directName]
  | directCall callRead =>
      cases callRead
      all_goals simp_all [returnKeyword, letKeyword, ifKeyword, trueKeyword, falseKeyword, keyword, assignment, semicolon, colon, openParen, minus, bang, directName]
  | bindDirect _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, trueKeyword, falseKeyword, keyword, assignment, semicolon, colon, openParen, minus, bang, directName]   | whileBounded _ _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, trueKeyword, falseKeyword, keyword, assignment, semicolon, colon, openParen, minus, bang, directName]   | forRange _ _ _ _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, trueKeyword, falseKeyword, keyword, assignment, semicolon, colon, openParen, minus, bang, directName]

-- Mirror StmtReads.let_header using the mutable annotated header.
theorem StmtReads.mutableLocal_inversion
    (read : StmtReads result scope (letKeyword :: keyword "mut" :: .word spelling :: colon :: input)
      tree rest) :
    (∃ (a : Surface.MutableLocalArgs scope result) (rhs : List Token),
      a.name.val = spelling ∧ TypeReads scope input a.written (assignment :: rhs) ∧
      ExprReads scope 0 rhs a.value (semicolon :: rest) ∧
      tree = (Surface.mutableLocal scope result).tree a) ∨
    OptionLetReadAt result scope true spelling input tree rest := by
  generalize htok : (letKeyword :: keyword "mut" :: .word spelling :: colon :: input) = toks at read
  cases read with
  | letMutable name ordinary written valid fits typeRead exprRead =>
      simp only [List.cons.injEq] at htok
      obtain ⟨_, ⟨_, ⟨hspelling, ⟨_, hinput⟩⟩⟩⟩ := htok
      injection hspelling with hname
      subst input
      refine Or.inl ⟨⟨name, ordinary, written, valid, _, _, fits⟩, _, ?_, typeRead, exprRead, rfl⟩
      exact hname.symm
  | letOption mutable name ordinary carrier resolved typeRead initializerRead =>
    cases mutable <;> simp only [optionLetHead, letKeyword, keyword, colon,
      Bool.false_eq_true, if_false, if_true, List.nil_append, List.cons_append,
      List.cons.injEq, Token.word.injEq, true_and] at htok
  · exact (ordinary.1 htok.1.symm).elim
  · obtain ⟨spellingEq, rfl⟩ := htok
    exact Or.inr ⟨name, carrier, _, ordinary, resolved, _, _, spellingEq.symm,
      typeRead, initializerRead, rfl⟩
  | directCall callRead =>
      cases callRead
      all_goals simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]
  | letBinding _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | assignVar _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | ret _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | ite _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | retVoid _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | bindDirect _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | whileBounded _ _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | forRange _ _ _ _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]

-- Mirror CallReads.inversion after disambiguating the reserved statement heads.
theorem StmtReads.directCall_inversion (name : Identifier) (ordinary : directName name)
    (read : StmtReads result scope (.word name.val :: openParen :: input) tree rest) :
    ∃ (a : Surface.DirectCallArgs scope result),
      a.name = name ∧ ArgsRead scope input a.args (semicolon :: rest) ∧
      tree = (Surface.directCall scope result).tree a := by
  generalize htok : (.word name.val :: openParen :: input) = toks at read
  cases read with
  | directCall callRead =>
      cases callRead
      rename_i call args argsProof
      injection htok with hhead htail
      injection hhead with hval
      injection htail with hargs
      subst input
      refine ⟨call, Subtype.ext hval.symm, ?_, rfl⟩
      exact argsProof
  | letBinding _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | assignVar _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | ret _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | ite _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | retVoid _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | letMutable _ _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | bindDirect _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | whileBounded _ _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | forRange _ _ _ _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]

-- Mirror StmtReads.let_header with the written type and the call's argument derivation.
theorem StmtReads.bindDirect_inversion
    (read : StmtReads result scope (letKeyword :: .word spelling :: colon :: input) tree rest) :
    (∃ (a : Surface.BindDirectArgs scope result) (rhs : List Token),
      a.name.val = spelling ∧ TypeReads scope input a.written (assignment :: rhs) ∧
      CallReads scope rhs a.call (semicolon :: rest) ∧
      tree = (Surface.bindDirect scope result).tree a) ∨
    OptionLetReadAt result scope false spelling input tree rest := by
  generalize htok : (letKeyword :: .word spelling :: colon :: input) = toks at read
  cases read with
  | bindDirect name ordinary written valid typeRead callRead =>
      cases callRead
      rename_i call args argsProof
      injection htok with _ htail
      injection htail with hspelling htail
      injection htail with _ htail
      injection hspelling with hname
      subst input
      refine Or.inl ⟨⟨name, ordinary, written, valid, call⟩, _, ?_, typeRead, .applied call argsProof, rfl⟩
      exact hname.symm
  | letOption mutable name ordinary carrier resolved typeRead initializerRead =>
    cases mutable <;> simp only [optionLetHead, letKeyword, keyword, colon,
      Bool.false_eq_true, if_false, if_true, List.nil_append, List.cons_append,
      List.cons.injEq, Token.word.injEq, true_and] at htok
  · obtain ⟨spellingEq, rfl⟩ := htok
    exact Or.inr ⟨name, carrier, _, ordinary, resolved, _, _, spellingEq.symm,
      typeRead, initializerRead, rfl⟩
  · exact False.elim (by cases htok.2)
  | directCall callRead =>
      cases callRead
      all_goals simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]
  | letBinding _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | assignVar _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | ret _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | ite _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | retVoid _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | letMutable _ _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | whileBounded _ _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | forRange _ _ _ _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]

-- Mirror StmtReads.ite_inversion and retain the distinct bound and body derivations.
theorem StmtReads.boundedWhile_inversion
    (read : StmtReads result scope (keyword "while" :: input) tree rest) :
    (∃ (a : Surface.BoundedWhileArgs scope result) (boundInput bodyInput : List Token),
      ExprReads scope 0 input a.condition (keyword "bounded" :: boundInput) ∧
      ExprReads scope 0 boundInput a.bound
        (keyword "ops" :: keyword "on_exceeded" :: .word a.overflow.val :: bodyInput) ∧
      BlockReads result scope bodyInput a.body rest ∧
      tree = (Surface.boundedWhile scope result).tree a) ∨
    (∃ tail, input = assignment :: tail) := by
  generalize htok : (keyword "while" :: input) = toks at read
  cases read with
  | whileBounded nonnegative overflow bound staticBound condRead boundRead blockRead =>
      injection htok with _ hinput
      subst input
      refine Or.inl ⟨⟨_, _, _, bound, staticBound, nonnegative, overflow, _⟩, _, _, condRead, boundRead, blockRead, rfl⟩
  | assignVar _ _ _ _ _ =>
      injection htok with _ htail
      exact Or.inr ⟨_, htail⟩
  | directCall callRead =>
      cases callRead
      rename_i call args argsProof
      injection htok with hhead htail
      exact (call.ordinary.2 (by injection hhead with hval; simpa [hval])).elim
  | letBinding _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | ret _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | ite _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | retVoid _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | letMutable _ _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | bindDirect _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | forRange _ _ _ _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]

-- Mirror StmtReads.boundedWhile_inversion, using the distinct range separator.
theorem StmtReads.forRange_inversion
    (read : StmtReads result scope (keyword "for" :: .word spelling :: keyword "in" :: input) tree rest) :
    ∃ (a : Surface.ForRangeArgs scope result) (highInput handlerInput bodyInput : List Token),
      a.name.val = spelling ∧ ExprReads scope 0 input a.lower (openRange :: highInput) ∧
      ExprReads scope 0 highInput a.upper handlerInput ∧
      OverflowReads handlerInput a.overflow bodyInput ∧
      BlockReads result (rangeBinding a.name a.lo a.hi :: scope) bodyInput a.body rest ∧
      tree = (Surface.forRange scope result).tree a := by
  generalize htok : (keyword "for" :: .word spelling :: keyword "in" :: input) = toks at read
  cases read with
  | forRange name ordinary body lo hi staticBounds lowerRead upperRead ovRead blockRead =>
      simp only [List.cons.injEq, and_true, true_and] at htok
      obtain ⟨hspelling, hinput⟩ := htok
      injection hspelling with hname
      subst input
      refine ⟨⟨name, ordinary, _, _, _, _, lo, hi, staticBounds, _, body⟩,
        _, _, _, ?_, lowerRead, upperRead, ovRead, blockRead, rfl⟩
      exact hname.symm
  | directCall callRead =>
      cases callRead
      rename_i call args argsProof
      injection htok with hhead htail
      injection htail with hspelling hargs
      cases hspelling
  | letBinding _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | assignVar _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | ret _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | ite _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | retVoid _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | letMutable _ _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | bindDirect _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]   | whileBounded _ _ _ _ _ _ _ => simp_all [returnKeyword, letKeyword, ifKeyword, keyword, assignment, semicolon, colon, openParen, directName]

-- Mirror UnitBody.printReads and recover the first declaration's unconsumed suffix.
theorem UnitReads.program_inversion (a : Surface.ProgramArgs) (read : UnitReads [] tokens a.unit) :
    ∃ rest, DeclReads [] tokens ⟨a.middle, a.first⟩ rest ∧
      UnitReads a.middle rest ⟨a.after, a.rest⟩ := by
  cases a with
  | mk middle after first rest =>
    cases read with | step firstDecl nextRead => exact ⟨_, firstDecl, nextRead⟩

end Gabbro.Core.Ast
