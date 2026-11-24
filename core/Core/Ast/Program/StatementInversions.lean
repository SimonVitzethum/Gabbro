module

public import Core.Ast.Program.StatementGrammar

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

/-- The continuation after the common binding header and initializer. A new
    continuation starts at its own discriminator, such as the word `else`. -/
-- The assignment tokens remain distinguishable after a contextual keyword head.
def AssignmentStart (input : List Token) : Prop :=
  (∃ tail, input = assignment :: tail) ∨
    (∃ field tail, input = dot :: .word field :: assignment :: tail)

theorem StmtReads.let_header
    (read : StmtReads result scope (letKeyword :: .word spelling :: assignment :: input) tree rest) :
    ∃ (name : Identifier) (ordinary : name.val ≠ "mut".toList) (type : Ty .value)
      (value : Expr scope type) (more : List Token),
      name.val = spelling ∧ ExprReads scope 0 input value more ∧
      LetTailReads result scope name ordinary value more tree rest := by
  generalize same : (letKeyword :: Token.word spelling :: assignment :: input) = tokens at read
  cases read with
  | letBinding name ordinary valueRead tail =>
    have pre := (List.cons.inj same).2
    have spellingEq := Token.word.inj (List.cons.inj pre).1
    cases (List.cons.inj (List.cons.inj pre).2).2
    exact ⟨name, ordinary, _, _, _, spellingEq.symm, valueRead, tail⟩
  | tupleBind _ patternRead _ _ =>
    cases patternRead
    cases (List.cons.inj (List.cons.inj same).2).1
  | directCall callRead =>
    cases callRead
    cases (List.cons.inj (List.cons.inj same).2).1
  | letOption mutable _ _ _ _ _ _ =>
    cases mutable
    all_goals cases (List.cons.inj (List.cons.inj (List.cons.inj same).2).2).1
  | letMutable _ _ _ _ _ _ _ =>
    cases (List.cons.inj (List.cons.inj (List.cons.inj same).2).2).1
  | letMutableValue _ _ _ =>
    cases (List.cons.inj (List.cons.inj (List.cons.inj same).2).2).1
  | bindDirect _ _ _ _ _ _ =>
    cases (List.cons.inj (List.cons.inj (List.cons.inj same).2).2).1
  | assignVar _ _ _ _ _ =>
    cases (List.cons.inj (List.cons.inj same).2).1
  | assignField _ _ _ _ _ _ _ _ =>
    cases (List.cons.inj (List.cons.inj same).2).1
  | _ => cases (List.cons.inj same).1

theorem AtomReads.not_assignment (read : AtomReads scope (assignment :: input) tree rest) : False := by
  cases read

theorem ExprReads.not_assignment (read : ExprReads scope minimum (assignment :: input) tree rest) : False := by
  cases read with
  | atom atomRead _ => exact atomRead.not_assignment

theorem StmtReads.assign_inversion
    (read : StmtReads result scope (.word name :: assignment :: input) tree rest) :
    ∃ (lo hi valueLo valueHi : Int) (ref : Local scope (.int lo hi)) (visible : ref.visible)
      (writable : ref.binding.mutable = true) (value : Expr scope (.int valueLo valueHi))
      (fits : Fits (.int valueLo valueHi) (.int lo hi)),
      ref.binding.name.val = name ∧ ExprReads scope 0 input value (semicolon :: rest) ∧
      tree = ⟨scope, .assignVar ref visible writable value fits⟩ := by
  generalize same : (Token.word name :: assignment :: input) = tokens at read
  cases read with
  | assignVar ref visible writable fits valueRead =>
    have spellingEq := Token.word.inj (List.cons.inj same).1
    cases (List.cons.inj (List.cons.inj same).2).2
    exact ⟨_, _, _, _, ref, visible, writable, _, fits, spellingEq.symm, valueRead, rfl⟩
  | ret _ _ valueRead =>
    rw [← (List.cons.inj same).2] at valueRead
    exact valueRead.not_assignment.elim
  | ite condRead _ _ =>
    rw [← (List.cons.inj same).2] at condRead
    exact condRead.not_assignment.elim
  | whileBounded _ _ _ _ condRead _ _ =>
    rw [← (List.cons.inj same).2] at condRead
    exact condRead.not_assignment.elim
  | variantMatch valueRead _ =>
    rw [← (List.cons.inj same).2] at valueRead
    exact valueRead.not_assignment.elim
  | retOption _ valueRead =>
    rw [← (List.cons.inj same).2] at valueRead
    cases valueRead
  | tupleBind _ patternRead _ _ =>
    rw [← (List.cons.inj same).2] at patternRead
    cases patternRead
  | directCall callRead =>
    cases callRead
    cases (List.cons.inj (List.cons.inj same).2).1
  | letOption mutable _ _ _ _ _ _ =>
    cases mutable
    all_goals cases (List.cons.inj (List.cons.inj same).2).1
  | _ => cases (List.cons.inj (List.cons.inj same).2).1

theorem StmtReads.ret_inversion
    (read : StmtReads (some expected) scope (returnKeyword :: input) tree rest) :
    (∃ (t : Ty .value) (value : Expr scope t) (fits : Fits t expected),
      ExprReads scope 0 input value (semicolon :: rest) ∧ tree = ⟨scope, .ret rfl value fits⟩) ∨
    (∃ (count : Nat) (declared : some expected = some (indexOptionType count)) (value : OptionInitializer scope count),
      OptionInitializerReads scope count input value (semicolon :: rest) ∧
      tree = ⟨scope, .retOption declared value⟩) ∨ AssignmentStart input := by
  generalize same : (returnKeyword :: input) = tokens at read
  cases read with
  | ret declared fits valueRead =>
    cases declared
    cases (List.cons.inj same).2
    exact .inl ⟨_, _, fits, valueRead, rfl⟩
  | retOption declared valueRead =>
    cases (List.cons.inj same).2
    exact .inr (.inl ⟨_, declared, _, valueRead, rfl⟩)
  | retVoid declared => cases declared
  | assignVar _ _ _ _ _ =>
    exact .inr (.inr (.inl ⟨_, (List.cons.inj same).2⟩))
  | assignField _ _ _ _ _ _ _ _ =>
    exact .inr (.inr (.inr ⟨_, _, (List.cons.inj same).2⟩))
  | directCall callRead =>
    cases callRead
    rename_i call _ _
    have reserved := Token.word.inj (List.cons.inj same).1
    exact (call.ordinary.2 (List.mem_map.mpr ⟨"return", by decide, reserved⟩)).elim
  | letOption mutable _ _ _ _ _ _ =>
    cases mutable
    all_goals cases (List.cons.inj same).1
  | _ => cases (List.cons.inj same).1

theorem StmtReads.ite_inversion
    (read : StmtReads result scope (ifKeyword :: input) tree rest) :
    (∃ (condition : Expr scope .bool) (first : List Token) (yes : BracedBlock result scope)
      (more : List Token) (no : BracedBlock result scope),
      ExprReads scope 0 input condition first ∧ BlockReads result scope first yes (elseKeyword :: more) ∧
      BlockReads result scope more no rest ∧ tree = ⟨scope, .ite condition yes no⟩) ∨ AssignmentStart input := by
  generalize same : (ifKeyword :: input) = tokens at read
  cases read with
  | ite condRead yesRead noRead =>
    cases (List.cons.inj same).2
    exact .inl ⟨_, _, _, _, _, condRead, yesRead, noRead, rfl⟩
  | assignVar _ _ _ _ _ =>
    exact .inr (.inl ⟨_, (List.cons.inj same).2⟩)
  | assignField _ _ _ _ _ _ _ _ =>
    exact .inr (.inr ⟨_, _, (List.cons.inj same).2⟩)
  | directCall callRead =>
    cases callRead
    rename_i call _ _
    have reserved := Token.word.inj (List.cons.inj same).1
    exact (call.ordinary.2 (List.mem_map.mpr ⟨"if", by decide, reserved⟩)).elim
  | letOption mutable _ _ _ _ _ _ =>
    cases mutable
    all_goals cases (List.cons.inj same).1
  | _ => cases (List.cons.inj same).1

theorem BlockReads.braced_inversion
    (read : BlockReads result scope (openBrace :: input) tree rest) :
    ∃ (after : Scope) (body : Block result scope after),
      tree = .braces body ∧ BlockItems result scope input ⟨after, body⟩ rest := by
  cases read
  rename_i after body read
  exact ⟨after, body, rfl, read⟩

theorem StmtReads.disjoint_closeBrace : ¬ StmtReads result scope (closeBrace :: input) tree rest := by
  intro read
  generalize h : (closeBrace :: input) = tokens at read
  cases read with
  | directCall callRead => cases callRead; cases (List.cons.inj h).1
  | letOption mutable _ _ _ _ _ _ =>
    cases mutable
    all_goals cases (List.cons.inj h).1
  | _ => cases (List.cons.inj h).1

end Gabbro.Core.Ast
