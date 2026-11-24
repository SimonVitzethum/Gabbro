module

public import Core.Ast.Program.StatementInversions

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

theorem ExprReads.not_dot (read : ExprReads scope minimum (dot :: input) tree rest) : False := by
  cases read with
  | atom atomRead _ => cases atomRead

theorem ExprReads.not_closeBrace (read : ExprReads scope minimum (closeBrace :: input) tree rest) : False := by
  cases read with
  | atom atomRead _ => cases atomRead

theorem ExprReads.not_assignmentStart (read : ExprReads scope minimum input tree rest)
    (assigning : AssignmentStart input) : False := by
  rcases assigning with ⟨_, rfl⟩ | ⟨_, _, rfl⟩
  · exact read.not_assignment
  · exact read.not_dot

private theorem ordinaryAtomWord.not_option (ordinary : ordinaryAtomWord spelling)
    (optionWord : spelling = indexSomeName.val ∨ spelling = indexNoneName.val) : False := by
  rcases optionWord with h | h
  · exact ordinary.2.2.2.1 h
  · exact ordinary.2.2.2.2 h

private theorem AtomReads.not_optionWord
    (optionWord : spelling = indexSomeName.val ∨ spelling = indexNoneName.val)
    (read : AtomReads scope (.word spelling :: input) tree rest) : False := by
  generalize head : Token.word spelling = token at read
  cases read with
  | «variable» ref _ ordinary =>
    exact ordinaryAtomWord.not_option ordinary (by simpa only [Token.word.inj head] using optionWord)
  | recordValue ref _ _ _ =>
    exact ordinaryAtomWord.not_option ref.ordinary (by simpa only [Token.word.inj head] using optionWord)
  | variantValue _ label _ _ ordinary _ _ _ =>
    exact ordinaryAtomWord.not_option ordinary (by simpa only [Token.word.inj head] using optionWord)
  | trueLit =>
    rcases optionWord with h | h <;> rw [h] at head <;> cases head
  | falseLit =>
    rcases optionWord with h | h <;> rw [h] at head <;> cases head
  | textLength _ =>
    rcases optionWord with h | h <;> rw [h] at head <;> cases head
  | _ => cases head

theorem OptionInitializerReads.disjointExpr
    (read : OptionInitializerReads scope count input value rest)
    (exprRead : ExprReads scope minimum input tree suffix) : False := by
  cases exprRead with
  | atom atomRead _ =>
    cases read with
    | absent => exact atomRead.not_optionWord (.inr rfl)
    | present _ _ => exact atomRead.not_optionWord (.inl rfl)

theorem OptionInitializerReads.disjointCall
    (read : OptionInitializerReads scope count input value rest)
    (callRead : CallReads scope input call suffix) : False := by
  cases callRead with
  | applied callee argsRead =>
    generalize head : Token.word callee.name.val = token at read
    cases read with
    | absent => exact ordinaryAtomWord.not_option callee.ordinary.1 (.inr (Token.word.inj head))
    | present _ _ => exact ordinaryAtomWord.not_option callee.ordinary.1 (.inl (Token.word.inj head))

theorem OptionInitializerReads.deterministic
    (left : OptionInitializerReads scope count input a rest)
    (right : OptionInitializerReads scope count input b suffix) : a = b ∧ rest = suffix := by
  cases left with
  | absent =>
    cases right with
    | absent => exact ⟨rfl, rfl⟩
  | present fits valueRead =>
    cases right with
    | present otherFits otherRead =>
      obtain ⟨same, tail⟩ := valueRead.deterministic otherRead
      cases same
      exact ⟨rfl, (List.cons.inj tail).2⟩

theorem OverflowReads.deterministic (left : OverflowReads input a rest)
    (right : OverflowReads input b suffix) : a = b ∧ rest = suffix := by
  cases left with
  | absent closed =>
    cases right with
    | absent => exact ⟨rfl, rfl⟩
    | named name => exact (closed _ rfl).elim
  | named name =>
    generalize h : name.val = spelling at right
    cases right with
    | absent closed => exact (closed _ rfl).elim
    | named other =>
      cases Subtype.ext h
      exact ⟨rfl, rfl⟩

end Gabbro.Core.Ast
