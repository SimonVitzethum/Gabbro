module

public import Core.Ast.Program.StatementGrammar

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

theorem PatternNameReads.consumes (read : PatternNameReads input name rest) : rest <:+ input := by
  cases read <;> exact List.suffix_cons _ _

theorem PatternTailReads.consumes (read : PatternTailReads input names rest) : rest <:+ input := by
  induction read with
  | close => exact List.suffix_cons _ _
  | next head _ suffix =>
    exact (suffix.trans head.consumes).trans (List.suffix_cons _ _)

theorem TuplePatternReads.consumes (read : TuplePatternReads input pattern rest) : rest <:+ input := by
  cases read with
  | tuple first second tail =>
    exact (tail.consumes.trans (second.consumes.trans
      ((List.suffix_cons _ _).trans first.consumes))).trans (List.suffix_cons _ _)

theorem TupleAnnotationReads.consumes (read : TupleAnnotationReads scope input annotation rest) :
    rest <:+ input := by
  cases read with
  | absent => exact List.suffix_cons _ _
  | written typeRead =>
    exact ((List.suffix_cons _ _).trans typeRead.consumes).trans (List.suffix_cons _ _)

theorem OverflowReads.consumes (read : OverflowReads input handler rest) : rest <:+ input := by
  cases read with
  | absent _ => exact List.suffix_refl _
  | named _ => exact (List.suffix_cons _ _).trans (List.suffix_cons _ _)

theorem OptionInitializerReads.consumes
    (read : OptionInitializerReads scope count input value rest) : rest <:+ input := by
  cases read with
  | absent => exact List.suffix_cons _ _
  | present _ body =>
    exact (((List.suffix_cons _ _).trans body.consumes).trans (List.suffix_cons _ _)).trans
      (List.suffix_cons _ _)

local macro "statement_suffix" recursor:ident read:term : tactic =>
  `(tactic|
    refine $recursor
      (motive_1 := fun _ input _ rest _ => rest <:+ input)
      (motive_2 := fun _ input _ rest _ => rest <:+ input)
      (motive_3 := fun _ input _ rest _ => rest <:+ input)
      (motive_4 := fun _ _ input _ _ _ rest _ => rest <:+ input)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ $read <;>
    (intros
     repeat first
     | assumption
     | apply List.suffix_rfl
     | apply List.suffix_cons
     | apply List.IsSuffix.trans ?_ (by assumption)
     | apply List.IsSuffix.trans ?_ (ExprReads.consumes (by assumption))
     | apply List.IsSuffix.trans ?_ (TypeReads.consumes (by assumption))
     | apply List.IsSuffix.trans ?_ (CallReads.consumes (by assumption))
     | apply List.IsSuffix.trans ?_ (LetTailReads.consumes (by assumption))
     | apply List.IsSuffix.trans ?_ (OverflowReads.consumes (by assumption))
     | apply List.IsSuffix.trans ?_ (TuplePatternReads.consumes (by assumption))
     | apply List.IsSuffix.trans ?_ (TupleAnnotationReads.consumes (by assumption))
     | apply List.IsSuffix.trans ?_ (OptionInitializerReads.consumes (by assumption))
     | apply List.IsSuffix.trans ?_ (List.suffix_append (optionLetHead _ _) _)
     | apply List.IsSuffix.trans ?_ (List.suffix_cons _ _)))

theorem StmtReads.consumes (read : StmtReads result scope input tree rest) : rest <:+ input := by
  statement_suffix StmtReads.rec read

theorem BlockItems.consumes (read : BlockItems result scope input tree rest) : rest <:+ input := by
  statement_suffix BlockItems.rec read

theorem BlockReads.consumes (read : BlockReads result scope input tree rest) : rest <:+ input := by
  statement_suffix BlockReads.rec read

end Gabbro.Core.Ast
