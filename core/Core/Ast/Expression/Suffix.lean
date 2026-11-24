module

public import Core.Ast.Expression.Grammar

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

local macro "expression_suffix" recursor:ident read:term : tactic =>
  `(tactic|
    refine $recursor
      (motive_1 := fun _ input _ _ rest _ => rest <:+ input)
      (motive_2 := fun input _ _ rest _ => rest <:+ input)
      (motive_3 := fun _ _ _ input _ _ rest _ => rest <:+ input)
      (motive_4 := fun _ input _ _ rest _ => rest <:+ input)
      (motive_5 := fun _ input _ _ rest _ => rest <:+ input)
      (motive_6 := fun input _ _ _ rest _ => rest <:+ input)
      (motive_7 := fun input _ _ _ rest _ => rest <:+ input)
      (motive_8 := fun input _ _ rest _ => rest <:+ input)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ $read <;>
    (intros
     repeat first
     | assumption
     | apply List.suffix_rfl
     | apply List.suffix_cons
     | apply List.IsSuffix.trans ?_ (by assumption)
     | apply List.IsSuffix.trans (l₂ := _) ?_ (List.suffix_cons _ _)))

theorem ExprReads.consumes (read : ExprReads scope minimum input tree rest) : rest <:+ input := by
  expression_suffix ExprReads.rec read

theorem AtomReads.consumes (read : AtomReads scope input tree rest) : rest <:+ input := by
  expression_suffix AtomReads.rec read

theorem ExprTail.consumes (read : ExprTail scope minimum first input tree rest) : rest <:+ input := by
  expression_suffix ExprTail.rec read

theorem LabeledItemsRead.consumes (read : LabeledItemsRead scope input items rest) : rest <:+ input := by
  expression_suffix LabeledItemsRead.rec read

/-- Extend the outer operator sequence at a lower precedence, preserving every operand read. -/
theorem ExprTail.follow (derivation : ExprTail scope minimum first input tree rest) :
    ∀ {lower resultType} {result : Expr scope resultType} {final}, lower ≤ minimum →
      ExprTail scope lower tree rest result final → ExprTail scope lower first input result final := by
  refine ExprTail.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun minimum _ first input _ tree rest _ =>
      ∀ {lower resultType} {result : Expr scope resultType} {final}, lower ≤ minimum →
        ExprTail scope lower tree rest result final → ExprTail scope lower first input result final)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ => True)
    ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?stop ?binary ?div ?compare ?logic ?arrayIndex ?tupleField ?recordField
    ?textConcat ?textIndex ?substring ?optionIsSome
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ derivation
  case stop =>
    intros
    assumption
  case binary =>
    intros
    rename_i op allowed operand _ _ ih _ _ _ _ lower next
    exact .binary op (Nat.le_trans lower allowed) operand (ih lower next)
  case div =>
    intros
    rename_i allowed operand nonzero _ _ ih _ _ _ _ lower next
    exact .div (Nat.le_trans lower allowed) operand nonzero (ih lower next)
  case compare =>
    intros
    rename_i op allowed operand follows _ _ ih _ _ _ _ lower next
    exact .compare op (Nat.le_trans lower allowed) operand follows (ih lower next)
  case logic =>
    intros
    rename_i op allowed operand _ _ ih _ _ _ _ lower next
    exact .logic op (Nat.le_trans lower allowed) operand (ih lower next)
  case arrayIndex =>
    intros
    rename_i base bounded below allowed operand _ _ ih _ _ _ _ lower next
    exact .arrayIndex base bounded below (Nat.le_trans lower allowed) operand (ih lower next)
  case tupleField =>
    intros
    rename_i base index allowed _ ih _ _ _ _ lower next
    exact .tupleField base index (Nat.le_trans lower allowed) (ih lower next)
  case recordField =>
    intros
    rename_i base field index written allowed _ ih _ _ _ _ lower next
    exact .recordField base field index written (Nat.le_trans lower allowed) (ih lower next)
  case textConcat =>
    intros
    rename_i left right allowed operand _ _ ih _ _ _ _ lower next
    exact .textConcat left right (Nat.le_trans lower allowed) operand (ih lower next)
  case textIndex =>
    intros
    rename_i base offset allowed operand _ _ ih _ _ _ _ lower next
    exact .textIndex base offset (Nat.le_trans lower allowed) operand (ih lower next)
  case substring =>
    intros
    rename_i base lo hi allowed first last _ _ _ ih _ _ _ _ lower next
    exact .substring base lo hi (Nat.le_trans lower allowed) first last (ih lower next)
  case optionIsSome =>
    intros
    rename_i ref visible ordinary allowed _ ih _ _ _ _ lower next
    exact .optionIsSome ref visible ordinary (Nat.le_trans lower allowed) (ih lower next)
  all_goals intros; exact True.intro


end Gabbro.Core.Ast
