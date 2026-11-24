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

end Gabbro.Core.Ast
