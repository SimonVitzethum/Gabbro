module

public import Core.Ast.Expression

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text


-- Mirror AtomReads.lit_inversion at the shared arithmetic tail constructor.
theorem ExprTail.arith_inversion (allowed : minimum ≤ op.precedence)
    (read : ExprTail scope minimum (left : Expr scope (.int lo₁ hi₁)) (op.token :: input) tree rest) :
    ∃ (lo₂ hi₂ : Int) (right : Expr scope (.int lo₂ hi₂)) (more : List Token),
      ExprReads scope (op.precedence + 1) input right more ∧
      ExprTail scope minimum (.binary op left right) more tree rest := by
  generalize h : op.token = token at read
  cases read with
  | stop blocked =>
      exfalso
      exact blocked ⟨.arith op, input, by simpa only [Infix.token] using congrArg (· :: input) h.symm, allowed⟩
  | binary op' _ rightRead tail =>
      have eq : op = op' := Arith.token_injective h
      cases eq
      exact ⟨_, _, _, _, rightRead, tail⟩
  | div _ rightRead _ tail =>
      have eq := Infix.token_injective (a := .arith op) (b := .div) h
      cases eq
  | compare op' _ rightRead _ tail =>
      have eq := Infix.token_injective (a := .arith op) (b := .compare op') h
      cases eq

-- Mirror ExprTail.arith_inversion and recover the divisor-range evidence.
theorem ExprTail.div_inversion (allowed : minimum ≤ Infix.div.precedence)
    (read : ExprTail scope minimum (left : Expr scope (.int lo₁ hi₁)) (Infix.div.token :: input) tree rest) :
    ∃ (lo₂ hi₂ : Int) (right : Expr scope (.int lo₂ hi₂)) (more : List Token) (nonzero : Divisor lo₂ hi₂),
      ExprReads scope (Infix.div.precedence + 1) input right more ∧
      ExprTail scope minimum (.div left right nonzero) more tree rest := by
  generalize h : Infix.token .div = token at read
  cases read with
  | stop blocked =>
      exfalso
      exact blocked ⟨.div, input, congrArg (· :: input) h.symm, allowed⟩
  | binary op' _ rightRead tail =>
      have eq := Infix.token_injective (a := .div) (b := .arith op') h
      cases eq
  | div _ rightRead _ tail' =>
      exact ⟨_, _, _, _, _, rightRead, tail'⟩
  | compare op' _ rightRead _ tail =>
      have eq := Infix.token_injective (a := .div) (b := .compare op') h
      cases eq

-- Mirror ExprTail.arith_inversion and recover the guard against an ungrouped comparison.
theorem ExprTail.compare_inversion (allowed : minimum ≤ (Infix.compare op).precedence)
    (read : ExprTail scope minimum (left : Expr scope (.int lo₁ hi₁))
      ((Infix.compare op).token :: input) tree rest) :
    ∃ (lo₂ hi₂ : Int) (right : Expr scope (.int lo₂ hi₂)) (more : List Token),
      ExprReads scope ((Infix.compare op).precedence + 1) input right more ∧
      (Infix.compare op).follows more ∧ ExprTail scope minimum (.compare op left right) more tree rest := by
  generalize h : Infix.token (.compare op) = token at read
  cases read with
  | stop blocked =>
      exfalso
      exact blocked ⟨.compare op, input, congrArg (· :: input) h.symm, allowed⟩
  | binary op' _ rightRead tail =>
      have eq := Infix.token_injective (a := .compare op) (b := .arith op') h
      cases eq
  | div _ rightRead _ tail =>
      have eq := Infix.token_injective (a := .compare op) (b := .div) h
      cases eq
  | compare op' _ rightRead follows tail' =>
      have eq := Infix.token_injective (a := .compare op) (b := .compare op') h
      cases eq
      exact ⟨_, _, _, _, rightRead, follows, tail'⟩

-- Mirror ExprTail.arith_inversion keeping both operands at Boolean type.
theorem ExprTail.logic_inversion (allowed : minimum ≤ (Infix.logic op).precedence)
    (read : ExprTail scope minimum (left : Expr scope .bool)
      ((Infix.logic op).token :: input) tree rest) :
    ∃ (right : Expr scope .bool) (more : List Token),
      ExprReads scope ((Infix.logic op).precedence + 1) input right more ∧
      ExprTail scope minimum (.logic op left right) more tree rest := by
  generalize h : Infix.token (.logic op) = token at read
  cases read with
  | stop blocked =>
      exfalso
      exact blocked ⟨.logic op, input, congrArg (· :: input) h.symm, allowed⟩
  | logic op' _ rightRead tail' =>
      have eq := Infix.token_injective (a := .logic op) (b := .logic op') h
      cases eq
      exact ⟨_, _, rightRead, tail'⟩

-- Mirror ExprReads.consumes with the atom motive of the mutual recursor.
theorem AtomReads.consumes (read : AtomReads scope input tree rest) : rest <:+ input := by
  refine AtomReads.rec
    (motive_1 := fun _ input _ _ rest _ => rest <:+ input)
    (motive_2 := fun input _ _ rest _ => rest <:+ input)
    (motive_3 := fun _ _ _ input _ _ rest _ => rest <:+ input)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ read
  · intro _ _ _ _ _ _ _ _ _ _ atom tail
    exact tail.trans atom
  · intro _ _
    exact List.suffix_cons _ _
  · intro input _ _ rest _ child
    exact ((List.suffix_cons closeParen rest).trans child).trans (List.suffix_cons openParen input)
  · intro _
    exact List.suffix_cons _ _
  · intro _
    exact List.suffix_cons _ _
  · intro _ _ _ _ _
    exact List.suffix_cons _ _
  · intro _ _
    exact (List.suffix_cons _ _).trans (List.suffix_cons _ _)
  · intro _ _ _ _ _ start child ihChild
    exact ihChild.trans (List.suffix_cons _ _)
  · intro _ _ _ _ _ ihChild
    exact ihChild.trans (List.suffix_cons _ _)
  · intro _ rest _ _ _
    exact List.suffix_refl rest
  · intro _ input _ _ _ _ _ _ _ _ _ _ op _ _ _ operand tail
    exact (tail.trans operand).trans (List.suffix_cons _ _)
  · intro _ input _ _ _ _ _ _ _ _ _ _ _ _ _ _ operand tail
    exact (tail.trans operand).trans (List.suffix_cons _ _)
  · intro _ input _ _ _ _ _ _ _ _ _ _ op _ _ _ _ operand tail
    exact (tail.trans operand).trans (List.suffix_cons _ _)
  · intro _ _ _ _ _ _ _ _ op _ _ _ operand tail
    exact (tail.trans operand).trans (List.suffix_cons _ _)

-- Mirror ExprReads.consumes with the tail motive of the mutual recursor.
theorem ExprTail.consumes (read : ExprTail scope minimum first input tree rest) : rest <:+ input := by
  refine ExprTail.rec
    (motive_1 := fun _ input _ _ rest _ => rest <:+ input)
    (motive_2 := fun input _ _ rest _ => rest <:+ input)
    (motive_3 := fun _ _ _ input _ _ rest _ => rest <:+ input)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ read
  · intro _ _ _ _ _ _ _ _ _ _ atom tail
    exact tail.trans atom
  · intro _ _
    exact List.suffix_cons _ _
  · intro input _ _ rest _ child
    exact ((List.suffix_cons closeParen rest).trans child).trans (List.suffix_cons openParen input)
  · intro _
    exact List.suffix_cons _ _
  · intro _
    exact List.suffix_cons _ _
  · intro _ _ _ _ _
    exact List.suffix_cons _ _
  · intro _ _
    exact (List.suffix_cons _ _).trans (List.suffix_cons _ _)
  · intro _ _ _ _ _ start child ihChild
    exact ihChild.trans (List.suffix_cons _ _)
  · intro _ _ _ _ _ ihChild
    exact ihChild.trans (List.suffix_cons _ _)
  · intro _ rest _ _ _
    exact List.suffix_refl rest
  · intro _ input _ _ _ _ _ _ _ _ _ _ op _ _ _ operand tail
    exact (tail.trans operand).trans (List.suffix_cons _ _)
  · intro _ input _ _ _ _ _ _ _ _ _ _ _ _ _ _ operand tail
    exact (tail.trans operand).trans (List.suffix_cons _ _)
  · intro _ input _ _ _ _ _ _ _ _ _ _ op _ _ _ _ operand tail
    exact (tail.trans operand).trans (List.suffix_cons _ _)
  · intro _ _ _ _ _ _ _ _ op _ _ _ operand tail
    exact (tail.trans operand).trans (List.suffix_cons _ _)

end Gabbro.Core.Ast


end Gabbro.Core.Ast
