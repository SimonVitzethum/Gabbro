module

public import Core.Ast.Expression

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

/-- The ordinary immutable, unannotated binding production. The common `let`
    header leaves the continuation token after the initializer to distinguish
    the plain statement from its fallible variants. -/
inductive StmtReads (scope : Scope) : List Token → Statement scope → List Token → Prop where
  | letValue (name : Identifier) (ordinary : name.val ≠ "mut".toList) :
      ExprReads scope 0 input value (semicolon :: rest) →
      StmtReads scope (letKeyword :: .word name.val :: assignment :: input)
        ⟨_, .letValue name ordinary value⟩ rest

theorem StmtReads.let_inversion
    (read : StmtReads scope (letKeyword :: .word spelling :: assignment :: input) tree rest) :
    ∃ (name : Identifier) (ordinary : name.val ≠ "mut".toList) (value : Expr scope .integer),
      name.val = spelling ∧ tree = ⟨_, .letValue name ordinary value⟩ ∧
      ExprReads scope 0 input value (semicolon :: rest) := by
  cases read with
  | letValue name ordinary initializer => exact ⟨name, ordinary, _, rfl, rfl, initializer⟩

theorem StmtReads.deterministic (left : StmtReads scope input a rest)
    (right : StmtReads scope input b rest') : a = b ∧ rest = rest' := by
  cases left with
  | letValue name ordinary initializer =>
    obtain ⟨name', ordinary', _, sameName, rfl, initializer'⟩ := right.let_inversion
    have same : name' = name := Subtype.ext sameName
    subst name'
    obtain ⟨rfl, suffix⟩ := initializer.deterministic initializer'
    exact ⟨rfl, (List.cons.inj suffix).2⟩

theorem StmtReads.disjoint_closeBrace : ¬ StmtReads scope (closeBrace :: input) tree rest := by
  intro read
  cases read

theorem StmtReads.consumes (read : StmtReads scope input tree rest) : rest <:+ input := by
  cases read with
  | letValue name _ initializer =>
    exact ((List.suffix_cons semicolon _).trans initializer.consumes).trans
      (List.suffix_append [letKeyword, .word name.val, assignment] _)

end Gabbro.Core.Ast
