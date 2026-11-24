module

public import Core.Ast.Expression

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

/-- The continuation after the common binding header and initializer. A new
    continuation starts at its own discriminator, such as the word `else`. -/
inductive LetTailReads (scope : Scope) (name : Identifier) (ordinary : name.val ≠ "mut".toList)
    (value : Expr scope .integer) : List Token → Statement scope → List Token → Prop where
  | plain : LetTailReads scope name ordinary value (semicolon :: rest)
      ⟨_, .letValue name ordinary value⟩ rest

theorem LetTailReads.plain_inversion
    (read : LetTailReads scope name ordinary value (semicolon :: rest) tree suffix) :
    tree = ⟨_, .letValue name ordinary value⟩ ∧ suffix = rest := by
  cases read
  exact ⟨rfl, rfl⟩

theorem LetTailReads.deterministic (left : LetTailReads scope name ordinary value input a rest)
    (right : LetTailReads scope name ordinary value input b rest') : a = b ∧ rest = rest' := by
  cases left
  obtain ⟨rfl, rfl⟩ := right.plain_inversion
  exact ⟨rfl, rfl⟩

theorem LetTailReads.consumes (read : LetTailReads scope name ordinary value input tree rest) :
    rest <:+ input := by
  cases read
  exact List.suffix_cons _ _

/-- Shared header for bindings. The initializer determines the position of
    the continuation and is read in the original scope. -/
inductive StmtReads (scope : Scope) : List Token → Statement scope → List Token → Prop where
  | letBinding (name : Identifier) (ordinary : name.val ≠ "mut".toList) :
      ExprReads scope 0 input value more →
      LetTailReads scope name ordinary value more tree rest →
      StmtReads scope (letKeyword :: .word name.val :: assignment :: input) tree rest

theorem StmtReads.let_header
    (read : StmtReads scope (letKeyword :: .word spelling :: assignment :: input) tree rest) :
    ∃ (name : Identifier) (ordinary : name.val ≠ "mut".toList) (value : Expr scope .integer) (more : List Token),
      name.val = spelling ∧ ExprReads scope 0 input value more ∧
      LetTailReads scope name ordinary value more tree rest := by
  cases read with
  | letBinding name ordinary initializer tail => exact ⟨name, ordinary, _, _, rfl, initializer, tail⟩

theorem StmtReads.deterministic (left : StmtReads scope input a rest)
    (right : StmtReads scope input b rest') : a = b ∧ rest = rest' := by
  cases left with
  | letBinding name ordinary initializer tail =>
    obtain ⟨name', ordinary', _, _, sameName, initializer', tail'⟩ := right.let_header
    have same : name' = name := Subtype.ext sameName
    subst name'
    obtain ⟨rfl, rfl⟩ := initializer.deterministic initializer'
    exact tail.deterministic tail'

theorem StmtReads.disjoint_closeBrace : ¬ StmtReads scope (closeBrace :: input) tree rest := by
  intro read
  cases read

theorem StmtReads.consumes (read : StmtReads scope input tree rest) : rest <:+ input := by
  cases read with
  | letBinding name _ initializer tail =>
    exact (tail.consumes.trans initializer.consumes).trans
      (List.suffix_append [letKeyword, .word name.val, assignment] _)

end Gabbro.Core.Ast
