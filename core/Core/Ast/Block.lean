module

public import Core.Ast.Print

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

/-- Read statements through the closing brace, carrying the growing scope. -/
inductive BlockItems : (before : Scope) → List Token → Statements before → List Token → Prop where
  | done : BlockItems scope (closeBrace :: rest) ⟨scope, .done⟩ rest
  | step : StmtReads before input ⟨middle, first⟩ more →
      BlockItems middle more ⟨after, next⟩ rest →
      BlockItems before input ⟨after, .step first next⟩ rest

theorem BlockItems.deterministic (left : BlockItems before input a rest)
    (right : BlockItems before input b rest') : a = b ∧ rest = rest' := by
  induction left with
  | done =>
    cases right with
    | done => exact ⟨rfl, rfl⟩
    | step read _ => exact (read.disjoint_closeBrace).elim
  | step first next ih =>
    cases right with
    | done => exact (first.disjoint_closeBrace).elim
    | step first' next' =>
      obtain ⟨same, rfl⟩ := first.deterministic first'
      cases same
      obtain ⟨equal, rfl⟩ := ih next'
      cases equal
      exact ⟨rfl, rfl⟩

inductive BlockReads (before : Scope) : List Token → Statements before → List Token → Prop where
  | braced : BlockItems before input tree rest → BlockReads before (openBrace :: input) tree rest

theorem BlockReads.deterministic (left : BlockReads before input a rest)
    (right : BlockReads before input b rest') : a = b ∧ rest = rest' := by
  cases left with
  | braced inner =>
    cases right with
    | braced inner' => exact inner.deterministic inner'

def Block.printItems : Block before after → List PrintedToken
  | .done => []
  | .step first next => first.printPieces ++ next.printItems

def Block.printPieces (tree : Block before after) : List PrintedToken :=
  printOpenBrace :: tree.printItems ++ [printCloseBrace]

theorem Block.printItems_reads (tree : Block before after) (rest : List Token) :
    BlockItems before (tree.printItems.map PrintedToken.value ++ closeBrace :: rest) ⟨after, tree⟩ rest := by
  induction tree with
  | done => exact .done
  | step first next ih =>
    simp only [Block.printItems, List.map_append, List.append_assoc]
    exact .step (first.printReads _) ih

theorem Block.printReads (tree : Block before after) :
    BlockReads before (tree.printPieces.map PrintedToken.value) ⟨after, tree⟩ [] := by
  simp only [Block.printPieces, List.map_append, List.map_cons, List.map_nil]
  exact .braced (tree.printItems_reads [])

end Gabbro.Core.Ast
