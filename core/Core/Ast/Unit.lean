module

public import Core.Ast.Declaration.Grammar

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

abbrev UnitItems (before : Scope) := (after : Scope) × UnitBody before after

/-- A unit has no unconsumed suffix. Each declaration determines the scope of the next. -/
inductive UnitReads : (before : Scope) → List Token → UnitItems before → Prop where
  | done : UnitReads scope [] ⟨scope, .done⟩
  | step : DeclReads before input ⟨middle, first⟩ more →
      UnitReads middle more ⟨after, next⟩ →
      UnitReads before input ⟨after, .step first next⟩

theorem UnitReads.deterministic (left : UnitReads before input a) (right : UnitReads before input b) :
    a = b := by
  induction left with
  | done =>
    cases right with
    | done => rfl
    | step read _ => exact (read.disjoint_end).elim
  | step first next ih =>
    cases right with
    | done => exact (first.disjoint_end).elim
    | step first' next' =>
      obtain ⟨same, rfl⟩ := first.deterministic first'
      cases same
      have equal := ih next'
      cases equal
      rfl

def UnitBody.printPieces : UnitBody before after → List PrintedToken
  | .done => []
  | .step first next => first.printPieces ++ next.printPieces

theorem UnitBody.printReads (tree : UnitBody before after) :
    UnitReads before (tree.printPieces.map PrintedToken.value) ⟨after, tree⟩ := by
  induction tree with
  | done => exact .done
  | step first next ih =>
    simp only [UnitBody.printPieces, List.map_append]
    exact .step (first.printReads _) ih

end Gabbro.Core.Ast
