module

public import Core.Ast.Program.StatementInversions
public import Core.Ast.Program.StatementSuffix

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

/-- The continuation after the common binding header and initializer. A new
    continuation starts at its own discriminator, such as the word `else`. -/
-- Combine the original StmtReads.deterministic and BlockItems.deterministic using the mutual recursor.
theorem StmtReads.deterministic (left : StmtReads result scope input a rest)
    (right : StmtReads result scope input b rest') : a = b ∧ rest = rest' := by
  revert b rest'
  refine StmtReads.rec
    (motive_1 := fun scope input tree rest _ =>
      ∀ {b rest'}, StmtReads result scope input b rest' → tree = b ∧ rest = rest')
    (motive_2 := fun before input tree rest _ =>
      ∀ {b rest'}, BlockItems result before input b rest' → tree = b ∧ rest = rest')
    (motive_3 := fun before input tree rest _ =>
      ∀ {b rest'}, BlockReads result before input b rest' → tree = b ∧ rest = rest')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ left
  · intros
    rename_i name ordinary exprRead letTail tree rest other
    obtain ⟨name', ordinary', _, value', more', sameName, read', tail'⟩ := other.let_header
    have nameEq : name' = name := Subtype.ext sameName
    cases nameEq
    obtain ⟨same, rfl⟩ := ExprReads.deterministic exprRead read'
    cases same
    exact LetTailReads.deterministic letTail tail'
  · intros
    rename_i s lo hi vlo vhi inputS val restS ref visible writable fits exprRead tree rest other
    obtain ⟨_, _, _, _, ref', visible', writable', value', fits', nameEq, read', treeEq⟩ := other.assign_inversion
    cases treeEq
    have eqRef : (⟨_, ref⟩ : (t : Ty .value) × Local s t) = ⟨_, ref'⟩ :=
      Local.visible_unique (scope := s) ref ref' visible visible' nameEq.symm
    cases eqRef
    obtain ⟨same, suffix⟩ := ExprReads.deterministic exprRead read'
    cases same
    exact ⟨rfl, (List.cons.inj suffix).2⟩
  · intros
    rename_i declared fits exprRead tree rest other
    cases declared
    rcases other.ret_inversion with ⟨t, value', fits', read', treeEq⟩ | ⟨tail, inputEq⟩
    · cases treeEq
      obtain ⟨same, suffix⟩ := ExprReads.deterministic exprRead read'
      cases same
      exact ⟨rfl, (List.cons.inj suffix).2⟩
    · exfalso
      cases inputEq
      cases exprRead with
      | atom a t => exact AtomReads.not_assignment a
  · intros
    rename_i condExpr first yesBlock more noBlock condRead yesRead noRead ihYes ihNo tree rest other
    rcases other.ite_inversion with ⟨cond', first', yes', more', no', condRead', yesRead', noRead', treeEq⟩ | ⟨tail, inputEq⟩
    · cases treeEq
      obtain ⟨same, firstEq⟩ := ExprReads.deterministic condRead condRead'
      cases same
      cases firstEq
      obtain ⟨sameYes, moreEq⟩ := ihYes yesRead'
      cases sameYes
      cases moreEq
      obtain ⟨sameNo, restEq⟩ := ihNo noRead'
      cases sameNo
      exact ⟨rfl, restEq⟩
    · exfalso
      cases inputEq
      cases condRead with
      | atom a t => exact AtomReads.not_assignment a
  · intros
    rename_i b rest' other
    cases other with
    | done => exact ⟨rfl, rfl⟩
    | step stRead _ => exact (StmtReads.disjoint_closeBrace stRead).elim
  · intros
    rename_i _ first next stRead blockRead ihSt ihBlock b rest' other
    cases other with
    | done => exact (StmtReads.disjoint_closeBrace stRead).elim
    | step stRead' blockRead' =>
        obtain ⟨sameFirst, moreEq⟩ := ihSt stRead'
        cases sameFirst
        cases moreEq
        obtain ⟨sameNext, restEq⟩ := ihBlock blockRead'
        cases sameNext
        exact ⟨rfl, restEq⟩
  · intros
    rename_i _ before input after body rest inner ih b rest' other
    cases other with
    | braced inner' =>
        obtain ⟨same, rfl⟩ := ih inner'
        cases same
        exact ⟨rfl, rfl⟩

theorem BlockItems.deterministic (left : BlockItems result scope input a rest)
    (right : BlockItems result scope input b rest') : a = b ∧ rest = rest' := by
  refine (BlockItems.rec
    (motive_1 := fun before input tree rest _ => True)
    (motive_2 := fun before input tree rest _ =>
      ∀ {b rest'}, BlockItems result before input b rest' → tree = b ∧ rest = rest')
    (motive_3 := fun before input tree rest _ => True)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial) ?_ ?_ (by intros; trivial) left) right
  · intros
    rename_i b rest' other
    cases other with
    | step stRead _ => exact (StmtReads.disjoint_closeBrace stRead).elim
    | done => exact ⟨rfl, rfl⟩
  · intros
    rename_i _ stRead midR moreR ihBlock b rest' other
    cases other with
    | done =>
        exfalso
        apply StmtReads.disjoint_closeBrace
        assumption
    | step stRead' blockRead' =>
        obtain ⟨sameFirst, moreEq⟩ := StmtReads.deterministic stRead stRead'
        injection sameFirst with hMiddle hFirst
        cases hMiddle
        cases hFirst
        cases moreEq
        obtain ⟨sameNext, restEq⟩ := ihBlock blockRead'
        cases sameNext
        exact ⟨rfl, restEq⟩

theorem BlockReads.deterministic (left : BlockReads result scope input a rest)
    (right : BlockReads result scope input b rest') : a = b ∧ rest = rest' := by
  cases left with
  | braced inner =>
    cases right with
    | braced inner' =>
      obtain ⟨same, rfl⟩ := inner.deterministic inner'
      cases same
      exact ⟨rfl, rfl⟩

end Gabbro.Core.Ast
