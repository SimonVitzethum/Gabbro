module

public import Core.Ast.Program.StatementPrefixes
public import Core.Ast.Program.StatementSuffix
import Core.Ast.Program.StatementComparison

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

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
    (motive_4 := fun scope allowed input labels payloads tree rest _ =>
      ∀ {other suffix}, VariantArmsRead result scope allowed input (labels := labels) (payloads := payloads)
        other suffix → tree = other ∧ rest = suffix)
    ?letBinding ?assignVar ?ret ?ite ?retVoid ?letMutable ?directCall ?bindDirect
    ?whileBounded ?forRange ?tupleBind ?assignField ?letMutableValue ?variantMatch ?letOption ?retOption
    ?done ?step ?braced ?armsDone ?armsNullary ?armsPayload ?armsWildcard left
  case letBinding =>
    intros
    rename_i name ordinary exprRead letTail tree rest other
    obtain ⟨name', ordinary', _, value', more', sameName, read', tail'⟩ := other.let_header
    have nameEq : name' = name := Subtype.ext sameName
    cases nameEq
    obtain ⟨same, rfl⟩ := ExprReads.deterministic exprRead read'
    cases same
    exact LetTailReads.deterministic letTail tail'
  case assignVar =>
    intros
    rename_i s lo hi vlo vhi inputS val restS ref visible writable fits exprRead tree rest other
    obtain ⟨_, _, _, _, ref', visible', writable', value', fits', nameEq, read', treeEq⟩ := other.assign_inversion
    cases treeEq
    have eqRef : (⟨_, ref⟩ : (t : Ty .value) × Local s t) = ⟨_, ref'⟩ :=
      Local.visible_unique (scope := s) ref ref' visible visible' nameEq.symm
    cases eqRef
    obtain ⟨same, suffix⟩ := ExprReads.deterministic exprRead read'
    cases same
    exact ⟨rfl, (List.cons.inj suffix).2⟩
  case ret =>
    intros
    rename_i declared fits exprRead tree rest other
    cases declared
    rcases other.ret_inversion with ⟨t, value', fits', read', treeEq⟩ | (⟨_, _, _, optionRead, _⟩ | assigning)
    · cases treeEq
      obtain ⟨same, suffix⟩ := ExprReads.deterministic exprRead read'
      cases same
      exact ⟨rfl, (List.cons.inj suffix).2⟩
    · exact (optionRead.disjointExpr exprRead).elim
    · exact (exprRead.not_assignmentStart assigning).elim
  case ite =>
    intros
    rename_i condExpr first yesBlock more noBlock condRead yesRead noRead ihYes ihNo tree rest other
    rcases other.ite_inversion with ⟨cond', first', yes', more', no', condRead', yesRead', noRead', treeEq⟩ | assigning
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
    · exact (condRead.not_assignmentStart assigning).elim
  case done =>
    intros
    rename_i b rest' other
    cases other with
    | done => exact ⟨rfl, rfl⟩
    | step stRead _ => exact (StmtReads.disjoint_closeBrace stRead).elim
  case step =>
    intros
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
  case braced =>
    intros
    rename_i _ before input after body rest inner ih b rest' other
    cases other with
    | braced inner' =>
        obtain ⟨same, rfl⟩ := ih inner'
        cases same
        exact ⟨rfl, rfl⟩

  case retVoid =>
    intros
    rename_i declared _ _ other
    exact StatementComparison.retVoid declared other
  case letMutable =>
    intros
    rename_i name ordinary written valid fits typeRead valueRead _ _ other
    exact StatementComparison.letMutable name ordinary written valid fits typeRead valueRead other
  case directCall =>
    intros
    rename_i callRead _ _ other
    cases callRead
    exact StatementComparison.directCall _ (by assumption) other
  case bindDirect =>
    intros
    rename_i name ordinary written valid typeRead callRead _ _ other
    exact StatementComparison.bindDirect name ordinary written valid typeRead callRead other
  case whileBounded =>
    intros
    rename_i nonnegative overflow bound staticBound condRead boundRead bodyRead bodyDet _ _ other
    exact StatementComparison.whileBounded nonnegative overflow bound staticBound condRead boundRead bodyRead bodyDet other
  case forRange =>
    intros
    rename_i name ordinary body lower upper static lowerRead upperRead handlerRead bodyRead bodyDet _ _ other
    exact StatementComparison.forRange name ordinary body lower upper static lowerRead upperRead handlerRead bodyRead bodyDet other
  case tupleBind =>
    intros
    rename_i checked patternRead annotationRead valueRead _ _ other
    exact StatementComparison.tupleBind checked patternRead annotationRead valueRead other
  case assignField =>
    intros
    rename_i ref visible writable field index checked fits valueRead _ _ other
    exact StatementComparison.assignField ref visible writable field index checked fits valueRead other
  case letMutableValue =>
    intros
    rename_i name ordinary valueRead _ _ other
    exact StatementComparison.letMutableValue name ordinary valueRead other
  case variantMatch =>
    intros
    rename_i valueRead armsRead armsDet _ _ other
    exact StatementComparison.variantMatch valueRead armsRead armsDet other
  case letOption =>
    intros
    rename_i mutable name ordinary carrier resolved typeRead valueRead _ _ other
    exact StatementComparison.letOption mutable name ordinary carrier resolved typeRead valueRead other
  case retOption =>
    intros
    rename_i declared valueRead _ _ other
    exact StatementComparison.retOption declared valueRead other
  case armsDone =>
    intros
    rename_i other
    cases other
    exact ⟨rfl, rfl⟩
  case armsNullary =>
    intros
    rename_i label caseName bodyRead tailRead bodyDet tailDet _ _ other
    generalize eq : (Token.word label.val :: matchArrow :: _) = tokens at other
    cases other with
    | nullary _ _ otherBody otherTail =>
      cases (List.cons.inj (List.cons.inj eq).2).2
      obtain ⟨rfl, rfl⟩ := bodyDet otherBody
      obtain ⟨rfl, rfl⟩ := tailDet otherTail
      exact ⟨rfl, rfl⟩
    | wildcard _ _ _ => exact (caseName (Token.word.inj (List.cons.inj eq).1)).elim
  case armsPayload =>
    intros
    rename_i label binder ordinary body bodyRead tailRead bodyDet tailDet _ _ other
    generalize eq : (Token.word label.val :: openParen :: Token.word binder.val :: closeParen :: matchArrow :: _) = tokens at other
    cases other with
    | payload _ otherBinder _ _ otherBody otherTail =>
      have tail := (List.cons.inj (List.cons.inj eq).2).2
      cases Subtype.ext (Token.word.inj (List.cons.inj tail).1)
      cases (List.cons.inj (List.cons.inj (List.cons.inj tail).2).2).2
      obtain ⟨rfl, rfl⟩ := bodyDet otherBody
      obtain ⟨rfl, rfl⟩ := tailDet otherTail
      exact ⟨rfl, rfl⟩
    | wildcard _ _ _ => cases (List.cons.inj (List.cons.inj eq).2).1
  case armsWildcard =>
    intros
    rename_i input _ _ _ _ _ _ bodyRead bodyDet _ _ other
    generalize eq : (Token.word ['_'] :: matchArrow :: input) = tokens at other
    cases other with
    | wildcard _ _ otherBody =>
      cases (List.cons.inj (List.cons.inj eq).2).2
      obtain ⟨rfl, suffix⟩ := bodyDet otherBody
      exact ⟨rfl, (List.cons.inj suffix).2⟩
    | nullary _ caseName _ _ =>
      exact (caseName (Token.word.inj (List.cons.inj eq).1).symm).elim
    | payload _ _ _ _ _ _ => cases (List.cons.inj (List.cons.inj eq).2).1
    | done => cases (List.cons.inj eq).1

theorem BlockItems.deterministic (left : BlockItems result scope input a rest)
    (right : BlockItems result scope input b rest') : a = b ∧ rest = rest' := by
  refine (BlockItems.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun before input tree rest _ =>
      ∀ {b rest'}, BlockItems result before input b rest' → tree = b ∧ rest = rest')
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ left) right
  all_goals try (intros; trivial)
  · intros
    rename_i other
    cases other with
    | done => exact ⟨rfl, rfl⟩
    | step statementRead _ => exact (StmtReads.disjoint_closeBrace statementRead).elim
  · intros
    rename_i statementRead itemsRead _ itemsDet _ _ other
    cases other with
    | done => exact (StmtReads.disjoint_closeBrace statementRead).elim
    | step otherStatement otherItems =>
      obtain ⟨same, rfl⟩ := statementRead.deterministic otherStatement
      cases same
      obtain ⟨otherSame, rfl⟩ := itemsDet otherItems
      cases otherSame
      exact ⟨rfl, rfl⟩

theorem BlockReads.deterministic (left : BlockReads result scope input a rest)
    (right : BlockReads result scope input b rest') : a = b ∧ rest = rest' := by
  cases left with
  | braced items =>
    cases right with
    | braced otherItems =>
      obtain ⟨same, rfl⟩ := items.deterministic otherItems
      cases same
      exact ⟨rfl, rfl⟩

end Gabbro.Core.Ast
