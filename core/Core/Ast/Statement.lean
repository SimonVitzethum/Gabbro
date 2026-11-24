module

public import Core.Ast.Program.StatementPrefixes
public import Core.Ast.Program.StatementSuffix

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

/-- The continuation after the common binding header and initializer. A new
    continuation starts at its own discriminator, such as the word `else`. -/
private theorem callNotReserved (call : DirectCall scope) (spelling : String)
    (reserved : spelling ∈ ["let", "if", "return", "while", "for", "leave", "next", "match"])
    (same : Token.word call.name.val :: first = keyword spelling :: second) : False :=
  call.ordinary.2 (List.mem_map.mpr ⟨spelling, reserved, (Token.word.inj (List.cons.inj same).1).symm⟩)

local macro "deny_statement" equality:ident : tactic =>
  `(tactic|
    exfalso
    first
    | (cases (List.cons.inj $equality).1; done)
    | (cases (List.cons.inj (List.cons.inj $equality).2).1; done)
    | (cases (List.cons.inj (List.cons.inj (List.cons.inj $equality).2).2).1; done)
    | cases (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj $equality).2).2).2).1)

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
    generalize eq : (returnKeyword :: semicolon :: _) = tokens at other
    cases other with
    | retVoid _ => exact ⟨rfl, (List.cons.inj (List.cons.inj eq).2).2⟩
    | ret otherDeclared _ _ => exact (by cases (declared.symm.trans otherDeclared))
    | retOption otherDeclared _ => exact (by cases (declared.symm.trans otherDeclared))
    | directCall callRead => cases callRead; deny_statement eq
    | tupleBind _ patternRead _ _ => cases patternRead; deny_statement eq
    | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
    | _ => deny_statement eq
  case letMutable =>
    intros
    rename_i name ordinary written valid fits typeRead valueRead _ _ other
    generalize eq : (letKeyword :: keyword "mut" :: Token.word name.val :: colon :: _) = tokens at other
    cases other with
    | letMutable otherName _ otherWritten _ _ otherType otherValue =>
      obtain ⟨nameEq, typeInput⟩ := binderHead_eq (List.cons.inj eq).2
      cases nameEq
      cases typeInput
      obtain ⟨rfl, rhsEq⟩ := typeRead.deterministic otherType
      cases (List.cons.inj rhsEq).2
      obtain ⟨same, suffix⟩ := valueRead.deterministic otherValue
      cases same
      exact ⟨rfl, (List.cons.inj suffix).2⟩
    | letOption mutable otherName otherOrdinary _ _ otherType otherValue =>
      cases mutable
      · have forbidden := Token.word.inj (List.cons.inj (List.cons.inj eq).2).1
        exact (otherOrdinary.1 forbidden.symm).elim
      · obtain ⟨_, typeInput⟩ := binderHead_eq (List.cons.inj eq).2
        cases typeInput
        obtain ⟨_, rhsEq⟩ := typeRead.deterministic otherType
        cases (List.cons.inj rhsEq).2
        exact (otherValue.disjointExpr valueRead).elim
    | directCall callRead => cases callRead; deny_statement eq
    | tupleBind _ patternRead _ _ => cases patternRead; deny_statement eq
    | _ => deny_statement eq
  case directCall =>
    intros
    rename_i call callRead _ _ other
    cases callRead
    generalize eq : (Token.word call.name.val :: openParen :: _) = tokens at other
    cases other with
    | directCall otherCall =>
      cases eq
      obtain ⟨rfl, suffix⟩ := CallReads.deterministic (.applied call (by assumption)) otherCall
      exact ⟨rfl, (List.cons.inj suffix).2⟩
    | ret _ _ _ => exact (callNotReserved call "return" (by decide) eq).elim
    | retVoid _ => exact (callNotReserved call "return" (by decide) eq).elim
    | retOption _ _ => exact (callNotReserved call "return" (by decide) eq).elim
    | ite _ _ _ => exact (callNotReserved call "if" (by decide) eq).elim
    | whileBounded _ _ _ _ _ _ _ => exact (callNotReserved call "while" (by decide) eq).elim
    | variantMatch _ _ => exact (callNotReserved call "match" (by decide) eq).elim
    | tupleBind _ _ _ _ => exact (callNotReserved call "let" (by decide) eq).elim
    | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
    | _ => deny_statement eq
  case bindDirect =>
    intros
    rename_i name ordinary written valid typeRead callRead _ _ other
    generalize eq : (letKeyword :: Token.word name.val :: colon :: _) = tokens at other
    cases other with
    | bindDirect otherName _ _ _ otherType otherCall =>
      obtain ⟨nameEq, typeInput⟩ := binderHead_eq eq
      cases nameEq
      cases typeInput
      obtain ⟨rfl, rhsEq⟩ := typeRead.deterministic otherType
      cases (List.cons.inj rhsEq).2
      obtain ⟨rfl, suffix⟩ := callRead.deterministic otherCall
      exact ⟨rfl, (List.cons.inj suffix).2⟩
    | letOption mutable _ _ _ _ otherType otherValue =>
      cases mutable
      · obtain ⟨_, typeInput⟩ := binderHead_eq eq
        cases typeInput
        obtain ⟨_, rhsEq⟩ := typeRead.deterministic otherType
        cases (List.cons.inj rhsEq).2
        exact (otherValue.disjointCall callRead).elim
      · deny_statement eq
    | directCall callRead => cases callRead; deny_statement eq
    | tupleBind _ patternRead _ _ => cases patternRead; deny_statement eq
    | _ => deny_statement eq
  case whileBounded =>
    intros
    rename_i nonnegative overflow bound staticBound condRead boundRead bodyRead bodyDet _ _ other
    generalize eq : (keyword "while" :: _) = tokens at other
    cases other with
    | whileBounded _ otherOverflow _ _ otherCond otherBound otherBody =>
      cases (List.cons.inj eq).2
      obtain ⟨sameCond, boundSuffix⟩ := condRead.deterministic otherCond
      cases sameCond
      cases (List.cons.inj boundSuffix).2
      obtain ⟨sameBound, bodySuffix⟩ := boundRead.deterministic otherBound
      cases sameBound
      have tail := (List.cons.inj (List.cons.inj bodySuffix).2).2
      cases Subtype.ext (Token.word.inj (List.cons.inj tail).1)
      cases (List.cons.inj tail).2
      obtain ⟨rfl, rfl⟩ := bodyDet otherBody
      exact ⟨rfl, rfl⟩
    | assignVar _ _ _ _ _ =>
      rw [(List.cons.inj eq).2] at condRead
      exact condRead.not_assignment.elim
    | assignField _ _ _ _ _ _ _ _ =>
      rw [(List.cons.inj eq).2] at condRead
      exact condRead.not_dot.elim
    | directCall callRead =>
      cases callRead
      rename_i call _
      exact (callNotReserved call "while" (by decide) eq.symm).elim
    | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
    | _ => deny_statement eq
  case forRange =>
    intros
    rename_i name ordinary body lower upper static lowerRead upperRead handlerRead bodyRead bodyDet _ _ other
    generalize eq : (keyword "for" :: Token.word name.val :: keyword "in" :: _) = tokens at other
    cases other with
    | forRange otherName _ _ _ _ _ otherLower otherUpper otherHandler otherBody =>
      obtain ⟨nameEq, rangeInput⟩ := binderHead_eq eq
      cases nameEq
      cases rangeInput
      obtain ⟨sameLower, upperInput⟩ := lowerRead.deterministic otherLower
      cases sameLower
      cases (List.cons.inj upperInput).2
      obtain ⟨sameUpper, rfl⟩ := upperRead.deterministic otherUpper
      cases sameUpper
      obtain ⟨rfl, rfl⟩ := handlerRead.deterministic otherHandler
      obtain ⟨rfl, rfl⟩ := bodyDet otherBody
      exact ⟨rfl, rfl⟩
    | directCall callRead => cases callRead; deny_statement eq
    | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
    | _ => deny_statement eq
  case tupleBind =>
    intros
    rename_i checked patternRead annotationRead valueRead _ _ other
    cases patternRead
    generalize eq : (letKeyword :: openParen :: _) = tokens at other
    cases other with
    | tupleBind _ otherPattern otherAnnotation otherValue =>
      cases (List.cons.inj eq).2
      obtain ⟨rfl, rfl⟩ := TuplePatternReads.deterministic (.tuple (by assumption) (by assumption) (by assumption)) otherPattern
      obtain ⟨rfl, rfl⟩ := annotationRead.deterministic otherAnnotation
      obtain ⟨same, suffix⟩ := valueRead.deterministic otherValue
      have sameType := tupleType_injective (congrArg Sigma.fst same)
      cases sameType
      cases same
      exact ⟨rfl, (List.cons.inj suffix).2⟩
    | directCall callRead =>
      cases callRead
      rename_i call _
      exact (callNotReserved call "let" (by decide) eq.symm).elim
    | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
    | _ => deny_statement eq
  case assignField =>
    intros
    rename_i ref visible writable field index checked fits valueRead _ _ other
    generalize eq : (Token.word ref.binding.name.val :: dot :: Token.word field.val :: assignment :: _) = tokens at other
    cases other with
    | assignField otherRef otherVisible _ otherField otherIndex otherChecked _ otherValue =>
      have sameRef := Local.visible_unique ref otherRef visible otherVisible (Token.word.inj (List.cons.inj eq).1)
      have sameType := congrArg Sigma.fst sameRef
      injection sameType with hn hl ht
      cases hn
      cases identifierList_injective hl
      cases tupleType_injective ht
      cases sameRef
      have fieldTail := (List.cons.inj (List.cons.inj eq).2).2
      cases Subtype.ext (Token.word.inj (List.cons.inj fieldTail).1)
      have sameIndex : index = otherIndex :=
        Fin.ext (identifierPosition_unique checked.1 checked.2 otherChecked.2)
      cases sameIndex
      cases (List.cons.inj (List.cons.inj fieldTail).2).2
      obtain ⟨same, suffix⟩ := valueRead.deterministic otherValue
      cases same
      exact ⟨rfl, (List.cons.inj suffix).2⟩
    | ret _ _ otherValue =>
      rw [← (List.cons.inj eq).2] at otherValue
      exact otherValue.not_dot.elim
    | ite otherCond _ _ =>
      rw [← (List.cons.inj eq).2] at otherCond
      exact otherCond.not_dot.elim
    | whileBounded _ _ _ _ otherCond _ _ =>
      rw [← (List.cons.inj eq).2] at otherCond
      exact otherCond.not_dot.elim
    | variantMatch otherValue _ =>
      rw [← (List.cons.inj eq).2] at otherValue
      exact otherValue.not_dot.elim
    | retOption _ otherValue =>
      rw [← (List.cons.inj eq).2] at otherValue
      cases otherValue
    | tupleBind _ patternRead _ _ => cases patternRead; deny_statement eq
    | directCall callRead => cases callRead; deny_statement eq
    | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
    | _ => deny_statement eq
  case letMutableValue =>
    intros
    rename_i name ordinary valueRead _ _ other
    generalize eq : (letKeyword :: keyword "mut" :: Token.word name.val :: assignment :: _) = tokens at other
    cases other with
    | letMutableValue otherName _ otherValue =>
      obtain ⟨nameEq, rhsEq⟩ := binderHead_eq (List.cons.inj eq).2
      cases nameEq
      cases rhsEq
      obtain ⟨same, suffix⟩ := valueRead.deterministic otherValue
      cases same
      exact ⟨rfl, (List.cons.inj suffix).2⟩
    | directCall callRead => cases callRead; deny_statement eq
    | tupleBind _ patternRead _ _ => cases patternRead; deny_statement eq
    | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
    | _ => deny_statement eq
  case variantMatch =>
    intros
    rename_i valueRead armsRead armsDet _ _ other
    generalize eq : (keyword "match" :: _) = tokens at other
    cases other with
    | variantMatch otherValue otherArms =>
      cases (List.cons.inj eq).2
      obtain ⟨same, suffix⟩ := valueRead.deterministic otherValue
      obtain ⟨rfl, rfl, rfl⟩ := variantValueType_injective (congrArg Sigma.fst same)
      cases same
      cases (List.cons.inj suffix).2
      obtain ⟨rfl, rfl⟩ := armsDet otherArms
      exact ⟨rfl, rfl⟩
    | assignVar _ _ _ _ _ =>
      rw [(List.cons.inj eq).2] at valueRead
      exact valueRead.not_assignment.elim
    | assignField _ _ _ _ _ _ _ _ =>
      rw [(List.cons.inj eq).2] at valueRead
      exact valueRead.not_dot.elim
    | directCall callRead =>
      cases callRead
      rename_i call _
      exact (callNotReserved call "match" (by decide) eq.symm).elim
    | letOption mutable _ _ _ _ _ _ => cases mutable <;> deny_statement eq
    | _ => deny_statement eq
  case letOption =>
    intros
    rename_i mutable name ordinary carrier resolved typeRead valueRead _ _ other
    generalize eq : (optionLetHead mutable name ++ _) = tokens at other
    cases other with
    | letOption otherMutable otherName otherOrdinary otherCarrier otherResolved otherType otherValue =>
      have sameHead := optionBindingHead_eq ordinary.1 otherOrdinary.1 eq
      obtain ⟨rfl, rfl, rfl⟩ := sameHead
      obtain ⟨sameType, rhsEq⟩ := typeRead.deterministic otherType
      injection sameType with hCarrier hCount
      cases hCarrier
      cases hCount
      cases (List.cons.inj rhsEq).2
      obtain ⟨rfl, suffix⟩ := valueRead.deterministic otherValue
      exact ⟨rfl, (List.cons.inj suffix).2⟩
    | letMutable _ _ _ _ _ otherType otherValue =>
      cases mutable
      · deny_statement eq
      · obtain ⟨_, rfl⟩ := binderHead_eq (List.cons.inj eq).2
        obtain ⟨_, rhsEq⟩ := typeRead.deterministic otherType
        cases (List.cons.inj rhsEq).2
        exact (valueRead.disjointExpr otherValue).elim
    | bindDirect _ _ _ _ otherType otherCall =>
      cases mutable
      · obtain ⟨_, rfl⟩ := binderHead_eq eq
        obtain ⟨_, rhsEq⟩ := typeRead.deterministic otherType
        cases (List.cons.inj rhsEq).2
        exact (valueRead.disjointCall otherCall).elim
      · deny_statement eq
    | directCall callRead => cases callRead; cases mutable <;> deny_statement eq
    | tupleBind _ patternRead _ _ => cases patternRead; cases mutable <;> deny_statement eq
    | _ => cases mutable <;> deny_statement eq
  case retOption =>
    intros
    rename_i declared valueRead _ _ other
    cases declared
    rcases other.ret_inversion with ⟨_, _, _, exprRead, _⟩ | (⟨_, otherDeclared, _, otherValue, rfl⟩ | assignment)
    · exact (valueRead.disjointExpr exprRead).elim
    · have sameCount := indexOptionType_injective (Option.some.inj otherDeclared)
      cases sameCount
      obtain ⟨rfl, suffix⟩ := valueRead.deterministic otherValue
      exact ⟨rfl, (List.cons.inj suffix).2⟩
    · rcases assignment with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> cases valueRead
  case armsDone =>
    intros
    rename_i other
    cases other
    exact ⟨rfl, rfl⟩
  case armsNullary =>
    intros
    rename_i label caseName bodyRead tailRead bodyDet tailDet _ _ other
    cases other with
    | nullary _ _ otherBody otherTail =>
      obtain ⟨rfl, rfl⟩ := bodyDet otherBody
      obtain ⟨rfl, rfl⟩ := tailDet otherTail
      exact ⟨rfl, rfl⟩
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
    | _ => deny_statement eq
  case armsWildcard =>
    intros
    rename_i bodyRead bodyDet _ _ other
    cases other with
    | wildcard _ _ otherBody =>
      obtain ⟨rfl, suffix⟩ := bodyDet otherBody
      exact ⟨rfl, (List.cons.inj suffix).2⟩
    | nullary _ caseName _ _ => exact (caseName rfl).elim

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
