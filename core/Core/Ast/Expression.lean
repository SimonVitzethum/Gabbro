module

public import Core.Ast.Expression.Resolution
public import Core.Ast.Expression.Suffix

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

-- Extend the original mutual ExprReads.deterministic recursor with the new atom and tail branches.
theorem ExprReads.deterministic (left : ExprReads scope minimum input a rest)
    (right : ExprReads scope minimum input b rest') : a.typed = b.typed ∧ rest = rest' := by
  revert b rest'
  refine ExprReads.rec
    (motive_1 := fun min input _ a rest _ =>
      ∀ {otherType} {b : Expr scope otherType} {rest'}, ExprReads scope min input b rest' → a.typed = b.typed ∧ rest = rest')
    (motive_2 := fun input _ a rest _ =>
      ∀ {otherType} {b : Expr scope otherType} {rest'}, AtomReads scope input b rest' → a.typed = b.typed ∧ rest = rest')
    (motive_3 := fun min _ first input _ a rest _ =>
      ∀ {otherType} {b : Expr scope otherType} {rest'}, ExprTail scope min first input b rest' → a.typed = b.typed ∧ rest = rest')
    (motive_4 := fun close input _ items rest _ =>
      ∀ {otherTypes} {b : ExprItems scope otherTypes} {rest'},
        (close = closeParen ∨ close = closeBracket) →
      ItemsRead scope close input b rest' → ((⟨_, items⟩ : Σ ts, ExprItems scope ts) = ⟨_, b⟩) ∧ rest = rest')
    (motive_5 := fun close input _ items rest _ =>
      ∀ {otherTypes} {b : ExprItems scope otherTypes} {rest'},
        (close = closeParen ∨ close = closeBracket) →
      ItemsTail scope close input b rest' → ((⟨_, items⟩ : Σ ts, ExprItems scope ts) = ⟨_, b⟩) ∧ rest = rest')
    (motive_6 := fun input _ _ items rest _ =>
      ∀ {labels types} {b : LabeledItems scope labels types} {rest'},
        LabeledItemsRead scope input b rest' → ((⟨_, _, items⟩ : Σ ls ts, LabeledItems scope ls ts) = ⟨_, _, b⟩) ∧ rest = rest')
    (motive_7 := fun input _ _ items rest _ =>
      ∀ {labels types} {b : LabeledItems scope labels types} {rest'},
        LabeledItemsTail scope input b rest' → ((⟨_, _, items⟩ : Σ ls ts, LabeledItems scope ls ts) = ⟨_, _, b⟩) ∧ rest = rest')
    (motive_8 := fun input _ payload rest _ =>
      ∀ {type} {b : CasePayload scope type} {rest'},
        CasePayloadRead scope input b rest' → ((⟨_, payload⟩ : Σ t, CasePayload scope t) = ⟨_, b⟩) ∧ rest = rest')
    ?atom ?lit ?grouped ?trueLit ?falseLit ?«variable» ?negativeLit ?neg ?not
    ?arrayValue ?tupleValue ?recordValue ?variantValue ?textLiteral ?textLength
    ?stop ?binary ?div ?compare ?logic ?arrayIndex ?tupleField ?recordField
    ?textConcat ?textIndex ?substring ?optionIsSome
    ?itemsClose ?itemsNext ?itemsTailClose ?itemsTailComma
    ?labeledClose ?labeledNext ?labeledTailClose ?labeledTailComma
    ?payloadBare ?payloadEmpty ?payloadValue left
  case atom =>
    intros
    rename_i input firstType first more minimum treeType tree rest atomRead tailRead atomDet tailDet otherType b rest' otherRead
    cases otherRead with
    | atom atom tail =>
      obtain ⟨same, rfl⟩ := atomDet atom
      cases same
      exact tailDet tail
  case lit =>
    intros
    rename_i _ _ value rest _ _ _ otherRead
    obtain ⟨same, suffix⟩ := otherRead.lit_inversion
    exact ⟨same.symm, suffix.symm⟩
  case grouped =>
    intros
    rename_i _ _ input _ tree rest insideRead insideDet _ _ _ otherRead
    cases otherRead with
    | grouped inside =>
      obtain ⟨same, suffix⟩ := insideDet inside
      exact ⟨same, (List.cons.inj suffix).2⟩
    | tupleValue firstRead _ _ =>
      exact (by obtain ⟨_, suffix⟩ := insideDet firstRead; cases suffix)
  case trueLit =>
    intros
    rename_i _ _ rest _ _ _ otherRead
    obtain ⟨same, suffix⟩ := otherRead.true_inversion
    exact ⟨same.symm, suffix.symm⟩
  case falseLit =>
    intros
    rename_i _ _ rest _ _ _ otherRead
    obtain ⟨same, suffix⟩ := otherRead.false_inversion
    exact ⟨same.symm, suffix.symm⟩
  case «variable» =>
    intros
    rename_i _ _ _ rest ref vis ord _ _ _ otherRead
    obtain ⟨_, ref', vis', ord', nameEq, sameTree, suffix⟩ := otherRead.variable_inversion ord ⟨_, ref, vis, rfl⟩
    have eqRef : (⟨_, ref⟩ : (t : Ty .value) × Local scope t) = ⟨_, ref'⟩ :=
      Local.visible_unique ref ref' vis vis' nameEq.symm
    cases eqRef
    cases sameTree
    exact ⟨rfl, suffix.symm⟩
  case negativeLit =>
    intros
    rename_i _ _ value rest _ _ _ otherRead
    obtain ⟨same, suffix⟩ := otherRead.negative_inversion
    exact ⟨same.symm, suffix.symm⟩
  case neg =>
    intros
    rename_i _ _ input _ _ operand rest start child childDet _ _ _ otherRead
    obtain ⟨_, _, operand', read', sameTree⟩ := otherRead.neg_inversion start
    cases sameTree
    obtain ⟨same, suffix⟩ := childDet read'
    cases same
    exact ⟨rfl, suffix⟩
  case not =>
    intros
    rename_i _ _ input operand rest _ child childDet _ _ _ otherRead
    obtain ⟨operand', primary, read', sameTree⟩ := otherRead.not_inversion
    cases sameTree
    obtain ⟨same, suffix⟩ := childDet read'
    cases same
    exact ⟨rfl, suffix⟩
  case stop =>
    intros
    rename_i _ _ _ rest _ left blocked _ _ _ otherRead
    cases otherRead with
    | stop => exact ⟨rfl, rfl⟩
    | binary op allowed => exact (blocked ⟨.arith op, _, rfl, allowed⟩).elim
    | div allowed => exact (blocked ⟨.div, _, rfl, allowed⟩).elim
    | compare op allowed => exact (blocked ⟨.compare op, _, rfl, allowed⟩).elim
    | logic op allowed => exact (blocked ⟨.logic op, _, rfl, allowed⟩).elim
    | arrayIndex _ _ _ allowed => exact (blocked ⟨.index, _, rfl, allowed⟩).elim
    | tupleField _ _ allowed => exact (blocked ⟨.projection, _, rfl, allowed⟩).elim
    | recordField _ _ _ _ allowed => exact (blocked ⟨.projection, _, rfl, allowed⟩).elim
    | textConcat _ _ allowed => exact (blocked ⟨.arith .add, _, rfl, allowed⟩).elim
    | textIndex _ _ allowed => exact (blocked ⟨.index, _, rfl, allowed⟩).elim
    | substring _ _ _ allowed => exact (blocked ⟨.index, _, rfl, allowed⟩).elim
    | optionIsSome _ _ _ allowed => exact (blocked ⟨.projection, _, rfl, allowed⟩).elim
  case binary =>

    intros
    rename_i _ _ _ input _ _ _ _ _ _ _ _ _ _ op allowed _ _ rightDet tailDet _ _ _ otherRead
    generalize h : op.token = token at otherRead
    cases otherRead with
    | stop blocked => exact (blocked ⟨.arith op, input, by simpa only [Infix.token] using congrArg (· :: input) h.symm, allowed⟩).elim
    | binary op' _ rightRead tail =>
      have eq : op = op' := Arith.token_injective h
      cases eq
      obtain ⟨same, rfl⟩ := rightDet rightRead
      cases same
      exact tailDet tail
    | div _ rightRead _ tail =>
      have eq := Infix.token_injective (a := .arith op) (b := .div) h
      cases eq
    | compare op' _ rightRead _ tail =>
      have eq := Infix.token_injective (a := .arith op) (b := .compare op') h
      cases eq
  case div =>
    intros
    rename_i _ _ _ input _ _ _ _ _ _ _ _ _ _ allowed _ _ _ rightDet tailDet _ _ _ otherRead
    generalize h : Infix.token .div = token at otherRead
    cases otherRead with
    | stop blocked => exact (blocked ⟨.div, input, congrArg (· :: input) h.symm, allowed⟩).elim
    | binary op' _ rightRead tail =>
      have eq := Infix.token_injective (a := .div) (b := .arith op') h
      cases eq
    | div _ rightRead _ tail' =>
      obtain ⟨same, rfl⟩ := rightDet rightRead
      cases same
      exact tailDet tail'
    | compare op' _ rightRead _ tail =>
      have eq := Infix.token_injective (a := .div) (b := .compare op') h
      cases eq
  case compare =>
    intros
    rename_i _ _ _ input _ _ _ _ _ _ _ _ _ _ op allowed _ _ _ rightDet tailDet _ _ _ otherRead
    generalize h : Infix.token (.compare op) = token at otherRead
    cases otherRead with
    | stop blocked => exact (blocked ⟨.compare op, input, congrArg (· :: input) h.symm, allowed⟩).elim
    | binary op' _ rightRead tail =>
      have eq := Infix.token_injective (a := .compare op) (b := .arith op') h
      cases eq
    | div _ rightRead _ tail =>
      have eq := Infix.token_injective (a := .compare op) (b := .div) h
      cases eq
    | compare op' _ rightRead _ tail' =>
      have eq := Infix.token_injective (a := .compare op) (b := .compare op') h
      cases eq
      obtain ⟨same, rfl⟩ := rightDet rightRead
      cases same
      exact tailDet tail'
  case logic =>
    intros
    rename_i _ _ _ input _ _ _ _ _ _ op allowed _ _ rightDet tailDet _ _ _ otherRead
    generalize h : Infix.token (.logic op) = token at otherRead
    cases otherRead with
    | stop blocked => exact (blocked ⟨.logic op, input, congrArg (· :: input) h.symm, allowed⟩).elim
    | logic op' _ rightRead tail' =>
      have eq := Infix.token_injective (a := .logic op) (b := .logic op') h
      cases eq
      obtain ⟨same, rfl⟩ := rightDet rightRead
      cases same
      exact tailDet tail'
  case arrayValue =>
    intros
    rename_i principal fits itemsRead itemsDet _ _ _ otherRead
    cases otherRead with
    | arrayValue otherPrincipal otherFits otherItems =>
      obtain ⟨same, rfl⟩ := itemsDet (Or.inr rfl) otherItems
      cases same
      cases principal.symm.trans otherPrincipal
      exact ⟨rfl, rfl⟩
  case tupleValue =>
    intros
    rename_i firstRead secondRead tailRead firstDet secondDet itemsDet _ _ _ otherRead
    cases otherRead with
    | grouped inside =>
      exact (by
        obtain ⟨_, delim⟩ := firstDet inside
        cases delim)
    | tupleValue otherFirst otherSecond otherItems =>
      obtain ⟨same, hfirst⟩ := firstDet otherFirst
      cases same
      cases (List.cons.inj hfirst).2
      obtain ⟨same, rfl⟩ := secondDet otherSecond
      cases same
      obtain ⟨same, rfl⟩ := itemsDet (Or.inl rfl) otherItems
      cases same
      exact ⟨rfl, rfl⟩
  case recordValue =>
    intros
    rename_i ref fields fits argRead argDet _ _ _ otherRead
    generalize hname : Token.word ref.name.val = token at otherRead
    cases otherRead with
    | recordValue otherRef otherFields otherFits otherArgs =>
      have sameRefs := ref.unique otherRef (Token.word.inj hname)
      cases sameRefs
      obtain ⟨sameArgs, rfl⟩ := argDet otherArgs
      cases sameArgs
      have sameFields := fields.unique otherFields (LabeledItems.lengths _)
      cases sameFields
      exact ⟨rfl, rfl⟩
    | «variable» localRef visible _ =>
      have same := Local.nameVisible_unique localRef ref.schema visible.2 ref.visible
        ((Token.word.inj hname).symm.trans ref.spelled.symm)
      exact (Eq.mp (congrArg Ty.valueBinding (congrArg Sigma.fst same)) visible.1 : False).elim
    | variantValue _ _ _ _ _ available _ _ =>
      exact (available.2 _ ref.schema.binding_mem
        (ref.spelled.trans (Token.word.inj hname))).elim
    | trueLit => exact (ref.ordinary.1 (Token.word.inj hname)).elim
    | falseLit => exact (ref.ordinary.2.1 (Token.word.inj hname)).elim
    | textLength _ => exact (ref.ordinary.2.2.1 (Token.word.inj hname)).elim
    | _ => cases hname
  case variantValue =>
    intros
    rename_i ref label index written ordinary available payload payloadRead payloadDet _ _ _ otherRead
    generalize hname : Token.word label.val = token at otherRead
    cases otherRead with
    | variantValue otherRef otherLabel otherIndex otherWritten _ _ otherPayload otherPayloadRead =>
      cases Subtype.ext (Token.word.inj hname)
      have sameRef := ref.unique otherRef (List.mem_of_getElem? written)
        (List.mem_of_getElem? otherWritten) available
      cases sameRef
      have sameIndex : index = otherIndex :=
        Fin.ext (identifierPosition_unique ref.distinct written otherWritten)
      cases sameIndex
      obtain ⟨samePayload, rfl⟩ := payloadDet otherPayloadRead
      cases samePayload
      exact ⟨rfl, rfl⟩
    | «variable» localRef visible _ =>
      exact (available.2 _ localRef.binding_mem (Token.word.inj hname).symm).elim
    | recordValue otherRef _ _ _ =>
      exact (available.2 _ otherRef.schema.binding_mem
        (otherRef.spelled.trans (Token.word.inj hname).symm)).elim
    | trueLit => exact (ordinary.1 (Token.word.inj hname)).elim
    | falseLit => exact (ordinary.2.1 (Token.word.inj hname)).elim
    | textLength _ => exact (ordinary.2.2.1 (Token.word.inj hname)).elim
    | _ => cases hname
  case textLiteral =>
    intros
    rename_i _ _ _ otherRead
    cases otherRead
    exact ⟨rfl, rfl⟩
  case textLength =>
    intros
    rename_i innerRead innerDet _ _ _ otherRead
    generalize h : lenofKeyword = token at otherRead
    cases otherRead with
    | textLength inner =>
      obtain ⟨same, suffix⟩ := innerDet inner
      cases same
      exact ⟨rfl, (List.cons.inj suffix).2⟩
    | «variable» ref visible ordinary =>
      exact (ordinary.2.2.1 (Token.word.inj h).symm).elim
    | recordValue ref _ _ _ =>
      exact (ref.ordinary.2.2.1 (Token.word.inj h).symm).elim
    | variantValue _ _ _ _ ordinary _ _ _ =>
      exact (ordinary.2.2.1 (Token.word.inj h).symm).elim
    | _ => cases h
  case arrayIndex =>
    intros
    rename_i allowed indexRead tailRead indexDet tailDet _ _ _ otherRead
    cases otherRead with
    | stop blocked => exact (blocked ⟨.index, _, rfl, allowed⟩).elim
    | arrayIndex _ _ _ _ otherIndex otherTail =>
      obtain ⟨same, suffix⟩ := indexDet otherIndex
      cases same
      cases (List.cons.inj suffix).2
      exact tailDet otherTail
  case textConcat =>
    intros
    rename_i allowed rightRead tailRead rightDet tailDet _ _ _ otherRead
    generalize h : Arith.add.token = token at otherRead
    cases otherRead with
    | stop blocked =>
      exact (blocked ⟨.arith .add, _, congrArg (· :: _) h.symm, allowed⟩).elim
    | textConcat _ _ _ otherRight otherTail =>
      obtain ⟨same, rfl⟩ := rightDet otherRight
      cases same
      exact tailDet otherTail
    | _ => cases h
  case textIndex =>
    intros
    rename_i allowed indexRead tailRead indexDet tailDet _ _ _ otherRead
    cases otherRead with
    | stop blocked => exact (blocked ⟨.index, _, rfl, allowed⟩).elim
    | textIndex _ _ _ otherIndex otherTail =>
      obtain ⟨same, suffix⟩ := indexDet otherIndex
      cases same
      cases (List.cons.inj suffix).2
      exact tailDet otherTail
    | substring _ _ _ _ otherFirst _ _ =>
      exact (by obtain ⟨_, suffix⟩ := indexDet otherFirst; cases suffix)
  case substring =>
    intros
    rename_i allowed firstRead lastRead tailRead firstDet lastDet tailDet _ _ _ otherRead
    cases otherRead with
    | stop blocked => exact (blocked ⟨.index, _, rfl, allowed⟩).elim
    | textIndex _ _ _ otherIndex _ =>
      exact (by obtain ⟨_, suffix⟩ := firstDet otherIndex; cases suffix)
    | substring _ _ _ _ otherFirst otherLast otherTail =>
      obtain ⟨same, firstSuffix⟩ := firstDet otherFirst
      cases same
      cases (List.cons.inj firstSuffix).2
      obtain ⟨same, lastSuffix⟩ := lastDet otherLast
      cases same
      cases (List.cons.inj lastSuffix).2
      exact tailDet otherTail
  case optionIsSome =>
    intros
    rename_i allowed tailRead tailDet _ _ _ otherRead
    cases otherRead with
    | stop blocked => exact (blocked ⟨.projection, _, rfl, allowed⟩).elim
    | optionIsSome _ _ _ _ otherTail => exact tailDet otherTail
  case itemsClose =>
    intros
    rename_i _ _ _ delimiter otherRead
    rcases delimiter with rfl | rfl
    all_goals
      cases otherRead with
      | close => exact ⟨rfl, rfl⟩
      | next exprRead _ =>
        cases exprRead with
        | atom atomRead _ => cases atomRead
  case itemsNext =>
    intros
    rename_i exprRead tailRead exprDet tailDet _ _ _ delimiter otherRead
    cases otherRead with
    | close =>
      rcases delimiter with rfl | rfl
      all_goals
        cases exprRead with
        | atom atomRead _ => cases atomRead
    | next otherExpr otherTail =>
      obtain ⟨same, rfl⟩ := exprDet otherExpr
      cases same
      obtain ⟨same, rfl⟩ := tailDet delimiter otherTail
      cases same
      exact ⟨rfl, rfl⟩
  case itemsTailClose =>
    intros
    rename_i _ _ _ delimiter otherRead
    rcases delimiter with rfl | rfl <;> cases otherRead <;> exact ⟨rfl, rfl⟩
  case itemsTailComma =>
    intros
    rename_i itemsDet _ _ _ delimiter otherRead
    rcases delimiter with rfl | rfl
    all_goals
      cases otherRead with
      | comma _ otherItems =>
        obtain ⟨same, rfl⟩ := itemsDet (by first | exact Or.inl rfl | exact Or.inr rfl) otherItems
        cases same
        exact ⟨rfl, rfl⟩
  case labeledClose =>
    intros
    rename_i otherRead
    cases otherRead
    exact ⟨rfl, rfl⟩
  case labeledNext =>
    intros
    rename_i name exprRead tailRead exprDet tailDet _ _ _ _ otherRead
    generalize hname : name.val = spelling at otherRead
    cases otherRead with
    | next otherName otherExpr otherTail =>
      cases Subtype.ext hname
      obtain ⟨same, rfl⟩ := exprDet otherExpr
      cases same
      obtain ⟨same, rfl⟩ := tailDet otherTail
      cases same
      exact ⟨rfl, rfl⟩
  case labeledTailClose =>
    intros
    rename_i otherRead
    cases otherRead
    exact ⟨rfl, rfl⟩
  case labeledTailComma =>
    intros
    rename_i itemsDet _ _ _ _ otherRead
    cases otherRead with
    | comma _ _ _ otherItems => exact itemsDet otherItems
  case payloadBare =>
    intros
    rename_i closed _ _ _ otherRead
    cases otherRead with
    | bare => exact ⟨rfl, rfl⟩
    | empty => exact (closed _ rfl).elim
    | value _ => exact (closed _ rfl).elim
  case payloadEmpty =>
    intros
    rename_i otherRead
    cases otherRead with
    | bare closed => exact (closed _ rfl).elim
    | empty => exact ⟨rfl, rfl⟩
    | value valueRead =>
      cases valueRead with
      | atom atomRead _ => cases atomRead
  case payloadValue =>
    intros
    rename_i valueRead valueDet _ _ _ otherRead
    cases otherRead with
    | bare closed => exact (closed _ rfl).elim
    | empty =>
      cases valueRead with
      | atom atomRead _ => cases atomRead
    | value otherValue =>
      obtain ⟨same, suffix⟩ := valueDet otherValue
      cases same
      exact ⟨rfl, (List.cons.inj suffix).2⟩
  all_goals intros

end Gabbro.Core.Ast
