module

public import Core.Ast.Expression.Resolution

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

theorem ExprTail.tupleProjection
    {base : Expr scope (tupleType (first :: second :: types))}
    (index : Fin (first :: second :: types).length)
    (allowed : minimum ≤ Infix.projection.precedence)
    (read : ExprTail scope minimum (inputType := inputType) other
      (dot :: .natural index.val :: input) tree rest)
    (sameBase : other.typed = base.typed) :
    ExprTail scope minimum (.tupleField base index) input tree rest := by
  generalize ht : (dot :: Token.natural index.val :: input) = tokens at read
  cases read with
  | stop blocked => exact (blocked ⟨.projection, _, ht.symm, allowed⟩).elim
  | tupleField otherBase otherIndex _ tail =>
    have sameType := congrArg Sigma.fst sameBase
    have sameShape := tupleType_injective sameType
    injection sameShape with hf hs
    injection hs with hs hs'
    cases hf
    cases hs
    cases hs'
    have htail := (List.cons.inj ht).2
    have sameIndex : index = otherIndex := Fin.ext (Token.natural.inj (List.cons.inj htail).1)
    have sameInput := (List.cons.inj htail).2
    cases sameIndex
    cases sameInput
    cases sameBase
    exact tail
  | _ =>
    have htype := congrArg Sigma.fst sameBase
    cases htype

theorem ExprTail.recordProjection
    {base : Expr scope (recordValueType name labels types)}
    (field : Identifier) (index : Fin types.length) (written : RecordFieldAt labels field index.val)
    (allowed : minimum ≤ Infix.projection.precedence)
    (read : ExprTail scope minimum (inputType := inputType) other
      (dot :: .word field.val :: input) tree rest)
    (sameBase : other.typed = base.typed) :
    ExprTail scope minimum (.recordField base field index written) input tree rest := by
  generalize ht : (dot :: Token.word field.val :: input) = tokens at read
  cases read with
  | stop blocked => exact (blocked ⟨.projection, _, ht.symm, allowed⟩).elim
  | recordField otherBase otherField otherIndex otherWritten _ tail =>
    have sameType := congrArg Sigma.fst sameBase
    injection sameType with hn hl hs
    cases hn
    cases identifierList_injective hl
    cases tupleType_injective hs
    have tokenTail := (List.cons.inj ht).2
    have sameField : field = otherField := Subtype.ext (Token.word.inj (List.cons.inj tokenTail).1)
    have sameInput := (List.cons.inj tokenTail).2
    cases sameField
    have sameIndex : index = otherIndex :=
      Fin.ext (identifierPosition_unique written.1 written.2 otherWritten.2)
    cases sameIndex
    cases sameInput
    cases sameBase
    exact tail
  | _ =>
    have htype := congrArg Sigma.fst sameBase
    cases htype

private theorem indexOptionType_injective (same : indexOptionType a = indexOptionType b) : a = b := by
  have endpoint : (a : Int) - 1 = (b : Int) - 1 := by
    injection same with _ _ _ layout
    injection layout with payload _
    injection payload
  omega

theorem ExprTail.optionProjection
    (ref : Local scope (indexOptionType count)) (visible : ref.visible)
    (ordinary : ordinaryLocal ref.binding.name) (allowed : minimum ≤ Infix.projection.precedence)
    (read : ExprTail scope minimum (inputType := inputType) other
      (dot :: .word indexIsSomeName.val :: openParen :: closeParen :: input) tree rest)
    (sameBase : other.typed = (Expr.variable ref visible ordinary).typed) :
    ExprTail scope minimum (.optionIsSome ref visible ordinary) input tree rest := by
  generalize ht : (dot :: Token.word indexIsSomeName.val :: openParen :: closeParen :: input) = tokens at read
  cases read with
  | stop blocked => exact (blocked ⟨.projection, _, ht.symm, allowed⟩).elim
  | optionIsSome otherRef otherVisible otherOrdinary _ tail =>
    have sameType := congrArg Sigma.fst sameBase
    cases indexOptionType_injective sameType
    have sameInput := (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj ht).2).2).2).2
    cases sameInput
    have sameRef : otherRef = ref := by
      injection sameBase with _ hexpr
      injection hexpr
    cases sameRef
    exact tail
  | _ =>
    have htype := congrArg Sigma.fst sameBase
    cases htype

end Gabbro.Core.Ast
