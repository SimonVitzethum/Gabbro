module

public import Core.Ast.Expression.PrintTokens

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

private theorem noOperatorAtSliceRange : ¬ Continues minimum (sliceRange :: more) := by
  rintro ⟨op, _, same, _⟩
  have head := (List.cons.inj same).1
  cases op with
  | arith a => cases a <;> cases head
  | compare c => cases c <;> cases head
  | logic l => cases l <;> cases head
  | _ => cases head

-- Extend the original Expr.printAtom using the leaf or grouped productions.
theorem Expr.printAtom (tree : Expr scope type) (rest : List Token) :
    AtomReads scope (tree.printTokens ++ rest) tree rest := by
  revert rest
  have openToken : printOpen.value = openParen := rfl
  have closeToken : printClose.value = closeParen := rfl
  have openBracketToken : printOpenBracket.value = openBracket := rfl
  have closeBracketToken : printCloseBracket.value = closeBracket := rfl
  have dotToken : printDot.value = dot := rfl
  have commaToken : printComma.value = comma := rfl
  have colonToken : printColon.value = colon := rfl
  have sliceToken : printSliceRange.value = sliceRange := rfl
  have lenofToken : printLenof.value = lenofKeyword := rfl
  have nameToken (name : Identifier) : name.print.value = .word name.val := rfl
  have integerToken (value : Nat) : (printInteger value).value = .natural value := rfl
  refine @Expr.rec scope
    (fun _ node => ∀ rest, AtomReads scope (node.printTokens ++ rest) node rest)
    (fun _ items => ∀ close rest, (¬ Continues 0 (close :: rest)) →
      ItemsRead scope close (items.printPieces.map PrintedToken.value ++ close :: rest) items rest ∧
      ItemsTail scope close (items.printTail.map PrintedToken.value ++ close :: rest) items rest)
    (fun _ _ items => ∀ rest,
      LabeledItemsRead scope (items.printPieces.map PrintedToken.value ++ closeParen :: rest) items rest ∧
      LabeledItemsTail scope (items.printTail.map PrintedToken.value ++ closeParen :: rest) items rest)
    (fun _ payload => ∀ rest, (∀ tail, rest ≠ openParen :: tail) →
      CasePayloadRead scope (payload.printPieces.map PrintedToken.value ++ rest) payload rest)
    ?lit ?binary ?trueLit ?falseLit ?«variable» ?negativeLit ?neg ?not ?div ?compare ?logic
    ?arrayValue ?arrayIndex ?tupleValue ?tupleField ?recordValue ?recordField ?variantValue
    ?textLiteral ?textConcat ?textIndex ?substring ?textLength ?optionIsSome
    ?itemsEmpty ?itemsNext ?labeledEmpty ?labeledNext ?payloadNullary ?payloadValue type tree
  case lit =>
    intro value rest
    exact .lit
  case binary =>
    intros
    rename_i op left right leftIH rightIH rest
    simp only [Expr.printTokens, Expr.printPieces, printOpen, printClose, printPunctuation, PrintedToken.unquoted, Arith.print_value, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc]
    apply AtomReads.grouped
    apply ExprReads.atom (leftIH (op.token :: right.printTokens ++ closeParen :: rest))
    exact .binary op (Nat.zero_le _) (.atom (rightIH (closeParen :: rest))
      (.stop noOperatorAtClose)) (.stop noOperatorAtClose)
  case trueLit =>
    intro rest
    exact .trueLit
  case falseLit =>
    intro rest
    exact .falseLit
  case «variable» =>
    intros
    rename_i ref visible ordinary rest
    exact .variable ref visible ordinary
  case negativeLit =>
    intro magnitude rest
    exact .negativeLit
  case neg =>
    intros
    rename_i operand operandIH rest
    have start : NegationStart (openParen :: operand.printTokens ++ closeParen :: rest) := by
      refine ⟨?_, ?_⟩
      · intro tail
        constructor <;> intro h <;> cases h
      · intro n tail h
        cases h
    simp only [Expr.printTokens, Expr.printPieces, printOpen, printClose, printPunctuation, PrintedToken.unquoted, Arith.print_value, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc]
    exact .neg start (.grouped (ExprReads.atom (operandIH (closeParen :: rest))
      (.stop noOperatorAtClose)))
  case not =>
    intros
    rename_i operand operandIH rest
    have primary : PrimaryStart (openParen :: operand.printTokens ++ closeParen :: rest) := by
      intro tail
      constructor <;> intro h <;> cases h
    simp only [Expr.printTokens, Expr.printPieces, printOpen, printClose, printPunctuation, PrintedToken.unquoted, Arith.print_value, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc]
    exact .not primary (.grouped (ExprReads.atom (operandIH (closeParen :: rest))
      (.stop noOperatorAtClose)))
  case div =>
    intros
    rename_i left right nonzero leftIH rightIH rest
    simp only [Expr.printTokens, Expr.printPieces, printOpen, printClose, printPunctuation, PrintedToken.unquoted, PrintedToken.slash, Arith.print_value, List.map_append, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.append_assoc]
    apply AtomReads.grouped
    apply ExprReads.atom (leftIH (Infix.div.token :: right.printTokens ++ closeParen :: rest))
    exact .div (Nat.zero_le _) (.atom (rightIH (closeParen :: rest))
      (.stop noOperatorAtClose)) nonzero (.stop noOperatorAtClose)
  case compare =>
    intros
    rename_i op left right leftIH rightIH rest
    simp only [Expr.printTokens, Expr.printPieces, printOpen, printClose, printPunctuation, PrintedToken.unquoted, Arith.print_value, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc]
    apply AtomReads.grouped
    apply ExprReads.atom (leftIH ((Infix.compare op).token :: right.printTokens ++ closeParen :: rest))
    refine .compare op (Nat.zero_le _) (.atom (rightIH (closeParen :: rest))
      (.stop noOperatorAtClose)) ?_ (.stop noOperatorAtClose)
    intro op' tail h
    have head := (List.cons.inj h).1
    cases op' <;> simp only [Infix.token, Compare.spelling, String.reduceToList] at head <;> cases head
  case logic =>
    intros
    rename_i op left right leftIH rightIH rest
    simp only [Expr.printTokens, Expr.printPieces, printOpen, printClose, printPunctuation, PrintedToken.unquoted, Arith.print_value, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc]
    apply AtomReads.grouped
    apply ExprReads.atom (leftIH ((Infix.logic op).token :: right.printTokens ++ closeParen :: rest))
    exact .logic op (Nat.zero_le _) (.atom (rightIH (closeParen :: rest))
      (.stop noOperatorAtClose)) (.stop noOperatorAtClose)

  case arrayValue =>
    intros
    rename_i items principal fits ih rest
    have read := (ih closeBracket rest noOperatorAtCloseBracket).1
    simpa only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc, openBracketToken, closeBracketToken] using
      (AtomReads.arrayValue principal fits read)
  case arrayIndex =>
    intros
    rename_i base index loBound hiBound baseIH indexIH rest
    have baseRead := baseIH (openBracket :: index.printTokens ++ closeBracket :: closeParen :: rest)
    have indexRead := ExprReads.atom (minimum := 0) (indexIH (closeBracket :: closeParen :: rest))
      (.stop noOperatorAtCloseBracket)
    simpa only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc, openToken, closeToken, openBracketToken, closeBracketToken] using
      (AtomReads.grouped (.atom baseRead (.arrayIndex base loBound hiBound (Nat.zero_le _)
        indexRead (.stop noOperatorAtClose))))
  case tupleValue =>
    intros
    rename_i first second items firstIH secondIH itemsIH rest
    let tail := items.printTail.map PrintedToken.value ++ closeParen :: rest
    have blocked : ¬ Continues 0 tail := by
      cases items with
      | empty => exact noOperatorAtClose
      | next _ _ => exact noOperatorAtComma
    have firstRead := ExprReads.atom (minimum := 0) (firstIH (comma :: second.printTokens ++ tail))
      (.stop noOperatorAtComma)
    have secondRead := ExprReads.atom (secondIH tail) (.stop blocked)
    have tailRead := (itemsIH closeParen rest noOperatorAtClose).2
    simpa only [Expr.printTokens, Expr.printPieces, tail, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append, openToken, commaToken, closeToken] using
      (AtomReads.tupleValue firstRead secondRead tailRead)
  case tupleField =>
    intros
    rename_i base index baseIH rest
    simpa only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc, openToken, closeToken, dotToken, integerToken] using
      (AtomReads.grouped (.atom (baseIH (dot :: .natural index.val :: closeParen :: rest))
        (.tupleField base index (Nat.zero_le _) (.stop noOperatorAtClose))))
  case recordValue =>
    intros
    rename_i ref args fields fits argsIH rest
    simpa only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc, nameToken, openToken, closeToken] using
      (AtomReads.recordValue ref fields fits (argsIH rest).1)
  case recordField =>
    intros
    rename_i base field index written baseIH rest
    simpa only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc, openToken, closeToken, dotToken, nameToken] using
      (AtomReads.grouped (.atom (baseIH (dot :: .word field.val :: closeParen :: rest))
        (.recordField base field index written (Nat.zero_le _) (.stop noOperatorAtClose))))
  case variantValue =>
    intros
    rename_i ref label index written ordinary available payload ih rest
    have valueRead := ih (closeParen :: rest) (fun _ impossible => by cases impossible)
    simpa only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc, openToken, closeToken, nameToken] using
      (AtomReads.grouped (.atom (.variantValue ref label index written ordinary available payload valueRead)
        (.stop noOperatorAtClose)))
  case textLiteral =>
    intros
    exact .textLiteral
  case textConcat =>
    intros
    rename_i left right leftIH rightIH rest
    have leftRead := leftIH (Arith.add.token :: right.printTokens ++ closeParen :: rest)
    have rightRead := ExprReads.atom (minimum := Arith.add.precedence + 1) (rightIH (closeParen :: rest)) (.stop noOperatorAtClose)
    simpa only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc, openToken, closeToken, Arith.print_value] using
      (AtomReads.grouped (.atom leftRead (.textConcat left right (Nat.zero_le _) rightRead (.stop noOperatorAtClose))))
  case textIndex =>
    intros
    rename_i base offset baseIH offsetIH rest
    have baseRead := baseIH (openBracket :: offset.printTokens ++ closeBracket :: closeParen :: rest)
    have offsetRead := ExprReads.atom (minimum := 0) (offsetIH (closeBracket :: closeParen :: rest))
      (.stop noOperatorAtCloseBracket)
    simpa only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc, openToken, closeToken, openBracketToken, closeBracketToken] using
      (AtomReads.grouped (.atom baseRead (.textIndex base offset (Nat.zero_le _)
        offsetRead (.stop noOperatorAtClose))))
  case substring =>
    intros
    rename_i base first last baseIH firstIH lastIH rest
    let lastInput := last.printTokens ++ (closeBracket :: closeParen :: rest)
    let firstInput := first.printTokens ++ (sliceRange :: lastInput)
    have baseRead := baseIH (openBracket :: firstInput)
    have firstRead := ExprReads.atom (minimum := 0)
      (firstIH (sliceRange :: lastInput))
      (.stop noOperatorAtSliceRange)
    have lastRead := ExprReads.atom (minimum := 0) (lastIH (closeBracket :: closeParen :: rest)) (.stop noOperatorAtCloseBracket)
    simpa only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc, openToken, closeToken, openBracketToken, closeBracketToken, sliceToken, firstInput, lastInput] using
      (AtomReads.grouped (.atom baseRead (.substring base first last (Nat.zero_le _)
        firstRead lastRead (.stop noOperatorAtClose))))
  case textLength =>
    intros
    rename_i base baseIH rest
    simpa only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc, lenofToken, openToken, closeToken] using
      (AtomReads.textLength (.atom (baseIH (closeParen :: rest)) (.stop noOperatorAtClose)))
  case optionIsSome =>
    intros
    rename_i ref visible ordinary rest
    exact .grouped (.atom (.variable ref visible ordinary)
      (.optionIsSome ref visible ordinary (Nat.zero_le _) (.stop noOperatorAtClose)))
  case itemsEmpty =>
    intro close rest _
    exact ⟨.close, .close⟩
  case itemsNext =>
    intros
    rename_i head tail headIH tailIH close rest blocked
    let more := tail.printTail.map PrintedToken.value ++ close :: rest
    have suffixBlocked : ¬ Continues 0 more := by
      cases tail with
      | empty => exact blocked
      | next _ _ => exact noOperatorAtComma
    have headRead := ExprReads.atom (headIH more) (.stop suffixBlocked)
    have tailRead := (tailIH close rest blocked).2
    have read := ItemsRead.next headRead tailRead
    constructor
    · simpa only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc, ExprItems.printPieces, more] using read
    · simpa only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc, ExprItems.printTail, more, commaToken] using
        (ItemsTail.comma (Or.inl (by intro h; cases h)) read)
  case labeledEmpty =>
    intro rest
    exact ⟨.close, .close⟩
  case labeledNext =>
    intros
    rename_i label value tail valueIH tailIH rest
    let more := tail.printTail.map PrintedToken.value ++ closeParen :: rest
    have blocked : ¬ Continues 0 more := by
      cases tail with
      | empty => exact noOperatorAtClose
      | next _ _ _ => exact noOperatorAtComma
    have valueRead := ExprReads.atom (valueIH more) (.stop blocked)
    have read := LabeledItemsRead.next label valueRead (tailIH rest).2
    constructor
    · simpa only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc, LabeledItems.printPieces, more, nameToken, colonToken] using read
    · simpa only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc, LabeledItems.printTail, more, commaToken, nameToken, colonToken] using
        (LabeledItemsTail.comma label value tail read)
  case payloadNullary =>
    intro parens rest closed
    cases parens with
    | false => exact .bare closed
    | true => exact .empty
  case payloadValue =>
    intros
    rename_i value valueIH rest _
    simpa only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc, CasePayload.printPieces, openToken, closeToken] using
      (CasePayloadRead.value (.atom (valueIH (closeParen :: rest)) (.stop noOperatorAtClose)))

theorem Expr.printReads (tree : Expr scope type) (blocked : ¬ Continues minimum rest) :
    ExprReads scope minimum (tree.printTokens ++ rest) tree rest :=
  .atom (tree.printAtom rest) (.stop blocked)

end Gabbro.Core.Ast
