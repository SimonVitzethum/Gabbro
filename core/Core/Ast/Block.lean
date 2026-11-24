module

public import Core.Ast.Statement
import Core.Ast.Aggregate.PatternPrint

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def overflowPieces : Option Identifier → List PrintedToken
  | none => []
  | some name => [printOnExceeded, name.print]

def OptionInitializer.printPieces : OptionInitializer scope count → List PrintedToken
  | .absent => [indexNoneName.print]
  | .present value _ => [indexSomeName.print, printOpen] ++ value.printPieces ++ [printClose]

mutual

def Stmt.printPieces : Stmt result before after → List PrintedToken
  | .letValue name _ value =>
    [letName.print, name.print, printAssignment] ++ value.printPieces ++ [printSemicolon]
  | .assignVar ref _ _ value _ =>
    [ref.binding.name.print, printAssignment] ++ value.printPieces ++ [printSemicolon]
  | .ret _ value _ =>
    [returnName.print] ++ value.printPieces ++ [printSemicolon]
  | .ite condition yes no =>
    [ifName.print] ++ condition.printPieces ++ yes.printPieces ++ [elseName.print] ++ no.printPieces

  | .retVoid _ => [returnName.print, printSemicolon]
  | .letMutable name _ written _ value _ =>
    [letName.print, printMut, name.print, printColon] ++ written.printPieces ++
      [printAssignment] ++ value.printPieces ++ [printSemicolon]
  | .directCall call => call.printPieces ++ [printSemicolon]
  | .bindDirect name _ written _ call =>
    [letName.print, name.print, printColon] ++ written.printPieces ++ [printAssignment] ++
      call.printPieces ++ [printSemicolon]
  | .whileBounded condition bound _ _ overflow body =>
    [printWhile] ++ condition.printPieces ++ [printBounded] ++ bound.printPieces ++
      [printOps, printOnExceeded, overflow.print] ++ body.printPieces
  | .forRange name _ lo hi _ overflow body =>
    [printFor, name.print, printIn] ++ lo.printPieces ++ [printOpenRange] ++ hi.printPieces ++
      overflowPieces overflow ++ body.printPieces
  | .tupleBind pattern annotation _ value =>
    [letName.print] ++ pattern.printPieces ++ tupleAnnotationPieces annotation ++
      [printAssignment] ++ value.printPieces ++ [printSemicolon]
  | .assignField ref _ _ field _ _ value _ =>
    [ref.binding.name.print, printDot, field.print, printAssignment] ++ value.printPieces ++ [printSemicolon]
  | .letMutableValue name _ value =>
    [letName.print, printMut, name.print, printAssignment] ++ value.printPieces ++ [printSemicolon]
  | .variantMatch value arms =>
    printMatch :: value.printPieces ++ [printOpenBrace] ++ arms.printPieces ++ [printCloseBrace]
  | .letOption (count := count) mutable name _ carrier _ value =>
    [letName.print] ++ (if mutable then [printMut] else []) ++ [name.print, printColon] ++
      (WrittenType.indexOption carrier count).printPieces ++ [printAssignment] ++
      value.printPieces ++ [printSemicolon]
  | .retOption _ value =>
    [returnName.print] ++ value.printPieces ++ [printSemicolon]

def Block.printItems : Block result before after → List PrintedToken
  | .done => []
  | .step first next => first.printPieces ++ next.printItems

def BracedBlock.printPieces : BracedBlock result before → List PrintedToken
  | .braces body => printOpenBrace :: body.printItems ++ [printCloseBrace]

def VariantArms.printPieces : VariantArms result scope allowed labels payloads → List PrintedToken
  | .done => []
  | .nullary label _ body rest => [label.print, printMatchArrow] ++ body.printPieces ++ rest.printPieces
  | .payload label binder _ body rest =>
    [label.print, printOpen, binder.print, printClose, printMatchArrow] ++ body.printPieces ++ rest.printPieces
  | .wildcard body _ _ => [discardName.print, printMatchArrow] ++ body.printPieces

end

def Stmt.printTokens (tree : Stmt result before after) : List Token :=
  tree.printPieces.map PrintedToken.value

theorem Stmt.printTokens_let (name : Identifier) (ordinary : name.val ≠ "mut".toList)
    (value : Expr scope type) :
    (Stmt.letValue (result := result) name ordinary value).printTokens =
      [letKeyword, .word name.val, assignment] ++ value.printTokens ++ [semicolon] := by
  simp only [Stmt.printTokens, Stmt.printPieces, Expr.printTokens, List.map_append,
    List.map_cons, List.map_nil]
  rfl

private theorem noOperatorAtWord : ¬ Continues minimum (.word word :: rest) := by
  rintro ⟨op, _, same, _⟩
  have head := (List.cons.inj same).1
  cases op with
  | arith a => cases a <;> cases head
  | compare c => cases c <;> cases head
  | logic l => cases l <;> cases head
  | _ => cases head

private theorem noOperatorAtOpenRange : ¬ Continues minimum (openRange :: rest) := by
  rintro ⟨op, _, same, _⟩
  have head := (List.cons.inj same).1
  cases op with
  | arith a => cases a <;> cases head
  | compare c => cases c <;> cases head
  | logic l => cases l <;> cases head
  | _ => cases head

theorem OptionInitializer.printReads (tree : OptionInitializer scope count) (rest : List Token) :
    OptionInitializerReads scope count (tree.printPieces.map PrintedToken.value ++ rest) tree rest := by
  cases tree with
  | absent => exact .absent
  | present value fits =>
    have hpSome : indexSomeName.print.value = .word indexSomeName.val := rfl
    have hpOpen : printOpen.value = openParen := rfl
    have hpClose : printClose.value = closeParen := rfl
    simpa only [OptionInitializer.printPieces, Expr.printTokens, List.map_append, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.append_assoc, hpSome, hpOpen, hpClose] using
      (OptionInitializerReads.present fits
        (value.printReads (minimum := 0) (rest := closeParen :: rest) noOperatorAtClose))

theorem Stmt.printReads (tree : Stmt result before after) (rest : List Token) :
    StmtReads result before (tree.printTokens ++ rest) ⟨after, tree⟩ rest := by
  have hpLet : letName.print.value = letKeyword := rfl
  have hpMut : printMut.value = keyword "mut" := rfl
  have hpName (name : Identifier) : name.print.value = .word name.val := rfl
  have hpColon : printColon.value = colon := rfl
  have hpAssign : printAssignment.value = assignment := rfl
  have hpSemi : printSemicolon.value = semicolon := rfl
  have hpWhile : printWhile.value = keyword "while" := rfl
  have hpBounded : printBounded.value = keyword "bounded" := rfl
  have hpOps : printOps.value = keyword "ops" := rfl
  have hpOverflow : printOnExceeded.value = keyword "on_exceeded" := rfl
  have hpFor : printFor.value = keyword "for" := rfl
  have hpIn : printIn.value = keyword "in" := rfl
  have hpOpenRange : printOpenRange.value = openRange := rfl
  have hpDot : printDot.value = dot := rfl
  have hpMatch : printMatch.value = keyword "match" := rfl
  have hpOpenBrace : printOpenBrace.value = openBrace := rfl
  have hpCloseBrace : printCloseBrace.value = closeBrace := rfl
  have hpReturn : returnName.print.value = returnKeyword := rfl
  have hpArrow : printMatchArrow.value = matchArrow := rfl
  have hpOpen : printOpen.value = openParen := rfl
  have hpClose : printClose.value = closeParen := rfl
  have hpDiscard : discardName.print.value = .word ['_'] := rfl
  refine Stmt.rec
    (motive_1 := fun before after tree => ∀ rest,
      StmtReads result before (tree.printTokens ++ rest) ⟨after, tree⟩ rest)
    (motive_2 := fun before after tree => ∀ rest,
      BlockItems result before (tree.printItems.map PrintedToken.value ++ closeBrace :: rest) ⟨after, tree⟩ rest)
    (motive_3 := fun before tree => ∀ rest,
      BlockReads result before (tree.printPieces.map PrintedToken.value ++ rest) tree rest)
    (motive_4 := fun scope allowed labels payloads arms => ∀ rest,
      VariantArmsRead result scope allowed
        (arms.printPieces.map PrintedToken.value ++ closeBrace :: rest) arms rest)
    ?letValue ?assignVar ?ret ?ite ?retVoid ?letMutable ?directCall ?bindDirect
    ?whileBounded ?forRange ?tupleBind ?assignField ?letMutableValue ?variantMatch ?letOption ?retOption
    ?done ?step ?braced ?armsDone ?armsNullary ?armsPayload ?armsWildcard tree rest
  case letValue =>
    intros
    rename_i before ty name ordinary expr rest
    change StmtReads result before ((Stmt.letValue name ordinary expr).printTokens ++ rest)
      ⟨⟨name, ty, false, false⟩ :: before, Stmt.letValue name ordinary expr⟩ rest
    rw [Stmt.printTokens_let]
    exact .letBinding name ordinary
      (by simpa only [List.append_assoc, List.singleton_append, List.nil_append] using
        (expr.printReads (minimum := 0) (rest := semicolon :: rest) noOperatorAtSemicolon)) .plain
  case assignVar =>
    intros
    rename_i ref visible writable value fits rest
    simp only [Stmt.printTokens, Stmt.printPieces, Expr.printTokens, List.map_append,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc]
    exact .assignVar ref visible writable fits (value.printReads noOperatorAtSemicolon)
  case ret =>
    intros
    rename_i declared value fits rest
    simp only [Stmt.printTokens, Stmt.printPieces, Expr.printTokens, List.map_append,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc]
    exact .ret declared fits (value.printReads noOperatorAtSemicolon)
  case ite =>
    intros
    rename_i condExpr yesBlock noBlock ihYes ihNo rest
    cases yesBlock with
    | braces yesBody =>
    cases noBlock with
    | braces noBody =>
      simp only [Stmt.printTokens, Stmt.printPieces, BracedBlock.printPieces,
        Expr.printTokens, printOpenBrace, printCloseBrace, elseName, Identifier.print,
        printPunctuation, PrintedToken.unquoted, keywordName, String.reduceToList,
        List.map_append, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.append_assoc]
      exact .ite (condExpr.printReads noOperatorAtOpenBrace)
        (by simpa only [BracedBlock.printPieces, elseKeyword, openBrace, closeBrace, printOpenBrace, printCloseBrace,
          printPunctuation, PrintedToken.unquoted, keywordName, String.reduceToList,
          List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
          List.append_assoc] using
          ihYes (elseKeyword :: openBrace :: noBody.printItems.map PrintedToken.value ++ closeBrace :: rest))
        (ihNo rest)
  case done =>
    intros
    rename_i rest
    exact .done
  case step =>
    intros
    rename_i first next ihFirst ihNext rest
    simp only [Block.printItems, List.map_append, List.append_assoc]
    exact .step (ihFirst (next.printItems.map PrintedToken.value ++ closeBrace :: rest)) (ihNext rest)
  case braced =>
    intros
    rename_i body ihBody rest
    simp only [BracedBlock.printPieces, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc]
    exact .braced (ihBody _)

  case retVoid =>
    intros
    rename_i declared rest
    exact .retVoid declared
  case letMutable =>
    intros
    rename_i name ordinary written valid value fits rest
    let rhs := value.printTokens ++ (semicolon :: rest)
    have typeRead := written.printReads valid (rest := assignment :: rhs) (by intro more h; cases h)
    have valueRead := value.printReads (minimum := 0) (rest := semicolon :: rest) noOperatorAtSemicolon
    simpa only [Stmt.printTokens, Stmt.printPieces, Expr.printTokens, List.map_append, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.append_assoc, hpLet, hpMut, hpName, hpColon,
      hpAssign, hpSemi, rhs] using (StmtReads.letMutable name ordinary written valid fits typeRead valueRead)
  case directCall =>
    intros
    rename_i call rest
    have read := call.printReads (rest := semicolon :: rest)
    simpa only [Stmt.printTokens, Stmt.printPieces, List.map_append, List.append_assoc,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, hpSemi] using (StmtReads.directCall read)
  case bindDirect =>
    intros
    rename_i name ordinary written valid call rest
    let rhs := call.printPieces.map PrintedToken.value ++ (semicolon :: rest)
    have typeRead := written.printReads valid (rest := assignment :: rhs) (by intro more h; cases h)
    have callRead := call.printReads (rest := semicolon :: rest)
    simpa only [Stmt.printTokens, Stmt.printPieces, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpLet, hpName, hpColon, hpAssign, hpSemi, rhs] using
      (StmtReads.bindDirect name ordinary written valid typeRead callRead)
  case whileBounded =>
    intros
    rename_i condition bound staticBound nonnegative overflow body ih rest
    let bodyInput := body.printPieces.map PrintedToken.value ++ rest
    let afterBound := keyword "ops" :: keyword "on_exceeded" :: .word overflow.val :: bodyInput
    let boundInput := bound.printTokens ++ afterBound
    have condRead := condition.printReads (minimum := 0) (rest := keyword "bounded" :: boundInput)
      noOperatorAtWord
    have boundRead := bound.printReads (minimum := 0) (rest := afterBound) noOperatorAtWord
    have bodyRead := ih rest
    simpa only [Stmt.printTokens, Stmt.printPieces, Expr.printTokens, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpWhile, hpBounded, hpOps, hpOverflow, hpName,
      bodyInput, afterBound, boundInput] using
      (StmtReads.whileBounded nonnegative overflow bound staticBound condRead boundRead bodyRead)
  case forRange =>
    intros
    rename_i name ordinary lower upper static overflow body ih rest
    let bodyInput := body.printPieces.map PrintedToken.value ++ rest
    let afterUpper := (overflowPieces overflow).map PrintedToken.value ++ bodyInput
    let highInput := upper.printTokens ++ afterUpper
    have bodyHead : ∃ tail, bodyInput = openBrace :: tail := by
      cases body
      exact ⟨_, rfl⟩
    have blocked : ¬ Continues 0 afterUpper := by
      cases overflow with
      | none =>
        obtain ⟨_, h⟩ := bodyHead
        simpa only [afterUpper, overflowPieces, List.map_nil, List.nil_append, h] using
          (noOperatorAtOpenBrace (minimum := 0))
      | some handler =>
        simpa only [afterUpper, overflowPieces, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append, hpOverflow, hpName, keyword] using
          (noOperatorAtWord (minimum := 0) (word := "on_exceeded".toList))
    have handlerRead : OverflowReads afterUpper overflow bodyInput := by
      cases overflow with
      | none =>
        apply OverflowReads.absent
        obtain ⟨_, h⟩ := bodyHead
        intro tail same
        change bodyInput = keyword "on_exceeded" :: tail at same
        rw [h] at same
        cases same
      | some name => exact .named name
    have lowerRead := lower.printReads (minimum := 0) (rest := openRange :: highInput) noOperatorAtOpenRange
    have upperRead := upper.printReads (minimum := 0) (rest := afterUpper) blocked
    simpa only [Stmt.printTokens, Stmt.printPieces, Expr.printTokens, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpFor, hpName, hpIn, hpOpenRange,
      bodyInput, afterUpper, highInput] using
      (StmtReads.forRange name ordinary body lower upper static lowerRead upperRead handlerRead (ih rest))
  case tupleBind =>
    intros
    rename_i pattern annotation checked value rest
    let rhs := value.printTokens ++ (semicolon :: rest)
    let suffix := (tupleAnnotationPieces annotation).map PrintedToken.value ++ (assignment :: rhs)
    have patternRead := pattern.printReads suffix (fun name present => (checked.2.2.1 name present).1)
    have annotationRead := TupleAnnotationReads.printReads annotation rhs
      (fun written present => (checked.2.2.2 written present).1)
    have valueRead := value.printReads (minimum := 0) (rest := semicolon :: rest) noOperatorAtSemicolon
    simpa only [Stmt.printTokens, Stmt.printPieces, Expr.printTokens, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpLet, hpAssign, hpSemi, suffix, rhs] using
      (StmtReads.tupleBind checked patternRead annotationRead valueRead)
  case assignField =>
    intros
    rename_i ref visible writable field index checked value fits rest
    have valueRead := value.printReads (minimum := 0) (rest := semicolon :: rest) noOperatorAtSemicolon
    simpa only [Stmt.printTokens, Stmt.printPieces, Expr.printTokens, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpName, hpDot, hpAssign, hpSemi] using
      (StmtReads.assignField ref visible writable field index checked fits valueRead)
  case letMutableValue =>
    intros
    rename_i name ordinary value rest
    have valueRead := value.printReads (minimum := 0) (rest := semicolon :: rest) noOperatorAtSemicolon
    simpa only [Stmt.printTokens, Stmt.printPieces, Expr.printTokens, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpLet, hpMut, hpName, hpAssign, hpSemi] using
      (StmtReads.letMutableValue name ordinary valueRead)
  case variantMatch =>
    intros
    rename_i value arms ih rest
    let armsInput := arms.printPieces.map PrintedToken.value ++ (closeBrace :: rest)
    have valueRead := value.printReads (minimum := 0) (rest := openBrace :: armsInput) noOperatorAtOpenBrace
    simpa only [Stmt.printTokens, Stmt.printPieces, Expr.printTokens, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpMatch, hpOpenBrace, hpCloseBrace, armsInput] using
      (StmtReads.variantMatch valueRead (ih rest))
  case letOption =>
    intros
    rename_i mutable name ordinary carrier resolved value rest
    let rhs := value.printPieces.map PrintedToken.value ++ (semicolon :: rest)
    have typeRead := (WrittenType.indexOption carrier _).printReads resolved
      (rest := assignment :: rhs) (by intro more h; cases h)
    have valueRead := value.printReads (semicolon :: rest)
    cases mutable with
    | false =>
      simpa only [Stmt.printTokens, Stmt.printPieces, List.map_append, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.append_assoc, hpLet, hpMut, hpName, hpColon, hpAssign, hpSemi,
        optionLetHead, Bool.false_eq_true, if_false, if_true, letKeyword, keyword, colon, rhs] using
        (StmtReads.letOption (result := result) false name ordinary carrier resolved typeRead valueRead)
    | true =>
      simpa only [Stmt.printTokens, Stmt.printPieces, List.map_append, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.append_assoc, hpLet, hpMut, hpName, hpColon, hpAssign, hpSemi,
        optionLetHead, Bool.false_eq_true, if_false, if_true, letKeyword, keyword, colon, rhs] using
        (StmtReads.letOption (result := result) true name ordinary carrier resolved typeRead valueRead)
  case retOption =>
    intros
    rename_i declared value rest
    simpa only [Stmt.printTokens, Stmt.printPieces, List.map_append, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.append_assoc, hpReturn, hpSemi] using
      (StmtReads.retOption declared (value.printReads (semicolon :: rest)))
  case armsDone =>
    intros
    exact .done
  case armsNullary =>
    intros
    rename_i label caseName body tail bodyIH tailIH rest
    have bodyRead := bodyIH (tail.printPieces.map PrintedToken.value ++ (closeBrace :: rest))
    simpa only [VariantArms.printPieces, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpName, hpArrow] using
      (VariantArmsRead.nullary label caseName bodyRead (tailIH rest))
  case armsPayload =>
    intros
    rename_i label binder ordinary body tail bodyIH tailIH rest
    have bodyRead := bodyIH (tail.printPieces.map PrintedToken.value ++ (closeBrace :: rest))
    simpa only [VariantArms.printPieces, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpName, hpOpen, hpClose, hpArrow] using
      (VariantArmsRead.payload label binder ordinary body bodyRead (tailIH rest))
  case armsWildcard =>
    intros
    rename_i body nonempty shape bodyIH rest
    simpa only [VariantArms.printPieces, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, hpDiscard, hpArrow] using
      (VariantArmsRead.wildcard nonempty shape (bodyIH (closeBrace :: rest)))

theorem Block.printItems_reads (tree : Block result before after) (rest : List Token) :
    BlockItems result before (tree.printItems.map PrintedToken.value ++ closeBrace :: rest) ⟨after, tree⟩ rest := by
  match tree with
  | .done => exact .done
  | .step first next =>
    simp only [Block.printItems, List.map_append, List.append_assoc]
    exact .step (first.printReads (next.printItems.map PrintedToken.value ++ closeBrace :: rest))
      (next.printItems_reads rest)
theorem BracedBlock.printReads (tree : BracedBlock result before) (rest : List Token) :
    BlockReads result before (tree.printPieces.map PrintedToken.value ++ rest) tree rest := by
  cases tree with
  | braces body =>
    simp only [BracedBlock.printPieces, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc]
    exact .braced (body.printItems_reads rest)

end Gabbro.Core.Ast
