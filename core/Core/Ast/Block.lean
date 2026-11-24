module

public import Core.Ast.Statement

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def overflowPieces : Option Identifier → List PrintedToken
  | none => []
  | some name => [printOnExceeded, name.print]

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

def Block.printItems : Block result before after → List PrintedToken
  | .done => []
  | .step first next => first.printPieces ++ next.printItems

def BracedBlock.printPieces : BracedBlock result before → List PrintedToken
  | .braces body => printOpenBrace :: body.printItems ++ [printCloseBrace]

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

-- Extend the original Stmt.printReads using its production for each constructor.
theorem Stmt.printReads (tree : Stmt result before after) (rest : List Token) :
    StmtReads result before (tree.printTokens ++ rest) ⟨after, tree⟩ rest := by
  sorry

-- Use the original Block.printItems_reads recursor mutually with Stmt.printReads.
theorem Block.printItems_reads (tree : Block result before after) (rest : List Token) :
    BlockItems result before (tree.printItems.map PrintedToken.value ++ closeBrace :: rest) ⟨after, tree⟩ rest := by
  sorry

theorem BracedBlock.printReads (tree : BracedBlock result before) (rest : List Token) :
    BlockReads result before (tree.printPieces.map PrintedToken.value ++ rest) tree rest := by
  cases tree with
  | braces body =>
    simp only [BracedBlock.printPieces, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc]
    exact .braced (body.printItems_reads rest)

end Gabbro.Core.Ast
