module

public import Core.Ast.Statement

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

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

theorem Stmt.printReads (tree : Stmt result before after) (rest : List Token) :
    StmtReads result before (tree.printTokens ++ rest) ⟨after, tree⟩ rest := by
  refine Stmt.rec
    (motive_1 := fun before after tree => ∀ rest,
      StmtReads result before (tree.printTokens ++ rest) ⟨after, tree⟩ rest)
    (motive_2 := fun before after tree => ∀ rest,
      BlockItems result before (tree.printItems.map PrintedToken.value ++ closeBrace :: rest) ⟨after, tree⟩ rest)
    (motive_3 := fun before tree => ∀ rest,
      BlockReads result before (tree.printPieces.map PrintedToken.value ++ rest) tree rest)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ tree rest
  · intros
    rename_i before ty name ordinary expr rest
    change StmtReads result before ((Stmt.letValue name ordinary expr).printTokens ++ rest)
      ⟨⟨name, ty, false⟩ :: before, Stmt.letValue name ordinary expr⟩ rest
    rw [Stmt.printTokens_let]
    exact .letBinding name ordinary
      (by simpa using
        (expr.printReads (rest := semicolon :: rest) noOperatorAtSemicolon)) .plain
  · intros
    rename_i ref visible writable value fits rest
    simp only [Stmt.printTokens, Stmt.printPieces, Expr.printTokens, List.map_append,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc]
    exact .assignVar ref visible writable fits (value.printReads noOperatorAtSemicolon)
  · intros
    rename_i declared value fits rest
    simp only [Stmt.printTokens, Stmt.printPieces, Expr.printTokens, List.map_append,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc]
    exact .ret declared fits (value.printReads noOperatorAtSemicolon)
  · intros
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
  · intros
    rename_i rest
    exact .done
  · intros
    rename_i first next ihFirst ihNext rest
    simp only [Block.printItems, List.map_append, List.append_assoc]
    exact .step (ihFirst (next.printItems.map PrintedToken.value ++ closeBrace :: rest)) (ihNext rest)
  · intros
    rename_i body ihBody rest
    simp only [BracedBlock.printPieces, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc]
    exact .braced (ihBody _)

theorem Block.printItems_reads (tree : Block result before after) (rest : List Token) :
    BlockItems result before (tree.printItems.map PrintedToken.value ++ closeBrace :: rest) ⟨after, tree⟩ rest := by
  refine (Block.rec
    (motive_1 := fun before after tree => True)
    (motive_2 := fun before after tree => ∀ rest,
      BlockItems result before (tree.printItems.map PrintedToken.value ++ closeBrace :: rest) ⟨after, tree⟩ rest)
    (motive_3 := fun before tree => ∀ rest,
      BlockReads result before (tree.printPieces.map PrintedToken.value ++ rest) tree rest)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial) ?_ ?_ ?_ tree) rest
  · intros
    rename_i rest
    exact .done
  · intros
    rename_i _ _ first next _ ihBlock rest
    simp only [Block.printItems, List.map_append, List.append_assoc]
    exact .step (Stmt.printReads first (next.printItems.map PrintedToken.value ++ closeBrace :: rest)) (ihBlock rest)
  · intros
    rename_i body ihBody rest
    simp only [BracedBlock.printPieces, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc]
    exact .braced (ihBody rest)

theorem BracedBlock.printReads (tree : BracedBlock result before) (rest : List Token) :
    BlockReads result before (tree.printPieces.map PrintedToken.value ++ rest) tree rest := by
  cases tree with
  | braces body =>
    simp only [BracedBlock.printPieces, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc]
    exact .braced (body.printItems_reads rest)

end Gabbro.Core.Ast
