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

-- Extend the original Stmt.printReads using its production for each constructor.
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
    exact .letBinding name ordinary (by simpa only [List.nil_append, List.append_assoc, List.singleton_append] using (expr.printReads (rest := [semicolon]) noOperatorAtSemicolon)) .plain
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
        Expr.printTokens, List.map_append, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.append_assoc]
      refine .ite (condExpr.printReads noOperatorAtOpenBrace) ?_ ?_
      · exact .braced (yesBody.printItems_reads (elseKeyword :: noBody.printItems.map PrintedToken.value ++ rest))
      · exact .braced (noBody.printItems_reads rest)
  · intro rest
    exact .done
  · intros
    rename_i first next ihFirst ihNext rest
    change BlockItems result before (first.printTokens ++ next.printItems.map PrintedToken.value ++ closeBrace :: rest)
      ⟨after, Block.step first next⟩ rest
    exact .step (ihFirst _) (ihNext _)
  · intros
    rename_i body ihBody rest
    simp only [BracedBlock.printPieces, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc]
    exact .braced (ihBody _)

-- Use the original Block.printItems_reads recursor mutually with Stmt.printReads.
theorem Block.printItems_reads (tree : Block result before after) (rest : List Token) :
    BlockItems result before (tree.printItems.map PrintedToken.value ++ closeBrace :: rest) ⟨after, tree⟩ rest := by
  refine (Block.rec
    (motive_1 := fun before after tree => True)
    (motive_2 := fun before after tree => ∀ rest,
      BlockItems result before (tree.printItems.map PrintedToken.value ++ closeBrace :: rest) ⟨after, tree⟩ rest)
    (motive_3 := fun before tree => ∀ rest,
      BlockReads result before (tree.printPieces.map PrintedToken.value ++ rest) tree rest)
    (by trivial) (by trivial) (by trivial) (by trivial) ?_ ?_ ?_ tree) rest
  · intro rest
    exact .done
  · intros
    rename_i first next ihFirst ihNext rest
    change BlockItems result before (first.printTokens ++ next.printItems.map PrintedToken.value ++ closeBrace :: rest)
      ⟨after, Block.step first next⟩ rest
    exact .step (Stmt.printReads first (next.printItems.map PrintedToken.value ++ closeBrace :: rest)) (ihNext rest)
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
