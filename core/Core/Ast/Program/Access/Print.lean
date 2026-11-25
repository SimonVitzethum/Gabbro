/-
  File:      core/Core/Ast/Program/Access/Print.lean
  Subject:   THE PRINTER OF THE ACCESS FORMS AND ITS ROUND TRIP (MK-04b): every access form prints to tokens
             that its production reads back (`Access.printReads`), after the head word `mem` that `Stmt.printPieces` adds.
-/
module

public import Core.Ast.Program.Access.Grammar
public import Core.Ast.Program.WrittenTypes
public import Core.Ast.Expression.PrintReads

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

/-- The pieces of an access form, without the head word `mem`. -/
def Access.printPieces : Access before after → List PrintedToken
  | .load name _ written _ region _ _ index mode =>
    [printLoadWord, name.print, printColon] ++ written.printPieces ++
      [printAssignment, region.binding.name.print, printComma] ++ index.printPieces ++
      [printComma, mode.print, printSemicolon]
  | .store region _ _ index value mode =>
    [printStoreWord, region.binding.name.print, printComma] ++ index.printPieces ++ [printComma] ++
      value.printPieces ++ [printComma, mode.print, printSemicolon]
  | .swap name _ written _ region _ _ index value mode =>
    [printSwapWord, name.print, printColon] ++ written.printPieces ++
      [printAssignment, region.binding.name.print, printComma] ++ index.printPieces ++
      [printComma] ++ value.printPieces ++ [printComma, mode.print, printSemicolon]
  | .vergleicheTausche name _ written _ region _ _ index expected neu mode =>
    [printCasWord, name.print, printColon] ++ written.printPieces ++
      [printAssignment, region.binding.name.print, printComma] ++ index.printPieces ++
      [printComma] ++ expected.printPieces ++ [printComma] ++ neu.printPieces ++
      [printComma, mode.print, printSemicolon]
  | .holeUndAddiere name _ written _ region _ _ index betrag mode =>
    [printFetchAddWord, name.print, printColon] ++ written.printPieces ++
      [printAssignment, region.binding.name.print, printComma] ++ index.printPieces ++
      [printComma] ++ betrag.printPieces ++ [printComma, mode.print, printSemicolon]

theorem ModeReads.print (mode : AccessMode) (more : List Token) :
    ModeReads (mode.print.value :: more) mode more := by
  cases mode
  · exact ModeReads.na
  · exact ModeReads.rlx
  · exact ModeReads.ra
  · exact ModeReads.sc

theorem Access.printReads (tree : Access before after) (rest : List Token) :
    AccessReads before (tree.printPieces.map PrintedToken.value ++ rest) ⟨after, tree⟩ rest := by
  have hpName (name : Identifier) : name.print.value = .word name.val := rfl
  have hpColon : printColon.value = colon := rfl
  have hpAssign : printAssignment.value = assignment := rfl
  have hpComma : printComma.value = comma := rfl
  have hpSemi : printSemicolon.value = semicolon := rfl
  have hpLoad : printLoadWord.value = keyword "load" := rfl
  have hpStore : printStoreWord.value = keyword "store" := rfl
  have hpSwap : printSwapWord.value = keyword "swap" := rfl
  have hpCas : printCasWord.value = keyword "cas" := rfl
  have hpFetchAdd : printFetchAddWord.value = keyword "fetch_add" := rfl
  cases tree with
  | load name ordinary written valid region visible receiverOrdinary index mode =>
    have modeRead := ModeReads.print mode (semicolon :: rest)
    have indexRead := index.printReads (minimum := 0)
      (rest := comma :: mode.print.value :: semicolon :: rest) noOperatorAtComma
    have typeRead := written.printReads valid
      (rest := assignment :: .word region.binding.name.val :: comma ::
        (index.printTokens ++ comma :: mode.print.value :: semicolon :: rest))
      (by intro more h; cases h)
    simpa only [Access.printPieces, Expr.printTokens, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpLoad, hpName, hpColon, hpAssign, hpComma,
      hpSemi] using
      (AccessReads.load name ordinary written valid region visible receiverOrdinary typeRead indexRead modeRead)
  | store region visible receiverOrdinary index value mode =>
    have modeRead := ModeReads.print mode (semicolon :: rest)
    have valueRead := value.printReads (minimum := 0)
      (rest := comma :: mode.print.value :: semicolon :: rest) noOperatorAtComma
    have indexRead := index.printReads (minimum := 0)
      (rest := comma :: (value.printTokens ++ comma :: mode.print.value :: semicolon :: rest)) noOperatorAtComma
    simpa only [Access.printPieces, Expr.printTokens, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpStore, hpName, hpComma, hpSemi] using
      (AccessReads.store region visible receiverOrdinary indexRead valueRead modeRead)
  | swap name ordinary written valid region visible receiverOrdinary index value mode =>
    have modeRead := ModeReads.print mode (semicolon :: rest)
    have valueRead := value.printReads (minimum := 0)
      (rest := comma :: mode.print.value :: semicolon :: rest) noOperatorAtComma
    have indexRead := index.printReads (minimum := 0)
      (rest := comma :: (value.printTokens ++ comma :: mode.print.value :: semicolon :: rest)) noOperatorAtComma
    have typeRead := written.printReads valid
      (rest := assignment :: .word region.binding.name.val :: comma ::
        (index.printTokens ++ (comma :: (value.printTokens ++ comma :: mode.print.value :: semicolon :: rest))))
      (by intro more h; cases h)
    simpa only [Access.printPieces, Expr.printTokens, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpSwap, hpName, hpColon, hpAssign, hpComma,
      hpSemi] using
      (AccessReads.swap name ordinary written valid region visible receiverOrdinary typeRead indexRead valueRead modeRead)
  | vergleicheTausche name ordinary written valid region visible receiverOrdinary index expected neu mode =>
    have modeRead := ModeReads.print mode (semicolon :: rest)
    have neuRead := neu.printReads (minimum := 0)
      (rest := comma :: mode.print.value :: semicolon :: rest) noOperatorAtComma
    have expectedRead := expected.printReads (minimum := 0)
      (rest := comma :: (neu.printTokens ++ comma :: mode.print.value :: semicolon :: rest)) noOperatorAtComma
    have indexRead := index.printReads (minimum := 0)
      (rest := comma :: (expected.printTokens ++ comma ::
        (neu.printTokens ++ comma :: mode.print.value :: semicolon :: rest))) noOperatorAtComma
    have typeRead := written.printReads valid
      (rest := assignment :: .word region.binding.name.val :: comma ::
        (index.printTokens ++ (comma :: (expected.printTokens ++ (comma ::
          (neu.printTokens ++ comma :: mode.print.value :: semicolon :: rest))))))
      (by intro more h; cases h)
    simpa only [Access.printPieces, Expr.printTokens, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpCas, hpName, hpColon, hpAssign, hpComma,
      hpSemi] using
      (AccessReads.vergleicheTausche name ordinary written valid region visible receiverOrdinary
        typeRead indexRead expectedRead neuRead modeRead)
  | holeUndAddiere name ordinary written valid region visible receiverOrdinary index betrag mode =>
    have modeRead := ModeReads.print mode (semicolon :: rest)
    have betragRead := betrag.printReads (minimum := 0)
      (rest := comma :: mode.print.value :: semicolon :: rest) noOperatorAtComma
    have indexRead := index.printReads (minimum := 0)
      (rest := comma :: (betrag.printTokens ++ comma :: mode.print.value :: semicolon :: rest)) noOperatorAtComma
    have typeRead := written.printReads valid
      (rest := assignment :: .word region.binding.name.val :: comma ::
        (index.printTokens ++ (comma :: (betrag.printTokens ++ comma :: mode.print.value :: semicolon :: rest))))
      (by intro more h; cases h)
    simpa only [Access.printPieces, Expr.printTokens, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpFetchAdd, hpName, hpColon, hpAssign, hpComma,
      hpSemi] using
      (AccessReads.holeUndAddiere name ordinary written valid region visible receiverOrdinary
        typeRead indexRead betragRead modeRead)

end Gabbro.Core.Ast
