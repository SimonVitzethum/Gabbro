module

public import Core.Ast.Program.WrittenTypes
public import Core.Ast.LowLevel.Proofs.Syntax
public import Core.Ast.LowLevel.Proofs.Elaboration
public import Core.Ast.LowLevel.Proofs.Execution
public import Core.Ast.LowLevel.Proofs.Preservation
public import Core.Ast.LowLevel.Proofs.Meaning
public import Core.Ast.LowLevel.Proofs.Satisfiability
public import Core.Ast.LowLevel.Proofs.EnvTypes

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine Waechter
open Gabbro.Core.Ast.Semantik

lemma viewPrints (region : Identifier) (type : WrittenType) (valid : type.valid []) :
    (Tree.view region type).production
      ((Tree.view region type).printPieces.map PrintedToken.value) := by
  refine ⟨type.printPieces.map PrintedToken.value, ?_, ?_⟩
  · simpa only [Tree.printPieces, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, keyword, word, Identifier.print,
      PrintedToken.unquoted, printPunctuation, printDot, dot, String.reduceToList]
  · simpa only [List.append_nil] using
      (WrittenType.printReads (tree := type) (scope := []) (rest := []) valid
        (by intro more h; cases h))

lemma druckAussage_view : DruckAussage .view := by
  intro tree printable
  cases tree with
  | view region type =>
      change type.valid [] at printable
      exact ⟨viewPrints region type printable, parseOfPrint _ (viewPrints region type printable)⟩

theorem view_aussage : ViewAussage := by
  unfold ViewAussage MeaningAussage
  constructor
  · exact ⟨parseAussage .view, inversionAussage .view,
      eindeutigAussage .view, druckAussage_view,
      elaboriert_form .view, realisiert_form .view,
      annahme_form .view, execution_ideal .view,
      execution_einheit .view, execution_impl .view,
      execution_fortschritt .view, erhaltung .view,
      regelSicher .view, regelAntwortSicher .view,
      aussenLokal .view, kosten .view,
      view_erfuellbar⟩
  · exact viewMeaning

def viewTreeEntry : RegistryEntry ``Gabbro.Core.Ast.LowLevel.Tree.view
    (schema ``Gabbro.Core.Ast.LowLevel.Tree.view) := by
  rw [schema,
    if_neg (by
      rw [beq_iff_eq]
      exact differentLabels (a := "view") (b := "addressType")
        (by intro same; simp only [String.reduceEq] at same)),
    if_neg (by
      rw [beq_iff_eq]
      exact differentLabels (a := "view") (b := "regionAddress")
        (by intro same; simp only [String.reduceEq] at same)),
    if_pos (by rw [beq_iff_eq])]
  exact aussageEntry ``Gabbro.Core.Ast.LowLevel.Tree.view .view view_aussage

end Gabbro.Core.Ast.LowLevel
