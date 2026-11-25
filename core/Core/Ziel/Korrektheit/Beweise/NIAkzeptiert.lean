/-
  File:      core/Core/Ziel/Korrektheit/Beweise/NIAkzeptiert.lean
  Subject:   THE PROOF of `NIAkzeptiertAussage`, the pinned noninterference leg of the goal theorem
             (`Core/Ziel/Korrektheit/Zusammensetzung.lean`).

  The statement quantifies over source units `t : Ast.Unit` and asks for noninterference of the
  elaborated unit `einheitVon P t`. Elaboration of a unit is `(fragment Ast.Category.unit t).einheit P`,
  so the leg is an instance of `fragment_nichtinterferent` at the fragment `fragment Ast.Category.unit t`.
  The fragment theorem is proved over all fragments with no open obligations (`FragmentNIBeweise`), and
  acceptance of the elaborated unit is exactly the hypothesis the leg supplies. No statement is changed
  and no witness or per-program fact is used.
-/
module

public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Beobachtung.Fluss.Beweise.Gesamt
public import Core.Ziel.Korrektheit.Zugriff

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Beobachtung

/-- THE ACCEPTED UNIT WITH A FRAME-ONLY FRAGMENT IS NONINTERFERENT. The elaborated unit of a source tree is the unit of its
    fragment, so the fragment theorem applies directly: acceptance is the stated hypothesis and all family and protocol
    duties are discharged by `FragmentNIBeweise`. -/
theorem niAkzeptiert_rein (P : Katalog.Plattform) (t : Ast.Unit)
    (rein : (Ast.Semantik.fragment Ast.Category.unit t).Rein)
    (h : Annahme.Akzeptiert (einheitVon P t)) : Beobachtung.Nichtinterferent (einheitVon P t) :=
  fragment_nichtinterferent (Ast.Semantik.fragment Ast.Category.unit t) P rein h

/-- THE ACCEPTED ELABORATED UNIT IS NONINTERFERENT (the pinned `NIAkzeptiertAussage`). A frame-only fragment by
    `niAkzeptiert_rein`; a fragment with an access instruction by the pinned `ZugriffNIFragmentAussage`. -/
theorem niAkzeptiert (P : Katalog.Plattform) (zugriff : ZugriffNIFragmentAussage) : NIAkzeptiertAussage P := by
  intro t h
  by_cases rein : (Ast.Semantik.fragment Ast.Category.unit t).Rein
  · exact niAkzeptiert_rein P t rein h
  · exact zugriff (Ast.Semantik.fragment Ast.Category.unit t) P
      ⟨Ast.Semantik.fragment_klassenrein Ast.Category.unit t, rein⟩ h

end Gabbro.Core.Ziel.Korrektheit
