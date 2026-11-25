/-
  File:      core/Core/Ziel/Korrektheit/Beweise/SicherheitAkzeptiert.lean
  Subject:   THE PROOF of `SicherheitAkzeptiertAussage`, the pinned safety leg of the goal theorem
             (`Core/Ziel/Korrektheit/Zusammensetzung.lean`).

  The leg quantifies over source units `t : Ast.Unit` and asks the four safety properties of the safety unit
  `sicherheitVon (einheitVon P t)`. Elaboration of a unit is `(fragment Ast.Category.unit t).einheit P`, and a
  unit fragment is `programm t`, whose clause table has no declared invariant (`programm_keine_invarianten`).
  Hence `sicherheitVon (einheitVon P t)` is definitionally `(fragment Ast.Category.unit t).sicherheitsEinheit P`,
  and the leg is the instance of `fragment_sicher` at that fragment. The boundary obligations are discharged by
  `arithmetik_grenzen` (the elaborated loader) and the rule duties by `Befehl.sicherheitsPflichten`; acceptance is
  stronger than needed and is not used. No statement is changed and no witness or per-program fact is used.
-/
module

public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Sicherheit.RegelnErfuellbar

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- EVERY RUN OF AN ACCEPTED ELABORATED UNIT IS SAFE (the pinned `SicherheitAkzeptiertAussage`). A unit has no
    declared invariant, so its safety unit is the fragment's safety unit and `fragment_sicher` applies directly. -/
theorem sicherheitAkzeptiert (P : Katalog.Plattform) : SicherheitAkzeptiertAussage P := by
  intro t h H ρ lauf
  simpa [einheitVon, Ast.Semantik.elaborieren, sicherheitVon,
    Ast.Semantik.Fragment.sicherheitsEinheit, Ast.Semantik.Fragment.einheit,
    Ast.Semantik.Fragment.tabellen, Ast.Semantik.fragment] using
    (Gabbro.Core.Sicherheit.fragment_sicher (Ast.Semantik.fragment Ast.Category.unit t) P
      (Ast.Semantik.programm_keine_invarianten t) (Ast.Semantik.fragment_rein Ast.Category.unit t) H ρ lauf)

end Gabbro.Core.Ziel.Korrektheit
