/-
  File:      core/Core/Ziel/Korrektheit/Beweise/SicherheitAkzeptiert.lean
  Subject:   THE PROOF of `SicherheitAkzeptiertAussage`, the pinned safety leg of the goal theorem
             (`Core/Ziel/Korrektheit/Zusammensetzung.lean`).

  The leg quantifies over source units `t : Ast.Unit` and asks the four safety properties of the safety unit
  `sicherheitVon (einheitVon P t)`. Elaboration of a unit is `(fragment Ast.Category.unit t).einheit P`, and a unit
  fragment is `programmMitInvarianten ⟨t, []⟩`, whose clause table is the empty denotation list
  (`fragment_unit_invarianten`). Hence `sicherheitVon (einheitVon P t)` is definitionally `(fragment
  Ast.Category.unit t).sicherheitsEinheit P`, and the leg is the instance of `fragment_sicher` at that fragment
  with the empty predicate list (the checker accepts it by `pruefeEinheit_leer`). The boundary obligations are
  discharged by `arithmetik_grenzen` (the elaborated loader) and the rule duties by
  `Befehl.sicherheitsPflichten`; acceptance is stronger than needed and is not used. Units with declared
  invariants are the content of `InvariantenSicherheitAussage`
  (`Core/Ast/Semantik/Runtime/UnitInvarianten.lean`). No statement is changed and no witness or per-program
  fact is used.
-/
module

public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Sicherheit.RegelnErfuellbar
public import Core.Ziel.Korrektheit.Zugriff

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- EVERY RUN OF A UNIT WITH A FRAME-ONLY FRAGMENT IS SAFE. A plain unit declares no invariant, so its safety unit is the
    fragment's safety unit and `fragment_sicher` applies directly. -/
theorem sicherheitAkzeptiert_rein (P : Katalog.Plattform) (t : Ast.Unit)
    (rein : (Ast.Semantik.fragment Ast.Category.unit t).Rein) :
    ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ →
      Gabbro.Core.Sicherheit.Speichersicher (sicherheitVon (einheitVon P t)) H ρ ∧
      Gabbro.Core.Sicherheit.InvariantenErhalten (sicherheitVon (einheitVon P t)) H ρ ∧
      Gabbro.Core.Sicherheit.Rennfrei (sicherheitVon (einheitVon P t)) H ρ ∧
      Gabbro.Core.Sicherheit.ToctouFrei (sicherheitVon (einheitVon P t)) H ρ := by
  intro H ρ lauf
  simpa [einheitVon, Ast.Semantik.elaborieren, sicherheitVon,
    Ast.Semantik.Fragment.sicherheitsEinheit, Ast.Semantik.Fragment.einheit,
    Ast.Semantik.Fragment.tabellen, Ast.Semantik.fragment] using
    (Gabbro.Core.Sicherheit.fragment_sicher (Ast.Semantik.fragment Ast.Category.unit t) P []
      (Ast.Semantik.fragment_unit_invarianten t) (Ast.Semantik.pruefeEinheit_leer _) rein H ρ lauf)

/-- EVERY RUN OF AN ACCEPTED ELABORATED UNIT IS SAFE (the pinned `SicherheitAkzeptiertAussage`). A frame-only fragment by
    `sicherheitAkzeptiert_rein`; a fragment with an access instruction by the pinned `ZugriffSicherAussage`. -/
theorem sicherheitAkzeptiert (P : Katalog.Plattform) (zugriff : Ast.Semantik.ZugriffSicherAussage) :
    SicherheitAkzeptiertAussage P := by
  intro t h H ρ lauf
  by_cases rein : (Ast.Semantik.fragment Ast.Category.unit t).Rein
  · exact sicherheitAkzeptiert_rein P t rein H ρ lauf
  · simpa [einheitVon, Ast.Semantik.elaborieren, sicherheitVon,
      Ast.Semantik.Fragment.sicherheitsEinheit, Ast.Semantik.Fragment.einheit,
      Ast.Semantik.Fragment.tabellen, Ast.Semantik.fragment] using
      (zugriff (Ast.Semantik.fragment Ast.Category.unit t) P [] (Or.inl ⟨⟨t, []⟩, rfl⟩)
        ⟨Ast.Semantik.fragment_klassenrein Ast.Category.unit t, rein⟩
        (Ast.Semantik.fragment_unit_invarianten t) (Ast.Semantik.pruefeEinheit_leer _) H ρ lauf)

end Gabbro.Core.Ziel.Korrektheit
