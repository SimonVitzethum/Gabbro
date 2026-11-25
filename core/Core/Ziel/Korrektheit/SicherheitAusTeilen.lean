/-
  File:      core/Core/Ziel/Korrektheit/SicherheitAusTeilen.lean
  Subject:   THE PROOF of `SicherheitAusTeilenAussage`, the pinned composition of the safety legs
             (`Core/Ziel/Korrektheit/Zusammensetzung.lean`).

  `GabbroSicherheitForm (R₀ P B) (S₀ P B)` has two conjuncts. The first is
  `SicherheitNichtLeerInstanzAussage P B` itself. The second quantifies over source-denoted accepted units `E`
  and their runs. `Bezeichnet P .unit a E` supplies a unit tree `t` with `E = elaborieren P t`, so `E` is
  `einheitVon P t`; the acceptance premise rewrites along that equality and `sicherheitAkzeptiert` gives the
  four properties. No statement is changed and no per-program witness is used.
-/
module

public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Ziel.Korrektheit.Beweise.SicherheitAkzeptiert

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- THE SAFETY THEOREM OVER THE CONCRETE FRAME FOLLOWS FROM ITS TWO LEGS (the pinned
    `SicherheitAusTeilenAussage`). -/
theorem sicherheitAusTeilen (P : Katalog.Plattform) (B : FormBeleg) : SicherheitAusTeilenAussage P B := by
  intro hAkzeptiert hNichtLeer
  refine ⟨hNichtLeer, ?_⟩
  intro a E hBez hE_akzeptiert H _ ρ hρ_laeufe
  obtain ⟨t, _, hElab⟩ := hBez
  have hE : E = einheitVon P t := by
    change E = Ast.Semantik.elaborieren P t
    exact hElab.1
  rcases hρ_laeufe with ⟨hρ, hLauf⟩
  rcases ρ with ⟨E', ρ'⟩
  change E' = E at hρ
  change Maschine.Laeufe E' H ρ' at hLauf
  subst E'
  subst E
  exact hAkzeptiert t hE_akzeptiert H ρ' hLauf

end Gabbro.Core.Ziel.Korrektheit
