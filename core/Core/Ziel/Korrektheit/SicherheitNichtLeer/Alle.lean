/-
  File:      core/Core/Ziel/Korrektheit/SicherheitNichtLeer/Alle.lean
  Subject:   THE PROOF of the pinned `SicherheitNichtLeerInstanzAussage`: the four refutations at
             `Ast.Semantik.Einheit` are wrapped as tag-carrying runs of the concrete frame `R₀`
             and fed to `S₀`. No statement is changed; the frame is independent of the platform and
             the registry evidence, so the four witnesses serve every `P` and `B`.
 -/
module

public import Core.Ziel.Korrektheit.SicherheitNichtLeer.Speicher
public import Core.Ziel.Korrektheit.SicherheitNichtLeer.Invarianten
public import Core.Ziel.Korrektheit.SicherheitNichtLeer.Aussen

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- EACH SAFETY LEG OF THE CONCRETE FRAME IS REFUTABLE (the pinned `SicherheitNichtLeerInstanzAussage`). -/
theorem sicherheitNichtLeerInstanz (P : Katalog.Plattform) (B : FormBeleg) :
    SicherheitNichtLeerInstanzAussage P B := by
  constructor
  · obtain ⟨E, H, ρ, run, bad⟩ := SicherheitNichtLeer.speichersicher_nichtLeerInstanz
    refine ⟨E, H, ⟨E, ρ⟩, ?_, ?_⟩
    · exact ⟨rfl, run⟩
    · exact bad
  constructor
  · obtain ⟨E, H, ρ, run, bad⟩ := SicherheitNichtLeer.invarianten_nichtLeerInstanz
    refine ⟨E, H, ⟨E, ρ⟩, ?_, ?_⟩
    · exact ⟨rfl, run⟩
    · exact bad
  constructor
  · obtain ⟨E, H, ρ, run, bad⟩ := SicherheitNichtLeer.rennfrei_nichtLeerInstanz
    refine ⟨E, H, ⟨E, ρ⟩, ?_, ?_⟩
    · exact ⟨rfl, run⟩
    · exact bad
  · obtain ⟨E, H, ρ, run, bad⟩ := SicherheitNichtLeer.toctoufrei_nichtLeerInstanz
    refine ⟨E, H, ⟨E, ρ⟩, ?_, ?_⟩
    · exact ⟨rfl, run⟩
    · exact bad

end Gabbro.Core.Ziel.Korrektheit
