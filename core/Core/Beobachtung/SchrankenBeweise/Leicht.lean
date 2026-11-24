/-
  File:      core/Core/Beobachtung/SchrankenBeweise/Leicht.lean
  Subject:   The five light M9 B9/B21 duties pinned in `SchrankenB9B21Pflichten`.
-/
module

public import Core.Beobachtung.SchrankenB9B21Pflichten

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme Gabbro.Core.Ast

/-- A step that grows no context's declared depth preserves the stack bound. -/
theorem stapelErhalten : stapelErhaltenAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E vor nach stapelVor tiefe
  intro c n bound
  exact le_trans (tiefe c) (stapelVor c n bound)

/-- An answer arrival touches only the answer log and the outside history, so both bounds pass
    through unchanged. -/
theorem antwortErhalten : antwortErhaltenAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E k run t a spur s s'
    stapelVor speicherVor schritt
  obtain ⟨_, _, _, stateEq⟩ := schritt
  rw [stateEq]
  exact ⟨stapelVor, speicherVor⟩

/-- An interrupt delivery touches only cores, status and delivered offers, so both bounds pass
    through unchanged. -/
theorem unterbrechungErhalten : unterbrechungErhaltenAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E run t id spur s s'
    stapelVor speicherVor schritt
  obtain ⟨k, irq, c, nmi, _, _, _, _, _, _, stateEq⟩ := schritt
  rw [stateEq]
  exact ⟨stapelVor, speicherVor⟩

/-- The loader duty transfers from the checker row's ideal start across the simulation match
    at cut zero. -/
theorem schrankenStartAusLokal : schrankenStartAusLokalAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form inst E pflicht simulation
  intro h ρ lauf
  intro s load0
  obtain ⟨η, idealLauf, sim⟩ := simulation lauf
  obtain ⟨_, abgleich, _⟩ := sim
  obtain ⟨s0, load0', bezug⟩ := abgleich.zustand 0
  have ideal := pflicht.start idealLauf
  have eq : s = s0 := Option.some.inj (load0.symm.trans load0')
  subst s
  exact ⟨(stapel_bezug pflicht.bezug bezug).mpr ideal.1,
    (speicher_bezug bezug).mpr ideal.2⟩

/-- Non-growing control and scalar forms preserve both bounds from the step footprint. -/
theorem kontrollflussSkalarSchranken : kontrollflussSkalarSchrankenAussage := by
  intro E tiefe b fuss η lauf t c w spur vor nach vorEq kopf spurEq nachEq step
    stapelVor speicherVor
  have footprint := fuss lauf t c w spur vor nach vorEq kopf spurEq nachEq step
  constructor
  · exact stapelErhalten E vor nach stapelVor footprint.1
  · intro n bound
    exact le_trans (Set.encard_le_encard footprint.2) (speicherVor n bound)

end Gabbro.Core.Beobachtung
