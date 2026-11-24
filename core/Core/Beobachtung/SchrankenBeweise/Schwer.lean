/-
  File:      core/Core/Beobachtung/SchrankenBeweise/Schwer.lean
  Subject:   The hard M9 B9/B21 bridge duty pinned in `SchrankenB9B21Pflichten`.

  The bridge duty moves the ideal bounds at cut `t + 1` across the run relation to
  the concrete post-state of any matched form step; the simulation hypothesis supplies
  the whole-run relation, so the step-level match itself needs no second analysis.
-/
module

public import Core.Beobachtung.SchrankenB9B21Pflichten
public import Core.Annahme.Schranken

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme Gabbro.Core.Ast

/-- Every implementation form step inherits the bounds already proved for the aligned
    ideal cut `t + 1`: the simulation relation connects that cut to the concrete
    post-state, and both legs move across it. -/
theorem schrankenRegelAusLokal : schrankenRegelAusLokalAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form instL
  intro E f pflicht simHyp regelSim
  intro h ρ lauf t c w spur vor nach
    vorEq kopf spurEq nachEq step stapelVor speicherVor
  obtain ⟨η, idealLauf, sim⟩ := simHyp lauf
  rcases sim with ⟨ordnung, matched, rest⟩
  have idealBounds := schranken_prefix_aus_lokal pflicht idealLauf (t + 1)
  obtain ⟨sNext, nextEq, bezugNach⟩ := matched.zustand (t + 1)
  have sNextEq : sNext = nach := Option.some.inj (nextEq.symm.trans nachEq)
  rw [sNextEq] at bezugNach
  exact ⟨(stapel_bezug pflicht.bezug bezugNach).mpr idealBounds.1,
    (speicher_bezug bezugNach).mpr idealBounds.2⟩
