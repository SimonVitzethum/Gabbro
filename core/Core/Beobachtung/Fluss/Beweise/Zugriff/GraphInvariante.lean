/-
  The single-run invariant behind `SpeicherGraphKopplungAussage`: a materialised write source at a cell
  exists exactly when a public write of that cell was observed after the last crash boundary. The crash
  case is essential: a restart rebuilds the graph from the restart entry while the low trace keeps the
  whole history, so a plain "write somewhere in the prefix" reading would be false.
-/
module

public import Core.Beobachtung.Fluss.Beweise.Zugriff.GraphBeob
public import Core.Beobachtung.Fluss.Fragment

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl Plan)

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- Every observed memory event that writes is a `speicher` constructor. -/
theorem SchreibBeob_ist_speicher {x : Ort} {ev : NiedrigesEreignis Ort Wert Grund Form}
    (h : SchreibBeob x ev) :
    ∃ a art ort m g1 g2, ev = .speicher a art ort m g1 g2 := by
  cases ev with
  | speicher a art ort m g1 g2 => exact ⟨a, art, ort, m, g1, g2, rfl⟩
  | _ => cases h

/-- The catalogue crash event that the graph machine restarts at. -/
def IstAbsturzEreignis : Ereignis → Bool
  | .persistenz .crash => true
  | _ => false

theorem AbsturzBeob_aussenBeob (E) {event : Ereignis}
    {ev : NiedrigesEreignis Ort Wert Grund Form}
    (hmem : ev ∈ aussenBeob E event) :
    AbsturzBeob ev = true ↔ IstAbsturzEreignis event = true := by
  constructor
  · intro hb
    cases event with
    | persistenz pe =>
      cases pe <;> simp only [aussenBeob, IstAbsturzEreignis] at hb ⊢
      · rw [Option.toList, sichtbar] at hmem
        split at hmem
        · simp only [List.mem_singleton] at hmem
          cases hmem
        · cases hmem
      · rw [Option.toList, sichtbar] at hmem
        split at hmem
        · simp only [List.mem_singleton] at hmem
          cases hmem
        · cases hmem
      · rfl
      · rfl
      · rfl
    | frage q =>
      simp only [IstAbsturzEreignis] 
      rw [aussenBeob, Option.toList, sichtbar] at hmem
      split at hmem
      · simp only [List.mem_singleton] at hmem
        cases hmem
      · cases hmem
    | antwort q =>
      simp only [IstAbsturzEreignis]
      rw [aussenBeob, Option.toList, sichtbar] at hmem
      split at hmem
      · simp only [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hmem | hmem <;> cases hmem
      · simp only [List.mem_append, List.mem_nil] at hmem
    | dma q a =>
      simp only [IstAbsturzEreignis] at hb ⊢
      rw [aussenBeob, Option.toList, sichtbar] at hmem
      simp only [List.mem_cons, List.mem_append, List.mem_nil] at hmem
      rcases hmem with rfl | hmem
      · cases hb
      · split at hmem
        · simp only [List.mem_singleton] at hmem
          cases hmem
        · cases hmem
    | geraet q a | interrupt c irq e | seite q =>
      simp only [aussenBeob, List.mem_singleton, IstAbsturzEreignis] at hmem ⊢
      cases hmem
      cases hb
  · intro hb
    cases event with
    | persistenz pe =>
      cases pe
      · simp only [IstAbsturzEreignis] at hb; cases hb
      · simp only [IstAbsturzEreignis] at hb; cases hb
      · simp only [IstAbsturzEreignis] at hb; cases hb
      · simp only [IstAbsturzEreignis] at hb; cases hb
      · simp only [IstAbsturzEreignis] at hb; cases hb
      · exact by simp only [aussenBeob, List.mem_singleton, AbsturzBeob]
    | frage q | antwort q | dma q a | geraet q a | interrupt c irq e | seite q =>
      simp only [IstAbsturzEreignis] at hb
      cases hb

theorem SchreibBeob_nicht_aussen (E) {event : Ereignis}
    {x : Ort} {ev : NiedrigesEreignis Ort Wert Grund Form}
    (hmem : ev ∈ aussenBeob E event) : SchreibBeob x ev → False := by
  intro hs
  obtain ⟨a, art, ort, m, g1, g2, rfl⟩ := SchreibBeob_ist_speicher hs
  cases event with
  | frage q =>
    rw [aussenBeob, Option.toList, sichtbar] at hmem
    split at hmem
    · simp only [List.mem_singleton] at hmem; cases hmem
    · cases hmem
  | antwort q =>
    rw [aussenBeob, Option.toList, sichtbar] at hmem
    split at hmem
    · simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | hmem <;> cases hmem
    · simp only [List.mem_append, List.mem_nil] at hmem
  | dma q a =>
    rw [aussenBeob, Option.toList, sichtbar] at hmem
    simp only [List.mem_cons, List.mem_append, List.mem_nil] at hmem
    rcases hmem with hmem | hmem
    · cases hmem
    · split at hmem
      · simp only [List.mem_singleton] at hmem; cases hmem
      · cases hmem
  | geraet q a | interrupt c irq e | seite q =>
    simp only [aussenBeob, List.mem_singleton] at hmem
    cases hmem
  | persistenz pe =>
    cases pe <;> simp only [aussenBeob, List.mem_singleton] at hmem
    all_goals
      split at hmem
      · simp only [List.mem_singleton] at hmem; cases hmem
      · cases hmem

end Gabbro.Core.Beobachtung
