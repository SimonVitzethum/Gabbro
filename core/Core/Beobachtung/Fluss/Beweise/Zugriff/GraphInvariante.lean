/-
  The single-run invariant behind `SpeicherGraphKopplungAussage`: a materialised write source at a cell
  exists exactly when a public write of that cell was observed after the last crash boundary. A restart
  rebuilds the graph while the low trace keeps the whole history, so a plain prefix reading is false.
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

theorem SchreibBeob_nicht_aussen
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    {event : Ereignis} {x : Ort} {ev : NiedrigesEreignis Ort Wert Grund Form}
    (hmem : ev ∈ aussenBeob E event) : SchreibBeob x ev → False := by
  intro hs
  obtain ⟨a, art, ort, m, g1, g2, rfl⟩ := SchreibBeob_ist_speicher hs
  cases event with
  | frage q =>
    simp only [aussenBeob, sichtbar, Option.toList, List.mem_singleton] at hmem
    split at hmem
    · cases hmem
    · cases hmem
  | antwort q =>
    simp only [aussenBeob, sichtbar, Option.toList, List.mem_append, List.mem_singleton,
      List.mem_nil] at hmem
    split at hmem <;> split at hmem
    all_goals cases hmem
  | dma q a =>
    simp only [aussenBeob, sichtbar, Option.toList, List.mem_cons, List.mem_append,
      List.mem_singleton, List.mem_nil] at hmem
    cases hmem
    split at hmem
    · cases hmem
    · cases hmem
  | geraet q a | interrupt c irq e | seite q =>
    simp only [aussenBeob, List.mem_singleton] at hmem
    cases hmem
  | persistenz pe =>
    cases pe <;> simp only [aussenBeob, sichtbar, Option.toList, List.mem_singleton] at hmem
    all_goals
      split at hmem
      · cases hmem
      · cases hmem

end Gabbro.Core.Beobachtung
