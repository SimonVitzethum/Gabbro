/-
  File:      core/Core/Aussen/Frage/Beweise.lean
  Subject:   THE OUTSIDE-QUESTION PROOFS (MK-06, design). Every statement of
             `Aussen/Frage/Aussagen` that the current model already decides is proved here
             from the machine lemmas (`antwort_global`, `verbrauch_lokal`), the commit
             lemmas (`atomar_gueltig`, `fruehere_antwort_ungueltig`, `gueltig_erfuellbar`,
             `ungueltig_erfuellbar`), the provenance lemmas (`abgeleitet_traegt`,
             `propagierung_monoton`, `provenienz_erfuellbar`) and the float lemmas
             (`gleit_erfuellbar`, `rechne` by shape). The step-level enforcement for the new
             `verbrauche` class stays follow-up work and is decomposed in the design report.
-/
module

public import Core.Aussen.Frage.Aussagen
public import Core.Katalog.Aussen
public import Core.Katalog.Lauf

@[expose] public section

namespace Gabbro.Core.Aussenfrage

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Aussen

/-- Questions leave in program order, arrival is global, consumption is local. -/
theorem frageSim : FrageSimAussage := by
  refine ⟨?_, ?_, ?_⟩
  · intro L Ort Wert Raum Lok Grund z t c q
    rfl
  · intro L Ort Wert Raum Lok Grund z a
    exact Zustand.antwort_global z a
  · intro L Ort Wert Raum Lok Grund z c
    exact Zustand.verbrauch_lokal z c

/-- The order/global/local facts hold on every state. -/
theorem frageSim_erfuellbar : FrageSimErfuellbarAussage :=
  frageSim

/-- The same question may receive two different answers. -/
theorem frageSim_nichtTrivial : FrageSimNichtTrivialAussage := by
  let q : Frage := ⟨.hosted, ⟨0, ⟨⟨.hosted, 0⟩, 0⟩, [.read]⟩, [], .read⟩
  refine ⟨q, ⟨⟨⟨.hosted, 0⟩, 0⟩, [], .ok (.data [])⟩,
    ⟨⟨⟨.hosted, 0⟩, 0⟩, [], .error .staleOrDenied⟩, ?_⟩
  intro h
  cases h

/-- A successful atomic answer is valid at commit; an effect resting only on an earlier
    answer is refused on a changed outside. -/
theorem gueltigBeiCommitPflicht : GueltigBeiCommitPflichtAussage :=
  ⟨fun p s q a h1 h2 => atomar_gueltig h1 h2,
    fun p s₁ q t mem ninstabil => fruehere_antwort_ungueltig p s₁ q t mem ninstabil⟩

/-- A hosted read is valid at commit. -/
theorem gueltigBeiCommit_erfuellbar : GueltigBeiCommitErfuellbarAussage :=
  fun p bytes => gueltig_erfuellbar p bytes

/-- An earlier hosted answer succeeds, and the same question is invalid on a changed
    outside with no row stability. -/
theorem gueltigBeiCommit_nichtTrivial : GueltigBeiCommitNichtTrivialAussage :=
  fun p => ungueltig_erfuellbar p []

/-- Propagation only grows the label; every derived value carries its provenance. -/
theorem provenienzTraegt : ProvenienzTraegtAussage :=
  ⟨fun u a h => abgeleitet_traegt u a h, fun step q h => propagierung_monoton step q h⟩

/-- A value read from a hosted answer carries that answer's provenance. -/
theorem provenienzTraegt_erfuellbar : ProvenienzTraegtErfuellbarAussage :=
  provenienz_erfuellbar

/-- A derived value carries its answer's provenance while a fresh value carries none. -/
theorem provenienzTraegt_nichtTrivial : ProvenienzTraegtNichtTrivialAussage := by
  let a : Antwort := ⟨⟨⟨.hosted, 0⟩, 0⟩, [], .ok (.data [])⟩
  refine ⟨a, ausAntwort a 0, rein 1, Abgeleitet.direkt a 0, rfl, ?_⟩
  intro h
  cases h

/-- The reference hardware answers every question kind with the matching answer kind. -/
theorem gleitAntwortZulaessig : GleitAntwortZulaessigAussage := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro op a b
    exact ⟨_, rfl⟩
  · intro op a b
    exact ⟨_, rfl⟩
  · intro a
    exact ⟨_, rfl⟩
  · intro a b c
    exact ⟨_, rfl⟩
  · intro n
    exact ⟨_, rfl⟩
  · intro op a b
    exact ⟨_, rfl⟩
  · intro op a b
    exact ⟨_, rfl⟩
  · intro a
    exact ⟨_, rfl⟩
  · intro a b c
    exact ⟨_, rfl⟩
  · intro n
    exact ⟨_, rfl⟩

/-- Conformant float hardware exists. -/
theorem gleitAntwort_erfuellbar : GleitAntwortErfuellbarAussage :=
  gleit_erfuellbar

/-- A bits answer is never equal to a truth answer, in either width. -/
theorem gleitAntwort_nichtTrivial : GleitAntwortNichtTrivialAussage := by
  constructor
  · intro x b h
    cases h
  · intro x b h
    cases h

/-- **The pinned root holds.** -/
theorem aussenFrageAussagen : AussenFrageAussagen :=
  ⟨frageSim, gueltigBeiCommitPflicht, provenienzTraegt, gleitAntwortZulaessig⟩

end Gabbro.Core.Aussenfrage
