/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Hebung/Teilbuendel.lean
  Subject:   The satisfiable part of the lift bundle, isolated from the two replay answers.

  Given hardware conformity, a random row and an admissible start, the band measure,
  mass preservation, an admitted replay and causality are all satisfiable: take a
  fixed admitted run for every band. What remains unsatisfied in general is that
  this fixed replay follows an arbitrary scheduler's context choice at every cut
  and stamps random answers with band draws. The structure below makes that split
  explicit without changing the pinned bundle.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Hebung.ZiehungsMass
public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Gabbro.Core.Maschine
open Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]

/-- The bundle without the scheduler-following and draw-stamping fields. -/
structure Teilbuendel (B : Zufallsbindung) (S : Scheduler)
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (h : Umgebung) where
  mu : MeasureTheory.Measure Band
  replay : Band → Maschine.Lauf E
  istWMass : MeasureTheory.IsProbabilityMeasure mu
  massErhalt : ∀ Z : Zylinder B.quelle, (Z.pfad.map Prod.fst).Nodup →
    mu {band : Band | ∀ p ∈ Z.pfad, band B.quelle.id p.1 % B.quelle.anz = p.2.val} =
      ZylinderGewicht B.quelle Z
  replayZulaessig : ∀ band, Maschine.Laeufe E h (replay band)
  replayKausal : KausalReplay replay

/-- The partial bundle exists: the measure comes from `ZiehungsMass`, the replay is a
    single run admitted by the hardware and start, and causality is trivial for a
    constant replay. -/
noncomputable def teilbuendel_erfuellbar (B : Zufallsbindung) (S : Scheduler)
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (h : Umgebung) (hardware : Hardware E.katalog h)
    (start : ∃ s : AussenStart, E.ZulStart h s) : Teilbuendel B S E h := by
  let s := Classical.choose start
  have zul := Classical.choose_spec start
  let rest := lauf_ab_start E hardware zul
  let ρ := Classical.choose rest
  have zulaessig := (Classical.choose_spec rest).1
  let mass := massBuendel_erfuellbar B
  exact
    { mu := mass.mu
      replay := fun _ => ρ
      istWMass := mass.istWMass
      massErhalt := mass.massErhalt
      replayZulaessig := fun _ => zulaessig
      replayKausal := fun _ _ _ _ _ _ => ⟨rfl, rfl⟩ }

end Gabbro.Core.Beobachtung
