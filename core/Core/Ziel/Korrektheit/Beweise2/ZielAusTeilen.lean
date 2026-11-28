/-
  File:      core/Core/Ziel/Korrektheit/Beweise2/ZielAusTeilen.lean
  Subject:   Composition of the goal theorem GabbroZielForm (R₀ P B) from its proof obligations.

  The same ideal run carries simulation, answer accounting and progress. The remaining
  progress obligation is return from preemption on fair hardware histories.
-/
module

public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Ziel.Korrektheit.Frontend
public import Core.Ziel.Korrektheit.Verfeinerung
public import Core.Ziel.Korrektheit.Beweise.NIAkzeptiert
public import Core.Ziel.Korrektheit.Beweise2.ZielNI
public import Core.Ziel.Korrektheit.Beweise2.EinheitHerkunft
public import Core.Ziel.Korrektheit.SchrankenAkzeptiert
public import Core.Ziel.Korrektheit.Beweise.Fortschritt.SchedulerEinheit
public import Core.Ziel.Korrektheit.Zugriff
public import Core.Annahme.Annahme
public import Core.Katalog.Erfuellbar
public import Core.Katalog.Start
public import Core.Maschine.Start
public import Core.Fortschritt.Saetze
import Core.Ziel.Korrektheit.Beweise.BildGueltig
import Core.Ziel.Korrektheit.Beweise2.ZugriffSchrittExistiert

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine
open Gabbro.Core.Fortschritt

/-- Every non-vacuity clause of the concrete frame follows from image validity and form coverage. -/
theorem zielAusTeilenNichtLeer (P : Katalog.Plattform) (B : FormBeleg)
    (bildG : BildGueltigAussage P) (formG : FormenGedecktAussage P B) : Ziel.NichtLeer (R₀ P B) := by
  unfold Ziel.NichtLeer
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact text_wohlgeformt P a
  · intro a E E' hE hE'
    exact bezeichnet_funktional P Ast.Category.unit a E E' hE hE'
  · intro f
    obtain ⟨a, E, enthaelt, bezeichnet, akzeptiert, realisiert⟩ := formG f
    have h : Annahme.Quelle.Akzeptiert E := by
      obtain ⟨t, _, elaboriert, _⟩ := bezeichnet
      rw [Ast.Semantik.elab_vollstaendig elaboriert] at akzeptiert ⊢
      exact (Annahme.Quelle.akzeptiert_elaboriert_iff P t).mpr akzeptiert
    exact ⟨a, E, enthaelt, bezeichnet, h, realisiert⟩
  · intro E hE
    exact Annahme.akzeptiert_katalog E hE.regeln
  · intro K hK
    exact Katalog.katalog_nichtLeer K hK
  · intro a E hbez hacc H hwH
    obtain ⟨t, _, hElab, hZul⟩ := hbez
    change E = einheitVon P t at hElab
    have img : (einheitVon P t).bild.gueltig (einheitVon P t).katalog.plattform.ziel :=
      bildG t hZul
    subst E
    exact Katalog.zulStart_erfuellbar hwH img
  · intro a E hbez hacc H s hwLauf hw zul fair
    obtain ⟨ρ, run, st, hwEq⟩ := fairer_lauf E zul fair
    exact ⟨⟨E, ρ⟩, ⟨rfl, run⟩, st, hwEq⟩
  · intro E hacc
    exact ideal_akzeptiert_quellbindung hacc

/-- Every admissible start has a run, and every implementation run has one ideal run
    carrying all legs of `Verfeinert`. -/
theorem zielAusTeilenVerfeinerung_mitFairSim {P : Katalog.Plattform} (B : FormBeleg)
    (fairSim : FairSimOhneHaengenAussage P)
    (schranken : SchrankenAkzeptiertAussage P) :
      (∀ a E, (R₀ P B).Bezeichnet a E → (R₀ P B).Akzeptiert E →
        (∀ H, (R₀ P B).Hardware ((R₀ P B).katalog E) H →
          (∀ s, (R₀ P B).ZulStart E H s →
            ∃ ρ, (R₀ P B).Laeufe E H ρ ∧ (R₀ P B).start ρ = s)
          ∧ (∀ ρ, (R₀ P B).Laeufe E H ρ →
            ∃ ι, (R₀ P B).IdealLaeufe E ι ∧
              Ziel.Verfeinert (R₀ P B) E H ρ ι))) := by
  intro a E hbez hacc H hwH
  constructor
  · intro s zul
    obtain ⟨ρ, run, st⟩ := lauf_ab_start E hwH zul
    exact ⟨⟨E, ρ⟩, ⟨rfl, run⟩, st⟩
  · intro ρ laufR
    obtain ⟨t, _, hElab, hZul⟩ := hbez
    change E = einheitVon P t at hElab
    rcases ρ with ⟨E', ρ'⟩
    change E' = E ∧ Maschine.Laeufe E' H ρ' at laufR
    have run : Maschine.Laeufe E' H ρ' := laufR.2
    have e't : E' = einheitVon P t := laufR.1.trans hElab
    subst E'
    subst E
    have matched : ∃ η : Maschine.I.Lauf (einheitVon P t),
        Maschine.I.Laeufe (einheitVon P t) η ∧ Maschine.I.Sim (einheitVon P t) ρ' η ∧
          (Katalog.FairLaeufe (einheitVon P t).katalog H ρ'.hw →
            ∀ c, ¬ Maschine.I.Haengt (einheitVon P t) ρ' η c) := by
      by_cases fair : Katalog.FairLaeufe (einheitVon P t).katalog H ρ'.hw
      · obtain ⟨η, valid, sim, noHang⟩ := fairSim t hZul hacc.regeln H ρ' run fair
        exact ⟨η, valid, sim, fun _ => noHang⟩
      · obtain ⟨η, valid, sim⟩ := verfeinerung_akzeptiert P t hacc.regeln H ρ' run
        exact ⟨η, valid, sim, fun h => (fair h).elim⟩
    obtain ⟨η, valid, sim, progress⟩ := matched
    refine ⟨⟨einheitVon P t, η⟩, ?_, ?_⟩
    · exact ⟨rfl, valid⟩
    · unfold Ziel.Verfeinert
      dsimp only [R₀]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact ⟨rfl, ⟨rfl, sim⟩⟩
      · intro k
        exact ⟨rfl, zielFX_akzeptiert P t hacc.regeln H ρ' run k⟩
      · intro fair
        refine ⟨?_, ?_⟩
        · intro c hc
          obtain ⟨_, hEq, hAng⟩ := hc
          cases hEq
          exact progress fair c hAng
        · refine ⟨rfl, ?_⟩
          change DeadlockFrei η
          exact deadlockfrei_aus_waechter valid hacc.2.2
      · exact ⟨rfl, schranken t hacc.regeln H ρ' run⟩

variable {P : Katalog.Plattform} (rueckkehr :
  ∀ (t : Ast.Unit), Annahme.Akzeptiert (einheitVon P t) →
    ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ →
      Katalog.FairLaeufe (einheitVon P t).katalog H ρ.hw →
      Maschine.VerdraengungKehrtZurueckAbsturzfrei ρ)

include rueckkehr

/-- Crash-free interrupt return suffices for fair simulation without hanging. -/
theorem fairSim_aus_rueckkehr (existiert : ZugriffSchrittExistiertAussage) :
    FairSimOhneHaengenAussage P := by
  intro t _ accepted H ρ run fair
  obtain ⟨η, valid, sim, _, _, progress⟩ :=
    einheitVon_sim_ziel_fortschritt_absturzfrei existiert P t run (rueckkehr t accepted H ρ run)
  exact ⟨η, valid, sim, (progress fair).1⟩

theorem zielAusTeilenVerfeinerung (B : FormBeleg) (existiert : ZugriffSchrittExistiertAussage)
    (schranken : SchrankenAkzeptiertAussage P) :
      (∀ a E, (R₀ P B).Bezeichnet a E → (R₀ P B).Akzeptiert E →
        (∀ H, (R₀ P B).Hardware ((R₀ P B).katalog E) H →
          (∀ s, (R₀ P B).ZulStart E H s →
            ∃ ρ, (R₀ P B).Laeufe E H ρ ∧ (R₀ P B).start ρ = s)
          ∧ (∀ ρ, (R₀ P B).Laeufe E H ρ →
            ∃ ι, (R₀ P B).IdealLaeufe E ι ∧
              Ziel.Verfeinert (R₀ P B) E H ρ ι))) :=
  zielAusTeilenVerfeinerung_mitFairSim B (fairSim_aus_rueckkehr rueckkehr existiert) schranken

/-- The goal over `R₀` follows from the listed proof obligations. -/
theorem zielAusTeilen (niSpuren : VergleichSpurenAussage) (B : FormBeleg)
    (formG : FormenGedecktAussage P B) : Ziel.GabbroZielForm (R₀ P B) := by
  unfold Ziel.GabbroZielForm
  constructor
  · exact zielAusTeilenNichtLeer P B (bildGueltig P) formG
  · constructor
    · exact zielAusTeilenVerfeinerung rueckkehr B zugriffSchrittExistiert (schrankenAkzeptiert P)
    · exact (zielNI_iff_vergleich P B).2 niSpuren

end Gabbro.Core.Ziel.Korrektheit
