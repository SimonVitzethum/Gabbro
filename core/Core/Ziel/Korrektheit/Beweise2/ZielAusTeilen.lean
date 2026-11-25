/-
  File:      core/Core/Ziel/Korrektheit/Beweise2/ZielAusTeilen.lean
  Subject:   THE COMPOSITION of the goal theorem `GabbroZielForm (R₀ P B)` from its proved legs and its open
             legs (`ZielAusTeilenAussage`, `Core/Ziel/Korrektheit/Zusammensetzung.lean`). No pinned statement
             and no theorem of the model is changed.

  Four legs are hypotheses of `ZielAusTeilenAussage`: image validity, form coverage, progress and bounds;
  noninterference is a fifth. The front-end, catalogue, start, refinement, guarantee, guard and class legs
  are discharged by existing theorems. Three steps are not among the delivered building blocks and are named
  exactly as premises of `zielAusTeilenMitLuecken`:

  1. `idealLuecke`: `I` is determinate and progresses for EVERY accepted elaborated unit, not only for units
     of the shape `einheitVon P t` (`ideal_akzeptierte_einheit`). This is the eighth conjunct of `NichtLeer`;
     `R₀` quantifies over all accepted units of `Ast.Semantik.Einheit`.
  2. `niLuecke`: noninterference for EVERY accepted elaborated unit, not only for source-denoted ones
     (`niAkzeptiert` goes through `fragment_nichtinterferent`, which needs a fragment and its `Rein` duty).
  3. `hang`: the no-hang leg of `Verfeinert` holds for EVERY ideal run matching the implementation run
     (`FortschrittAkzeptiertAussage` supplies it only for the ideal run its own witness returns; `Sim` does
     not determine that witness uniquely).

  `zielAusTeilenOhneIdealUndNI` delivers the middle part and the first seven conjuncts are discharged inline;
  it needs no extra premise beyond `hang`. `zielAusTeilenAusScheduler` discharges the progress leg from
  `SchedulerFortschrittVoraussetzung`, naming that premise as the content of `FortschrittAkzeptiertAussage`.
-/
module

public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Ziel.Korrektheit.Frontend
public import Core.Ziel.Korrektheit.Verfeinerung
public import Core.Ziel.Korrektheit.Beweise.NIAkzeptiert
public import Core.Ziel.Korrektheit.SchrankenAkzeptiert
public import Core.Ziel.Korrektheit.Beweise.FortschrittAkzeptiert
public import Core.Annahme.Annahme
public import Core.Katalog.Erfuellbar
public import Core.Katalog.Start
public import Core.Maschine.Start
public import Core.Fortschritt.Saetze

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine
open Gabbro.Core.Fortschritt

variable (hang :
  ∀ (P : Katalog.Plattform) (t : Ast.Unit), Annahme.Akzeptiert (einheitVon P t) →
    ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ →
      Katalog.FairLaeufe (einheitVon P t).katalog H ρ.hw →
      ∀ η : Maschine.I.Lauf (einheitVon P t),
        Maschine.I.Laeufe (einheitVon P t) η → Maschine.I.Sim (einheitVon P t) ρ η →
        ∀ c, ¬ Maschine.I.Haengt (einheitVon P t) ρ η c)

include hang

/-- The middle part of `GabbroZielForm (R₀ P B)`: from every admissible start a run, and one ideal run that
refines every implementation run. Only the no-hang premise is extra; all other legs are existing theorems. -/
theorem zielAusTeilenVerfeinerung (P : Katalog.Plattform) (B : FormBeleg) :
    BildGueltigAussage P → FormenGedecktAussage P B → FortschrittAkzeptiertAussage →
      SchrankenAkzeptiertAussage P → NIAkzeptiertAussage P →
      (∀ a E, (R₀ P B).Bezeichnet a E → (R₀ P B).Akzeptiert E →
        (∀ H, (R₀ P B).Hardware ((R₀ P B).katalog E) H →
          (∀ s, (R₀ P B).ZulStart E H s →
            ∃ ρ, (R₀ P B).Laeufe E H ρ ∧ (R₀ P B).start ρ = s)))
      ∧ (∀ a E, (R₀ P B).Bezeichnet a E → (R₀ P B).Akzeptiert E →
        (∀ H, (R₀ P B).Hardware ((R₀ P B).katalog E) H →
          (∀ ρ, (R₀ P B).Laeufe E H ρ →
            ∃ ι, (R₀ P B).IdealLaeufe E ι ∧
              Ziel.Verfeinert (R₀ P B) E H ρ ι))) := by
  intro bildG formG _ schranken _
  constructor
  · intro a E hbez hacc H hwH s zul
    exact lauf_ab_start E hwH zul
  · intro a E hbez hacc H hwH ρ laufR
    obtain ⟨t, _, hElab, hZul⟩ := hbez
    change E = einheitVon P t at hElab
    rcases ρ with ⟨E', ρ'⟩
    change E' = E ∧ Maschine.Laeufe E' H ρ' at laufR
    have run : Maschine.Laeufe E' H ρ' := laufR.2
    have e't : E' = einheitVon P t := laufR.1.trans hElab
    subst E'
    subst E
    obtain ⟨η, valid, sim⟩ := verfeinerung_akzeptiert P t hacc H ρ' run
    refine ⟨⟨einheitVon P t, η⟩, ?_, ?_⟩
    · exact ⟨rfl, valid⟩
    · unfold Ziel.Verfeinert
      dsimp only [R₀]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact ⟨rfl, ⟨rfl, sim⟩⟩
      · intro k
        exact ⟨rfl, zielFX_akzeptiert P t hacc H ρ' run k⟩
      · intro fair
        refine ⟨?_, ?_⟩
        · intro c
          exact hang P t hacc H ρ' run fair η valid sim c
        · refine ⟨rfl, ?_⟩
          change DeadlockFrei η
          exact deadlockfrei_aus_waechter valid hacc.2.2
      · exact ⟨rfl, schranken t hacc H ρ' run⟩

/-- The goal over `R₀` follows once the three named gaps are supplied. -/
theorem zielAusTeilenMitLuecken
    (idealLuecke : ∀ E : Ast.Semantik.Einheit, Annahme.Akzeptiert E →
      Maschine.I.Bestimmt E.einrichtung E.system ∧ Maschine.I.Fortschritt E.einrichtung E.system)
    (niLuecke : ∀ E : Ast.Semantik.Einheit, Annahme.Akzeptiert E →
      Beobachtung.Nichtinterferent E) (P : Katalog.Plattform) (B : FormBeleg) :
    ZielAusTeilenAussage P B := by
  intro bildG formG fortschritt schranken ni
  unfold Ziel.GabbroZielForm
  constructor
  · unfold Ziel.NichtLeer
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a
      exact text_wohlgeformt P a
    · intro a E E' hE hE'
      exact bezeichnet_funktional P a E E' hE hE'
    · intro f
      exact formG f
    · intro E hE
      exact Annahme.akzeptiert_katalog E hE
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
      exact ⟨⟨E, ρ⟩, rfl, run, st, hwEq⟩
    · intro E hacc
      exact idealLuecke E hacc
  · constructor
    · exact zielAusTeilenVerfeinerung hang P B bildG formG fortschritt schranken ni
    · intro E H₁ H₂ ρ₁ s₂ hacc hw₁ hw₂ laufR gleiche zulStart niedrig
      rcases ρ₁ with ⟨E₁, ρ₁'⟩
      change E₁ = E ∧ Maschine.Laeufe E₁ H₁ ρ₁' at laufR
      subst E₁
      have run₁ : Maschine.Laeufe E H₁ ρ₁' := laufR.2
      obtain ⟨ρ₂', run₂, stEq, polEq⟩ :=
        (niLuecke E hacc) H₁ H₂ ρ₁' s₂ hw₁ hw₂ run₁ gleiche zulStart niedrig
      constructor
      · refine ⟨⟨E, ρ₂'⟩, ?_, ?_, ?_⟩
        · exact rfl
        · exact run₂
        · exact stEq
        · exact ⟨rfl, ⟨rfl, polEq⟩⟩
      · intro ρ₂ lauf₂ st₂ pol₂
        rcases ρ₂ with ⟨E₂, ρ₂''⟩
        change E₂ = E ∧ Maschine.Laeufe E₂ H₂ ρ₂'' at lauf₂
        change E₂ = E ∧ ∃ h : E₂ = E, Beobachtung.GleichePolitik E ρ₁' (h ▸ ρ₂'') at pol₂
        subst E₂
        obtain ⟨_, h, pol⟩ := pol₂
        cases h
        exact ((niLuecke E hacc) H₁ H₂ ρ₁' s₂ hw₁ hw₂ run₁ gleiche zulStart niedrig).2
          ρ₂'' lauf₂.2 st₂ pol

/-- The goal follows from the scheduler premise in place of the progress leg, with the three gaps supplied. -/
theorem zielAusTeilenAusScheduler
    (idealLuecke : ∀ E : Ast.Semantik.Einheit, Annahme.Akzeptiert E →
      Maschine.I.Bestimmt E.einrichtung E.system ∧ Maschine.I.Fortschritt E.einrichtung E.system)
    (niLuecke : ∀ E : Ast.Semantik.Einheit, Annahme.Akzeptiert E →
      Beobachtung.Nichtinterferent E) (scheduler : SchedulerFortschrittVoraussetzung)
    (P : Katalog.Plattform) (B : FormBeleg) :
    BildGueltigAussage P → FormenGedecktAussage P B → SchrankenAkzeptiertAussage P →
      NIAkzeptiertAussage P → Ziel.GabbroZielForm (R₀ P B) := by
  intro bildG formG schranken ni
  exact zielAusTeilenMitLuecken idealLuecke niLuecke P B bildG formG
    (fortschritt_akzeptiert_aus_scheduler scheduler) schranken ni

end Gabbro.Core.Ziel.Korrektheit
