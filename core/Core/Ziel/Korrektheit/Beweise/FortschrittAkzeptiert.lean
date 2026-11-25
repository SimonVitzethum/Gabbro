/-
  File:      core/Core/Ziel/Korrektheit/Beweise/FortschrittAkzeptiert.lean
  Subject:   THE PROGRESS PROMISE FOR EVERY ACCEPTED ELABORATED UNIT — the legs that hold today, and the one
             scheduler premise missing for the pinned statement.

  `FortschrittAkzeptiertAussage` is pinned through `KorrektheitAussagen` and is not changed here. Two of its
  legs are available for every accepted unit today: a matched ideal run with whole-run simulation
  (`sim_im_lauf`) and the composed per-cut alternatives (`fortschritt_im_lauf`). The four form-side fields of
  `FortschrittsPflichten` are theorems of the elaborated system (`Fragment.fertig`, `Befehl.fortschritt`,
  `Befehl.komponierbar`, `Fragment.bereit_eindeutig`), collected in `einheit_fortschrittsfelder`.

  The remaining leg is per-context liveness: `¬ Haengt` asks that a continuously enabled, dispatched context
  eventually be serviced on a hardware-fair history. `FairLaeufe` speaks about cores, deliveries and cycles
  only — explicitly "independently of dispatch ... or the existence of a successful implementation step"
  (`Katalog/Lauf.lean`) — so it does not arbitrate which ready context takes a step. The four scheduler fields
  `angebot`, `wahl`, `individuell` and `systemweit` of `FortschrittsPflichten` are therefore an additional
  premise (`SchedulerFortschrittVoraussetzung`), not a theorem of the current model. With that premise the pinned
  statement follows by `sim_ziel_fortschritt_im_lauf`; without it the strongest theorem here is
  `fortschritt_akzeptiert_ohne_haengen`, which leaves exactly the no-hang leg open.
-/
module

public import Core.Ziel.Korrektheit.Verfeinerung
public import Core.Verfeinerung.Fortschritt
public import Core.Verfeinerung.Simulation
public import Core.Ast.Semantik.Pflichten

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine
open Gabbro.Core.Ideal (RegelFortschritt)

/-- THE MISSING SCHEDULER PREMISE. On every fair run of every accepted elaborated unit, the matched ideal run
    admits a selection predicate `nutzbar` for which the four dispatch and selection duties hold: `angebot`
    (a dispatched core offers a tick), `wahl` (the recorded run takes the offered context step), `individuell`
    (a continuously enabled open context is offered again past every cut) and `systemweit` (the system-wide
    completion duty; vacuous for `blockierend`). The other four fields of `FortschrittsPflichten` are theorems
    over the elaborated system (`einheit_fortschrittsfelder`), so this is exactly the hypothesis that
    `sim_ziel_fortschritt_im_lauf` still needs for the pinned `FortschrittAkzeptiertAussage`. -/
def SchedulerFortschrittVoraussetzung : Prop :=
  ∀ (P : Katalog.Plattform) (t : Ast.Unit), Annahme.Akzeptiert (einheitVon P t) →
    ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ → Katalog.FairLaeufe (einheitVon P t).katalog H ρ.hw →
      ∀ η : Maschine.I.Lauf (einheitVon P t),
        Maschine.I.Laeufe (einheitVon P t) η →
        Maschine.I.Laufabgleich ρ η →
        η.umgebung = H →
        ∃ nutzbar, Maschine.I.FortschrittsPflichten
          (Maschine.I.FortschrittsKlasse.blockierend : Maschine.I.FortschrittsKlasse Ast.Semantik.Befehl)
          ρ η nutzbar

/-- The four form-side fields of `FortschrittsPflichten` hold for the elaborated unit without any acceptance
    or run premise: a headless context is finished, every instruction has its ideal step, that step composes
    through the shared protocol, and a ready context is neither finished nor blocked. -/
theorem einheit_fortschrittsfelder (P : Katalog.Plattform) (t : Ast.Unit) :
    (∀ s c, (einheitVon P t).system.kopf s c = none → (einheitVon P t).system.fertig s c) ∧
    (∀ f : Ast.Semantik.Befehl, RegelFortschritt (einheitVon P t).system f) ∧
    (∀ f : Ast.Semantik.Befehl,
      Maschine.I.RegelKomponierbar (einheitVon P t).einrichtung (einheitVon P t).system f) ∧
    (∀ s c, Maschine.I.Bereit (E := einheitVon P t) s c →
      ¬ (einheitVon P t).system.fertig s c ∧ ∀ b, ¬ (einheitVon P t).system.blockiert s c b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Ast.Semantik.Fragment.fertig (Ast.Semantik.fragment Ast.Category.unit t) P
  · intro f
    exact Ast.Semantik.Befehl.fortschritt (Ast.Semantik.fragment Ast.Category.unit t) f
  · intro f
    exact Ast.Semantik.Befehl.komponierbar (Ast.Semantik.fragment Ast.Category.unit t) P f
  · intro s c bereit
    rcases bereit with ⟨w, plans, u, step⟩
    exact Ast.Semantik.Fragment.bereit_eindeutig (Ast.Semantik.fragment Ast.Category.unit t) P step

/-- TODAY'S PROGRESS LEG FOR EVERY ACCEPTED ELABORATED UNIT: a matched ideal run with whole-run simulation and
    the composed per-cut alternatives exist. This is all of the pinned statement except the per-context
    no-hang leg; the scheduler duty `SchedulerFortschrittVoraussetzung` is what remains. -/
theorem fortschritt_akzeptiert_ohne_haengen :
    ∀ (P : Katalog.Plattform) (t : Ast.Unit), Annahme.Akzeptiert (einheitVon P t) →
      ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
        Maschine.Laeufe (einheitVon P t) H ρ →
        ∃ η : Maschine.I.Lauf (einheitVon P t),
          Maschine.I.Laeufe (einheitVon P t) η ∧
          Maschine.I.Sim (einheitVon P t) ρ η ∧
          Maschine.I.FortschrittDerKlasse
            (Maschine.I.FortschrittsKlasse.blockierend : Maschine.I.FortschrittsKlasse Ast.Semantik.Befehl) η := by
  intro P t _ H ρ lauf
  have pflicht : Maschine.I.SimPflichten (einheitVon P t) :=
    (Ast.Semantik.Fragment.simBasis (Ast.Semantik.fragment Ast.Category.unit t) P).mit_formen
      (Ast.Semantik.sim_formen (Ast.Semantik.fragment Ast.Category.unit t) P)
  obtain ⟨η, valid, sim⟩ := Maschine.I.sim_im_lauf pflicht lauf
  refine ⟨η, valid, sim, ?_⟩
  obtain ⟨fertig, regeln, komponierbar, _⟩ := einheit_fortschrittsfelder P t
  refine ⟨?_, trivial⟩
  intro zeit kontext live dispatch
  exact Maschine.I.fortschritt_im_lauf valid fertig regeln komponierbar zeit kontext live dispatch

/-- The pinned statement follows once the scheduler duties are stated for the elaborated unit:
    `sim_ziel_fortschritt_im_lauf` consumes exactly `SchedulerFortschrittVoraussetzung`, and every other premise is
    already a theorem. -/
theorem fortschritt_akzeptiert_aus_scheduler (scheduler : SchedulerFortschrittVoraussetzung) :
    FortschrittAkzeptiertAussage := by
  intro P t akzeptiert H ρ lauf fair
  have pflicht : Maschine.I.SimPflichten (einheitVon P t) :=
    (Ast.Semantik.Fragment.simBasis (Ast.Semantik.fragment Ast.Category.unit t) P).mit_formen
      (Ast.Semantik.sim_formen (Ast.Semantik.fragment Ast.Category.unit t) P)
  obtain ⟨η, valid, sim, _, rest⟩ :=
    Maschine.I.sim_ziel_fortschritt_im_lauf
      (klasse := (Maschine.I.FortschrittsKlasse.blockierend : Maschine.I.FortschrittsKlasse Ast.Semantik.Befehl))
      pflicht lauf
      (fun η valid matched environment fairness =>
        scheduler P t akzeptiert H ρ lauf fairness η valid matched environment)
  exact ⟨η, valid, sim, (rest fair).1, (rest fair).2⟩

end Gabbro.Core.Ziel.Korrektheit
