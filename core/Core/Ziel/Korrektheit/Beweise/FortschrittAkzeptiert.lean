/-
  File:      core/Core/Ziel/Korrektheit/Beweise/FortschrittAkzeptiert.lean
  Subject:   THE PROGRESS PROMISE FOR EVERY ACCEPTED ELABORATED UNIT — the legs that hold
             without any scheduler premise.

  Two legs of the pinned `FortschrittAkzeptiertAussage` are available for every accepted
  unit today: a matched ideal run with whole-run simulation (`sim_im_lauf`) and the composed
  per-cut alternatives (`fortschritt_im_lauf`). The four form-side fields of
  `FortschrittsPflichten` are theorems of the elaborated system (`einheit_fortschrittsfelder`
  in `Beweise/Fortschritt/EinheitLaeufe.lean`). With them, `fortschritt_akzeptiert_ohne_haengen`
  is the strongest scheduler-free theorem here, leaving exactly the per-context no-hang leg
  open. The two run premises that close it — `Maschine.SchedulerFair` and
  `Maschine.VerdraengungKehrtZurueck` — deliver the selection duties in
  `Beweise/Fortschritt/SchedulerEinheit.lean`.
-/
module

public import Core.Ziel.Korrektheit.Verfeinerung
public import Core.Verfeinerung.Fortschritt
public import Core.Verfeinerung.Simulation
public import Core.Ziel.Korrektheit.Beweise.Fortschritt.EinheitLaeufe

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine
open Gabbro.Core.Ideal (RegelFortschritt)

/-- TODAY'S PROGRESS LEG FOR EVERY ACCEPTED ELABORATED UNIT: a matched ideal run with whole-run simulation and
    the composed per-cut alternatives exist. This is all of the pinned statement except the per-context
    no-hang leg; the scheduler duties are what remains. -/
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

end Gabbro.Core.Ziel.Korrektheit
