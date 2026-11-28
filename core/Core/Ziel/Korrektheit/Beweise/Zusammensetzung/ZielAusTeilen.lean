module

public import Core.Ziel.Korrektheit.Beweise2.ZielAusTeilen
public import Core.Ziel.Korrektheit.Beweise.Zusammensetzung.BegleitZusammensetzung
import Core.Ziel.Korrektheit.Beweise2.ZugriffSchrittExistiert

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- The remaining fair-simulation premises are jointly realised, with a matched ideal run. -/
theorem FairSimOhneHaengenAussage.erfuellbar (P : Katalog.Plattform) :
    ∃ (t : Ast.Unit) (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Ast.Semantik.zugelassen P Ast.Category.unit t ∧ Annahme.Akzeptiert (einheitVon P t) ∧
      Maschine.Laeufe (einheitVon P t) H ρ ∧ Katalog.FairLaeufe (einheitVon P t).katalog H ρ.hw ∧
      ∃ η : Maschine.I.Lauf (einheitVon P t),
        Maschine.I.Laeufe (einheitVon P t) η ∧ Maschine.I.Sim (einheitVon P t) ρ η ∧
          ∀ c, ¬ Maschine.I.Haengt (einheitVon P t) ρ η c := by
  have accepted := trivialUnit_akzeptiert P
  obtain ⟨H, ρ, run, fair, scheduler, returned⟩ := einheitVon_fair_lauf_erfuellbar P trivialUnit accepted
  obtain ⟨η, valid, sim, noHang, _⟩ :=
    fortschritt_akzeptiert zugriffSchrittExistiert P trivialUnit accepted H ρ run fair scheduler returned
  exact ⟨trivialUnit, H, ρ, trivialUnit_zugelassen P, accepted, run, fair, η, valid, sim, noHang⟩


end Gabbro.Core.Ziel.Korrektheit
