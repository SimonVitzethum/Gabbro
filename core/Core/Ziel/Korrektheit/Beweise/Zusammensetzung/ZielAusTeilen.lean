module

public import Core.Ziel.Korrektheit.Beweise2.ZielAusTeilen
public import Core.Ziel.Korrektheit.Beweise.Zusammensetzung.VergleichSpuren
import Core.Ziel.Korrektheit.Beweise.Zusammensetzung.BegleitZusammensetzung
import Core.Ziel.Korrektheit.Beweise.BildGueltig
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

theorem zielNI_widerlegt (P : Katalog.Plattform) (B : FormBeleg) : ¬ Ziel.NI (R₀ P B) := by
  intro ni
  exact vergleichSpurenOhneHerkunft_widerlegt
    (vergleichSpuren_iff_ohneHerkunft.1 ((zielNI_iff_vergleich P B).1 ni))

/-- All five premises hold on the registered base certificate. The resulting NI clause
    would cover an accepted unit with a secret-dependent implementation loader. -/
theorem zielAusTeilen_widerlegt : ¬ ZielAusTeilenAussage .x86_64 beleg := by
  intro composition
  have goal := composition (bildGueltig .x86_64) beleg_gedeckt
    (fortschritt_akzeptiert zugriffSchrittExistiert) (schrankenAkzeptiert .x86_64) (niAkzeptiert .x86_64)
  exact zielNI_widerlegt .x86_64 beleg goal.2.2

end Gabbro.Core.Ziel.Korrektheit
