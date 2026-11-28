module

public import Core.Ziel.Korrektheit.Zusammensetzung
import Core.Ziel.Korrektheit.NichtAkzeptierteEinheit
import Core.Ziel.Korrektheit.Beweise.Zusammensetzung.NICounterexample
import Core.Ziel.Korrektheit.Beweise.Falsifizierbar

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- The four content requirements hold on every platform of the concrete frame. -/
theorem zielInhalt (P : Katalog.Plattform) : ZielInhaltAussage P := by
  obtain ⟨H, _, _, ρ, admitted⟩ := trivialUnit_lauf P
  exact ⟨⟨trivialUnit, trivialUnit_akzeptiert P, H, ρ, admitted⟩,
    ⟨textIndexUnit, textIndexUnit_nicht_akzeptiert_auf P⟩, simRefutierbar, niRefutierbar⟩

end Gabbro.Core.Ziel.Korrektheit
