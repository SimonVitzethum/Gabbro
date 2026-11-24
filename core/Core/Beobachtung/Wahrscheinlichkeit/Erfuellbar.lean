/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Erfuellbar.lean
  Subject:   Non-vacuity, proved: the coin interior and the binding witness (M9P).

  This is the `_erfuellbar` side of M9P, proved, with no witness runs: the fair
  coin's event is strictly inside `(0, 1)` (`muenz_nichtLeer` discharges
  `ProbNichtLeer`), bindings can be formed over it (`bindungsZeuge`), and the
  run-measure notion (cylinder weight) agrees with the event probability
  (`muenzZylinder`).

  What stays future work (documented, not faked): full premise satisfiability of
  `hebeAussage` needs an accepted unit whose catalogue selects a `.zufall` row.
  No such unit exists yet - the `random` source form lands with M6, and its
  acceptance case with the checker side. The relaxed `KatalogWohlgeformt` already
  admits the row; `quelleDeklariertAussage` pins the declaration discipline.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Form
public import Core.Beobachtung.Wahrscheinlichkeit.Quelle

@[expose] public section

namespace Gabbro.Core.Beobachtung

/-- The coin discharges `ProbNichtLeer`: its event is strictly inside `(0, 1)`. -/
theorem muenz_nichtLeer : ProbNichtLeer muenzQuelle :=
  ⟨muenzEreignis, inferInstance, muenz_innen.1, muenz_innen.2⟩

/-- Bindings can be formed over the coin: a witness for the declaration premises.
    Catalogue selection of the row is per-program (relaxed `KatalogWohlgeformt`). -/
theorem bindungsZeuge : ∃ B : Zufallsbindung, B.quelle = muenzQuelle :=
  ⟨⟨muenzQuelle, Katalog.Endpunkt.hosted, []⟩, rfl⟩

/-- The singleton cylinder over the coin's heads weighs `2⁻¹`: the run-measure
    notion agrees with the event probability. -/
theorem muenzZylinder :
    ZylinderGewicht muenzQuelle ⟨[(0, muenzKopf)]⟩ = (2⁻¹ : ENNReal) := by
  have hZ := zylinderSingleton muenzQuelle 0 muenzKopf
  rw [hZ]
  exact PMF.ofFintype_apply muenzSumme muenzKopf

end Gabbro.Core.Beobachtung
