/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/Erfuellbar.lean
  Subject:   Non-vacuity, proved: the coin interior, the platform witness, the
    declaration discipline (M9P).

  This is the `_erfuellbar` side of M9P, proved, with no witness runs: the fair
  coin's event is strictly inside `(0, 1)` (`muenz_nichtLeer` discharges
  `ProbNichtLeer`), bindings can be formed over it (`bindungsZeuge`), and the
  run-measure notion (cylinder weight) agrees with the event probability
  (`muenzZylinder`).

  Random rows are platform rows: `beispielPlattformZufall` shows the coin row is
  selected on x86-64, with its law fixed by `zufallGesetz`; `quelleDeklariert`
  shows every `.zufall` row selected in an accepted catalogue is backed by exactly
  one platform-declared source — the declaration discipline (B11(d), model side),
  proved, not pinned.

  The `…_erfuellbar` side of the new obligations is proved here too: the checker
  accepts key-consistent clauses with nontrivial bounds on the coin, and the lift
  premises (`hebeAussage_erfuellbar`) hold jointly for the coin binding on the
  approved x86-64 rows.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Form
public import Core.Beobachtung.Wahrscheinlichkeit.Quelle
public import Core.Annahme
public import Core.Katalog.Erfuellbar

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog

/-- The coin discharges `ProbNichtLeer`: its event is strictly inside `(0, 1)`. -/
theorem muenz_nichtLeer : ProbNichtLeer muenzQuelle :=
  ⟨muenzEreignis, inferInstance, muenz_innen.1, muenz_innen.2⟩

/-- Bindings can be formed over the coin: a witness for the declaration premises.
    The row itself comes from the platform profile, never from a program. -/
theorem bindungsZeuge : ∃ B : Zufallsbindung, B.quelle = muenzQuelle :=
  ⟨⟨muenzQuelle, Katalog.Endpunkt.hosted, []⟩, rfl⟩

/-- The example platform row: the coin row is selected on x86-64. -/
theorem beispielPlattformZufall : Zeile.zufall 0 ∈ Plattform.x86_64.zeilen := by
  apply List.mem_append_right
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  exact List.mem_singleton_self _

/-- Declaration discipline, proved (B11(d), model side): every `.zufall` row
    selected in an accepted catalogue is backed by exactly one platform-declared
    source. -/
theorem quelleDeklariert {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (hacc : Annahme.Akzeptiert E) (id : Nat)
    (hmem : E.katalog.enthaelt (.zufall id)) :
    ∃! Q : Zufallsquelle, zufallGesetz E.katalog.plattform id = some Q ∧ Q.id = id := by
  have hw := Annahme.akzeptiert_katalog _ hacc
  have hmem' : Zeile.zufall id ∈ E.katalog.plattform.zeilen := hw.2.2.1 hmem
  rw [Plattform.zeilen, Plattform.dauerZeilen_leer, Plattform.zufallZeilen_inhalt] at hmem'
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_singleton,
    List.not_mem_nil, false_or, or_false, false_and, and_false, exists_false,
    ZielZeilen, reduceCtorEq, Zeile.endpoint.injEq, Zeile.dauer.injEq,
    Zeile.zufall.injEq] at hmem'
  subst hmem'
  refine ⟨muenzQuelle, ⟨zufallGesetz_nationaleMuenze _, rfl⟩, fun Q hQ => ?_⟩
  have htab := zufallGesetz_nationaleMuenze E.katalog.plattform
  have heq : muenzQuelle = Q := Option.some.inj (htab.symm.trans hQ.1)
  exact heq.symm

/-- The singleton cylinder over the coin's heads weighs `2⁻¹`: the run-measure
    notion agrees with the event probability. -/
theorem muenzZylinder :
    ZylinderGewicht muenzQuelle ⟨[(0, muenzKopf)]⟩ = (2⁻¹ : ENNReal) := by
  have hZ := zylinderSingleton muenzQuelle 0 muenzKopf
  rw [hZ]
  exact PMF.ofFintype_apply muenzSumme muenzKopf

/-- The coin's cylinder weight is its event probability: the clause path
    `[(0, 0)]` (draw 0, outcome 0 = heads) carries `2⁻¹`, strictly inside
    `(0, 1)` by `muenz_innen`. -/
theorem muenzZylinder_gleich :
    ZylinderGewicht muenzQuelle (natZylinder muenzQuelle [(0, 0)]) =
      Wahrscheinlichkeit muenzQuelle muenzEreignis := by
  have h1 : natZylinder muenzQuelle [(0, 0)] = ⟨[(0, muenzKopf)]⟩ := rfl
  rw [h1, zylinderSingleton]
  change muenzQuelle.gesetz muenzKopf =
    Wahrscheinlichkeit muenzQuelle fun x => x = muenzKopf
  rw [wahrscheinlichkeitEinzel muenzQuelle muenzKopf]

/-- Satisfiability of the event obligation's checker side: a key-consistent
    clause the checker accepts, with a nontrivial bound carried by the coin. -/
theorem prEreignis_erfuellbar :
    ∃ pfad pNum pDen,
      pruefeProb (.ereignis pfad 1 2 pNum pDen) = true ∧
      0 < pNum ∧ pNum < pDen ∧
      ZylinderGewicht muenzQuelle (natZylinder muenzQuelle pfad) =
        Wahrscheinlichkeit muenzQuelle muenzEreignis := by
  exact ⟨[(0, 0)], 1, 2, rfl, by decide, by decide, muenzZylinder_gleich⟩

/-- Satisfiability of the cost obligation's checker side: the checker accepts a
    geometric certificate with exit rate strictly inside `(0, 1)` (the coin's
    rate `1 / 2` by `muenzWahrscheinlichkeit`). -/
theorem kostenErwartung_erfuellbar :
    ∃ cNum cDen qNum qDen bNum bDen,
      pruefeProb (.kosten cNum cDen qNum qDen bNum bDen) = true ∧
      0 < qNum ∧ qNum < qDen ∧ 0 < bNum := by
  exact ⟨1, 1, 1, 2, 2, 1, by decide, by decide, by decide, by decide⟩

/-- Satisfiability of the termination obligation's checker side: the checker
    accepts a nontrivial geometric exit rate. -/
theorem fastSicherAbschluss_erfuellbar :
    ∃ qNum qDen, pruefeProb (.abschluss qNum qDen) = true ∧
      0 < qNum ∧ qNum < qDen := by
  exact ⟨1, 2, by decide, by decide, by decide⟩

/-- Satisfiability of the progress obligation's checker side: same geometric
    shape as termination. -/
theorem fastSicherFortschritt_erfuellbar :
    ∃ qNum qDen, pruefeProb (.fortschritt qNum qDen) = true ∧
      0 < qNum ∧ qNum < qDen := by
  exact ⟨1, 2, by decide, by decide, by decide⟩

/-- Satisfiability of the lift premises: the coin binding on the approved x86-64
    rows meets hardware with a selected source row. The bundle itself (the
    conclusion of `hebeAussage`) stays pinned for Hy4. -/
theorem hebeAussage_erfuellbar :
    ∃ (B : Zufallsbindung) (h : Umgebung),
      Katalog.Hardware Annahme.trivialeEinheit.katalog h ∧
        Annahme.trivialeEinheit.katalog.enthaelt
          (Katalog.Zeile.zufall B.quelle.id) := by
  obtain ⟨B, hB⟩ := bindungsZeuge
  obtain ⟨_, h, _, hw, _⟩ := Katalog.plattform_erfuellbar Plattform.x86_64
  refine ⟨B, h, hw, ?_⟩
  rw [hB]
  change Katalog.Zeile.zufall 0 ∈ Plattform.x86_64.zeilen
  exact beispielPlattformZufall

end Gabbro.Core.Beobachtung
