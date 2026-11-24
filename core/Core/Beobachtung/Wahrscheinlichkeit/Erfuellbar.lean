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

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Core.Beobachtung.Wahrscheinlichkeit.Form
public import Core.Beobachtung.Wahrscheinlichkeit.Aussagen
public import Core.Beobachtung.Wahrscheinlichkeit.Quelle
public import Core.Beobachtung.Wahrscheinlichkeit.KostenErwartungBeweis
public import Core.Annahme
public import Core.Katalog.Erfuellbar

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog
open MeasureTheory

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

/-- Joint satisfiability of the sharpened cost premises with a genuine certificate:
    `c = 1`, `q = 1/2`, `b = 2` (so `c / q = 2`), a family that exits at tick one
    for every band, and cost one. Unlike the refuted form, binding the cost to the
    first exit makes the constant-cost instance obey the bound. -/
theorem kostenPflicht_erfuellbar
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Umgebung)
    (hb : Hebebuendel B S E h) :
    ∃ (kosten : Maschine.Lauf E → Nat) (ueberlebt : Nat → Set Band),
      pruefeProb (.kosten 1 1 1 2 2 1) = true ∧
      (∀ n, MeasurableSet (ueberlebt n)) ∧
      (∀ n, ueberlebt (n + 1) ⊆ ueberlebt n) ∧
      (∀ n, hb.mu (ueberlebt n) ≤ (1 - ((1 : ENNReal) / 2)) ^ n) ∧
      (∀ band n, band ∉ ueberlebt n → (∀ m < n, band ∈ ueberlebt m) →
        (kosten (hb.replay band) : ENNReal) ≤ (n : ENNReal) * ((1 : ENNReal) / 1)) ∧
      (∃ band : Band, (kosten (hb.replay band) : ENNReal) = 1) ∧
      kostenPflicht B hb kosten 1 1 1 2 2 1 ∧
      KostenForm B hb kosten (2 : ENNReal) := by
  letI : MeasureTheory.IsProbabilityMeasure hb.mu := hb.istWMass
  let ueberlebt : Nat → Set Band := fun n => if n = 0 then Set.univ else ∅
  refine ⟨fun _ => 1, ueberlebt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · intro n
    by_cases hn : n = 0
    · subst n
      exact (by simp only [ueberlebt, if_pos rfl, MeasurableSet.univ])
    · exact (by simp only [ueberlebt, hn, if_false, MeasurableSet.empty])
  · intro n band hmem
    have hmemEmpty : band ∈ (∅ : Set Band) := by
      simpa only [ueberlebt, Nat.add_one, Nat.succ_ne_zero, if_false] using hmem
    exact False.elim hmemEmpty
  · intro n
    by_cases hn : n = 0
    · subst n
      rw [show ueberlebt 0 = Set.univ by simp only [ueberlebt, if_pos rfl]]
      rw [IsProbabilityMeasure.measure_univ, pow_zero]
    · rw [show ueberlebt n = ∅ by simp only [ueberlebt, hn, if_false]]
      rw [measure_empty]
      exact zero_le
  · intro band n hnout hmin
    have hn0 : n ≠ 0 := by
      intro hn
      subst n
      exact hnout (by simp only [ueberlebt, if_pos rfl, Set.mem_univ])
    have hnOne : 1 ≤ n := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hn0)
    have hnOneE : (1 : ENNReal) ≤ (n : ENNReal) := by exact_mod_cast hnOne
    simpa only [Nat.cast_one, div_one, mul_one] using hnOneE
  · exact ⟨fun _ _ => 0, by simp only [Nat.cast_one]⟩
  · intro hpruefe ueb hmeas hanti hdecay hkosten
    exact kostenErwartung L Ort Wert Raum Lok Grund Bedingung Wahl Form E B S h hb
      (fun _ => 1) 1 1 1 2 2 1 hpruefe ueb hmeas hanti hdecay hkosten
  · unfold KostenForm
    simp only [Nat.cast_one]
    change (∫⁻ band, (1 : ENNReal) ∂hb.mu) ≤ (2 : ENNReal)
    rw [lintegral_const, IsProbabilityMeasure.measure_univ, one_mul]
    norm_num

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

/-- Two declared adversaries that are genuinely different: their answer results
    differ, so a singleton adversary class is a real restriction. -/
def beispielAntwort0 : Antwort :=
  ⟨⟨⟨.hosted, 0⟩, 0⟩, [], .ok (.register 0)⟩

def beispielAntwort1 : Antwort :=
  ⟨⟨⟨.hosted, 0⟩, 0⟩, [], .error .unsupported⟩

def beispielGegner0 : Gegner := fun _ _ _ => beispielAntwort0

def beispielGegner1 : Gegner := fun _ _ _ => beispielAntwort1

def beispielFrage : Frage :=
  ⟨.hosted, ⟨0, ⟨⟨.hosted, 0⟩, 0⟩, []⟩, [], .read⟩

theorem beispielGegner1_ne_0 : beispielGegner1 ≠ beispielGegner0 := by
  intro h
  have happ := congrFun (congrFun (congrFun h (fun _ _ => 0)) ([] : AussenVerlauf)) beispielFrage
  have hdiff : beispielAntwort0.result ≠ beispielAntwort1.result := by
    intro hr
    cases hr
  exact hdiff (congrArg Antwort.result happ).symm

/-- Satisfiability of the information-theoretic duty with a nontrivial declaration:
    a singleton budget class, the positive bound `1` and a game that holds only at
    the declared run. Every event has measure at most one, so the duty holds. -/
theorem infoTheoretischPflicht_erfuellbar
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Umgebung)
    (hb : Hebebuendel B S E h) :
    ∃ deklaration : InfoDeklaration L Ort Wert Raum Lok Grund Bedingung Wahl Form E,
      deklaration.eps = 1 ∧
      (∃ A : Gegner, deklaration.imBudget A) ∧
      (∃ A : Gegner, ¬ deklaration.imBudget A) ∧
      (¬ ∀ A : Gegner, ∀ ρ : Maschine.Lauf E, deklaration.spiel A ρ) ∧
      (∃ band : Band, deklaration.spiel beispielGegner0 (hb.replay band)) ∧
      InfoTheoretischPflicht B hb deklaration := by
  letI : MeasureTheory.IsProbabilityMeasure hb.mu := hb.istWMass
  let band0 : Band := fun _ _ => 0
  let deklaration : InfoDeklaration L Ort Wert Raum Lok Grund Bedingung Wahl Form E :=
    { imBudget := fun A => A = beispielGegner0
      eps := 1
      spiel := fun A ρ => A = beispielGegner0 ∧ ρ = hb.replay band0 }
  refine ⟨deklaration, rfl, ⟨beispielGegner0, rfl⟩, ⟨beispielGegner1, ?_⟩, ?_, ⟨band0, ?_⟩, ?_⟩
  · exact beispielGegner1_ne_0
  · intro hall
    exact beispielGegner1_ne_0 (hall beispielGegner1 (hb.replay band0)).1
  · exact ⟨rfl, rfl⟩
  · intro A hA
    calc
      hb.mu {band | deklaration.spiel A (hb.replay band)} ≤ hb.mu Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := IsProbabilityMeasure.measure_univ

/-- Satisfiability of the reduction duty with a nontrivial declaration: singleton
    scheme and primitive classes carrying the named hardness assumption, factor
    `1`, identity reduction and a game held by the declared run. The reduction
    lands in the primitive class and both games coincide, so the inequality is
    reflexive. -/
theorem reduktionPflicht_erfuellbar
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Umgebung)
    (hb : Hebebuendel B S E h) :
    ∃ deklaration : ReduktionDeklaration L Ort Wert Raum Lok Grund Bedingung Wahl Form E,
      deklaration.c = 1 ∧
      (∃ A : Gegner, deklaration.schemaGegner A) ∧
      (∃ A : Gegner, ¬ deklaration.schemaGegner A) ∧
      (∀ A : Gegner, deklaration.schemaGegner A →
        deklaration.primitivGegner (deklaration.reduktion A)) ∧
      ReduktionPflicht B hb deklaration := by
  let band0 : Band := fun _ _ => 0
  let spiel0 : Gegner → Maschine.Lauf E → Prop :=
    fun A ρ => A = beispielGegner0 ∧ ρ = hb.replay band0
  let deklaration : ReduktionDeklaration L Ort Wert Raum Lok Grund Bedingung Wahl Form E :=
    { schemaGegner := fun A => A = beispielGegner0
      reduktion := fun A => A
      primitivGegner := fun A => A = beispielGegner0
      c := 1
      spiel := spiel0
      ziel := spiel0 }
  refine ⟨deklaration, rfl, ⟨beispielGegner0, rfl⟩, ⟨beispielGegner1, ?_⟩, ?_, ?_⟩
  · exact beispielGegner1_ne_0
  · intro A hA
    exact hA
  · intro A hA
    constructor
    · exact hA
    · change hb.mu {band | spiel0 A (hb.replay band)} ≤
        (1 : ENNReal) * hb.mu {band | spiel0 A (hb.replay band)}
      rw [one_mul]

end Gabbro.Core.Beobachtung
