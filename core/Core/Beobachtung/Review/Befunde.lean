/-
  File:      core/Core/Beobachtung/Review/Befunde.lean
  Subject:   Statement-level review findings for core/Core/Beobachtung.

  `infoTheoretischAussage` and `reduktionAussage` quantify freely over the bound
  parameters (`eps`, `c`) and the adversary predicates (`imBudget`, `spiel`,
  `ziel`) that their doc comments describe as program-fixed GabbroProve parameters.
  Instantiating a zero bound with `imBudget`/`spiel` true (respectively `spiel`
  true and `ziel` false) makes the body demand `mu univ <= 0`, which contradicts
  the lift bundle's probability measure. The negations are conditional on a lift
  bundle, exactly as the already-known `kostenErwartung_widerlegt`: bundle
  existence stays pinned in `hebeAussage`.

  Nothing here changes an existing statement. These are refutations only.
-/
module

public import Core.Beobachtung.Wahrscheinlichkeit.Aussagen

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog
open MeasureTheory

private def reviewAntwort : Antwort :=
  ⟨⟨⟨.hosted, 0⟩, 0⟩, [], .ok (.register 0)⟩

private def reviewGegner : Gegner := fun _ _ _ => reviewAntwort

/-- The information-theoretic body is unhaltbar at `eps = 0` with an always-true
    budget and game: every adversary then has `mu univ <= 0`, i.e. `1 <= 0`. -/
theorem schrankenForm_eps_null_unhaltbar
    {B : Zufallsbindung} {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
    [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung} (hb : Hebebuendel B S E h) :
    ¬ SchrankenForm B hb (fun _ => True) 0 (fun _ _ => True) := by
  intro hform
  letI : MeasureTheory.IsProbabilityMeasure hb.mu := hb.istWMass
  have hle := hform reviewGegner trivial
  change hb.mu Set.univ ≤ 0 at hle
  rw [MeasureTheory.IsProbabilityMeasure.measure_univ] at hle
  exact (not_le_of_gt zero_lt_one) hle

/-- The reduction body is unhaltbar at `c = 0` with an always-true game and an
    always-false target: the right-hand measure is `0 * mu empty = 0`, so again
    `mu univ <= 0`, i.e. `1 <= 0`. -/
theorem reduktionForm_c_null_unhaltbar
    {B : Zufallsbindung} {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
    [DecidableEq L]
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {S : Scheduler} {h : Umgebung} (hb : Hebebuendel B S E h) :
    ¬ ReduktionForm B hb (fun _ => True) (fun A => A) (fun _ => True) 0
        (fun _ _ => True) (fun _ _ => False) := by
  intro hform
  letI : MeasureTheory.IsProbabilityMeasure hb.mu := hb.istWMass
  have hle := hform reviewGegner trivial
  change hb.mu Set.univ ≤ 0 * hb.mu (∅ : Set Band) at hle
  rw [MeasureTheory.measure_empty, zero_mul,
    MeasureTheory.IsProbabilityMeasure.measure_univ] at hle
  exact (not_le_of_gt zero_lt_one) hle

/-- The pinned information-theoretic `Aussage` is false for every lift bundle:
    its free `eps`/`imBudget`/`spiel` binders admit the zero-bound instantiation. -/
theorem infoTheoretischAussage_widerlegt
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Umgebung)
    (hb : Hebebuendel B S E h) : ¬ infoTheoretischAussage := by
  intro hall
  exact schrankenForm_eps_null_unhaltbar hb
    (hall L Ort Wert Raum Lok Grund Bedingung Wahl Form E B S h hb
      (fun _ => True) 0 (fun _ _ => True))

/-- The pinned reduction `Aussage` is false for every lift bundle: its free
    `c`/`spiel`/`ziel` binders (and the entirely unused `primitivGegner`) admit the
    zero-factor instantiation. -/
theorem reduktionAussage_widerlegt
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Umgebung)
    (hb : Hebebuendel B S E h) : ¬ reduktionAussage := by
  intro hall
  exact reduktionForm_c_null_unhaltbar hb
    (hall L Ort Wert Raum Lok Grund Bedingung Wahl Form E B S h hb
      (fun _ => True) (fun A => A) (fun _ => True) 0
      (fun _ _ => True) (fun _ _ => False))

end Gabbro.Core.Beobachtung
