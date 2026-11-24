/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/PflichtWiderlegung.lean
  Subject:   The pinned expected-cost obligation is false (M9P, B11(c)).

  `kostenPflicht` bounds the cost of a band by `n * c` for SOME exit index `n`
  (`∀ band, ∃ n, band ∉ ueberlebt n ∧ cost ≤ n * c`). It does not require `n` to
  be the first exit. A constant cost function therefore satisfies every premise
  with the empty survival family, while its integral exceeds the certified bound.
  The refutation below is conditional on a lift bundle: the unconditional step is
  bundle existence, which stays pinned in `hebeAussage`.
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Core.Beobachtung.Wahrscheinlichkeit.Aussagen

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog
open MeasureTheory

/-- The expected-cost obligation is refuted for every bundle: a constant cost
    `2`, the empty survival family and the certificate `c = q = b = 1` satisfy all
    premises, yet the integral is `2 > 1`. The unconditional negation needs a
    bundle; the model-side existence of one is pinned in `hebeAussage`. -/
theorem kostenErwartung_widerlegt
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    (E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (B : Zufallsbindung) (S : Scheduler) (h : Umgebung)
    (hb : Hebebuendel B S E h) : ¬ kostenErwartungAussage := by
  intro hall
  letI : MeasureTheory.IsProbabilityMeasure hb.mu := hb.istWMass
  have hk := hall L Ort Wert Raum Lok Grund Bedingung Wahl Form E B S h hb
    (fun _ => 2) 1 1 1 1 1 1
  have hwider : ¬ kostenPflicht B hb (fun _ => 2) 1 1 1 1 1 1 := by
    intro hpflicht
    have hres := hpflicht (by decide) (fun _ => (∅ : Set Band))
      (fun _ => MeasurableSet.empty)
      (fun _ => Set.empty_subset _)
      (fun n => by simp only [measure_empty, zero_le])
      (fun band => ⟨2, by simp only [Set.mem_empty_iff_false, not_false_eq_true], by norm_num⟩)
    unfold KostenForm at hres
    norm_num at hres
  exact hwider hk

end Gabbro.Core.Beobachtung
