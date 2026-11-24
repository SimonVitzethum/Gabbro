/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/PflichtBeweise.lean
  Subject:   The three provable pinned probabilistic obligations (M9P, B11(c)).

  Every statement is proved from the lift bundle's own fields and the checker's
  finite verdict: cylinder rewriting by `massErhalt` (on key-`Nodup` paths, carried
  by `schluesselNodupB_nodup`), measure monotonicity for the run event, and
  continuity of the measure from above against the geometric decay of the
  survival family. The cost obligation is NOT provable from its pinned premises;
  its conditional refutation lives in `PflichtWiderlegung.lean`.
-/
module

public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Core.Beobachtung.Wahrscheinlichkeit.Aussagen

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog

/-- A key-consistent checker path maps to a `Nodup` list of draw positions. A
    repeated position in the data denotes the empty cylinder, while the product
    law is positive; the checker refuses exactly those paths, and this bridge
    makes `massErhalt` applicable to every accepted one. -/
theorem schluesselNodupB_nodup (Q : Zufallsquelle) (pfad : List (Nat × Nat))
    (h : schluesselNodupB pfad = true) :
    ((natZylinder Q pfad).pfad.map Prod.fst).Nodup := by
  simp only [natZylinder, List.map_map, Function.comp_apply]
  induction pfad with
  | nil =>
      simp only [List.map_nil, List.nodup_nil]
  | cons p rest ih =>
      simp only [schluesselNodupB, Bool.and_eq_true] at h
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        have hfalse : (rest.any fun q : Nat × Nat => decide (q.1 = p.1)) = false := by
          simpa only [Bool.not_eq_true'] using h.2
        have htrue : (rest.any fun q : Nat × Nat => decide (q.1 = p.1)) = true := by
          rw [List.any_eq_true]
          obtain ⟨q, hqmem, hqfst⟩ := List.mem_map.mp hmem
          have hqfst' : q.1 = p.1 := by simpa only [Function.comp_apply] using hqfst
          exact ⟨q, hqmem, by simp only [hqfst', decide_eq_true_eq]⟩
        rw [htrue] at hfalse
        contradiction
      · exact ih h.1

/-- `planned.probability.event`: a checker-accepted cylinder bound carries to the
    run event, because its preimage under the replay contains the cylinder and
    the measure is monotone. -/
theorem prEreignis : prEreignisAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form _ E B S h hb
    pfad wNum wDen pNum pDen hpruefe hgew
  simp only [pruefeProb, Bool.and_eq_true, decide_eq_true_eq] at hpruefe
  have hnodup : ((natZylinder B.quelle pfad).pfad.map Prod.fst).Nodup :=
    schluesselNodupB_nodup B.quelle pfad hpruefe.1
  have hmass := hb.massErhalt (natZylinder B.quelle pfad) hnodup
  have hcyl : hb.mu (zylinderEreignis B.quelle pfad) =
      (wNum : ENNReal) / (wDen : ENNReal) := by
    simpa only [zylinderEreignis, hgew] using hmass
  have hsubset : zylinderEreignis B.quelle pfad ⊆
      {band | laufZylinderEreignis B S hb pfad (hb.replay band)} := by
    intro band hband
    exact ⟨band, rfl, hband⟩
  have hmono : hb.mu (zylinderEreignis B.quelle pfad) ≤
      hb.mu {band | laufZylinderEreignis B S hb pfad (hb.replay band)} :=
    measure_mono hsubset
  have hpDen0 : (pDen : ENNReal) ≠ 0 := by
    exact_mod_cast hpruefe.2.2.1
  have hpDenTop : (pDen : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top pDen
  have hwDen0 : (wDen : ENNReal) ≠ 0 := by
    exact_mod_cast hpruefe.2.1
  have hwDenTop : (wDen : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top wDen
  have hcross : (pNum : ENNReal) * (wDen : ENNReal) ≤
      (wNum : ENNReal) * (pDen : ENNReal) := by
    exact_mod_cast hpruefe.2.2.2.1
  have hratio : (pNum : ENNReal) / (pDen : ENNReal) ≤
      (wNum : ENNReal) / (wDen : ENNReal) := by
    rw [ENNReal.div_le_iff hpDen0 hpDenTop]
    have hrewrite : ((wNum : ENNReal) / (wDen : ENNReal)) * (pDen : ENNReal) =
        ((wNum : ENNReal) * (pDen : ENNReal)) / (wDen : ENNReal) := by
      simp only [div_eq_mul_inv]
      ac_rfl
    rw [hrewrite]
    rw [ENNReal.le_div_iff_mul_le (Or.inr hwDen0) (Or.inr hwDenTop)]
    exact hcross
  change (pNum : ENNReal) / (pDen : ENNReal) ≤
    hb.mu {band | laufZylinderEreignis B S hb pfad (hb.replay band)}
  exact hratio.trans (hcyl.ge.trans_le hmono)

/-- Geometric rates certified by the checker: the exit rate is in `(0, 1]`, hence
    its complement is a contraction and the powers tend to zero. -/
theorem rateDaten (qNum qDen : Nat)
    (hpruefe : pruefeProb (.abschluss qNum qDen) = true) :
    0 < (qNum : ENNReal) / (qDen : ENNReal) ∧
      (qNum : ENNReal) / (qDen : ENNReal) ≤ 1 ∧
      1 - (qNum : ENNReal) / (qDen : ENNReal) < 1 := by
  simp only [pruefeProb, decide_eq_true_eq] at hpruefe
  have hqDen0 : (qDen : ENNReal) ≠ 0 := by exact_mod_cast hpruefe.1
  have hqDenTop : (qDen : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top qDen
  have hqPos : 0 < (qNum : ENNReal) / (qDen : ENNReal) := by
    apply ENNReal.div_pos
    · exact_mod_cast (Nat.ne_of_gt hpruefe.2.1)
    · exact hqDenTop
  have hqLe : (qNum : ENNReal) / (qDen : ENNReal) ≤ 1 := by
    rw [ENNReal.div_le_iff hqDen0 hqDenTop]
    simpa only [one_mul] using (show (qNum : ENNReal) ≤ qDen from by exact_mod_cast hpruefe.2.2)
  refine ⟨hqPos, hqLe, ENNReal.sub_lt_self (by norm_num) (by norm_num) hqPos.ne'⟩

/-- The survivor intersection has measure zero: the measures form an antitone
    family bounded by a geometric null sequence, so continuity from above and the
    squeeze theorem pin the limit at zero. -/
theorem schnittMassNull {α : Type*} [MeasurableSpace α] {q : ENNReal}
    (mu : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure mu] (ueberlebt : Nat → Set α)
    (hmeas : ∀ n, MeasurableSet (ueberlebt n))
    (hanti : ∀ n, ueberlebt (n + 1) ⊆ ueberlebt n)
    (hdecay : ∀ n, mu (ueberlebt n) ≤ (1 - q) ^ n)
    (hq : 0 < q ∧ q ≤ 1 ∧ 1 - q < 1) :
    mu (⋂ n, ueberlebt n) = 0 := by
  have hantito : Antitone ueberlebt := antitone_nat_of_succ_le hanti
  have hfin : ∃ n, mu (ueberlebt n) ≠ ⊤ := ⟨0, MeasureTheory.measure_ne_top mu (ueberlebt 0)⟩
  have hlim : Filter.Tendsto (mu ∘ ueberlebt) Filter.atTop
      (nhds (mu (⋂ n, ueberlebt n))) :=
    MeasureTheory.tendsto_measure_iInter_atTop (fun n => (hmeas n).nullMeasurableSet) hantito hfin
  have hlimGeom : Filter.Tendsto (fun n : Nat => (1 - q) ^ n) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq.2.2
  have hle0 : mu (⋂ n, ueberlebt n) ≤ 0 :=
    le_of_tendsto_of_tendsto' hlim hlimGeom hdecay
  exact le_antisymm hle0 (bot_le)

/-- Almost-sure termination: the complement of the survivor intersection is the
    set of bands that leave the family, hence lies in the target's preimage. -/
theorem fastSicherAbschluss : fastSicherAbschlussAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form _ E B S h hb
    Ziel qNum qDen hpruefe ueberlebt hmeas hanti hdecay hexit
  have hdaten := rateDaten qNum qDen hpruefe
  let q : ENNReal := (qNum : ENNReal) / (qDen : ENNReal)
  have hnull : hb.mu (⋂ n, ueberlebt n) = 0 :=
    schnittMassNull hb.mu ueberlebt hmeas hanti hdecay hdaten
  have hAmeas : MeasurableSet (⋂ n, ueberlebt n) := MeasurableSet.iInter hmeas
  have hAfin : hb.mu (⋂ n, ueberlebt n) ≠ ⊤ := MeasureTheory.measure_ne_top hb.mu _
  have hcompl : hb.mu (⋂ n, ueberlebt n)ᶜ = 1 := by
    rw [measure_compl hAmeas hAfin, IsProbabilityMeasure.measure_univ, hnull, tsub_zero]
  have hsubset : (⋂ n, ueberlebt n)ᶜ ⊆ {band | Ziel (hb.replay band)} := by
    intro band hband
    apply hexit band
    simpa only [Set.mem_compl_iff, Set.mem_iInter, not_forall] using hband
  have hle : hb.mu {band | Ziel (hb.replay band)} ≤ 1 := by
    rw [← IsProbabilityMeasure.measure_univ (μ := hb.mu)]
    exact measure_mono (Set.subset_univ _)
  have hge : 1 ≤ hb.mu {band | Ziel (hb.replay band)} := by
    rw [← hcompl]
    exact measure_mono hsubset
  change hb.mu {band | Ziel (hb.replay band)} = 1
  exact le_antisymm hle hge

/-- Almost-sure progress: retry progress has the same geometric survival shape
    as termination, with the same exit link into the goal. -/
theorem fastSicherFortschritt : fastSicherFortschrittAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form _ E B S h hb
    Ziel qNum qDen hpruefe ueberlebt hmeas hanti hdecay hexit
  have hdaten := rateDaten qNum qDen hpruefe
  let q : ENNReal := (qNum : ENNReal) / (qDen : ENNReal)
  have hnull : hb.mu (⋂ n, ueberlebt n) = 0 :=
    schnittMassNull hb.mu ueberlebt hmeas hanti hdecay hdaten
  have hAmeas : MeasurableSet (⋂ n, ueberlebt n) := MeasurableSet.iInter hmeas
  have hAfin : hb.mu (⋂ n, ueberlebt n) ≠ ⊤ := MeasureTheory.measure_ne_top hb.mu _
  have hcompl : hb.mu (⋂ n, ueberlebt n)ᶜ = 1 := by
    rw [measure_compl hAmeas hAfin, IsProbabilityMeasure.measure_univ, hnull, tsub_zero]
  have hsubset : (⋂ n, ueberlebt n)ᶜ ⊆ {band | Ziel (hb.replay band)} := by
    intro band hband
    apply hexit band
    simpa only [Set.mem_compl_iff, Set.mem_iInter, not_forall] using hband
  have hle : hb.mu {band | Ziel (hb.replay band)} ≤ 1 := by
    rw [← IsProbabilityMeasure.measure_univ (μ := hb.mu)]
    exact measure_mono (Set.subset_univ _)
  have hge : 1 ≤ hb.mu {band | Ziel (hb.replay band)} := by
    rw [← hcompl]
    exact measure_mono hsubset
  change hb.mu {band | Ziel (hb.replay band)} = 1
  exact le_antisymm hle hge

end Gabbro.Core.Beobachtung
