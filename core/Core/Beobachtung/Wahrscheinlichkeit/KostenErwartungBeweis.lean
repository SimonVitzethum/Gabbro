/-
  File:      Core/Beobachtung/Wahrscheinlichkeit/KostenErwartungBeweis.lean
  Subject:   The expected-cost obligation, proved (M9P, B11(c)).

  Off the null intersection of the survivor family every band has a first exit;
  the cost premise bounds its cost by that first exit times `c`. The tail-sum
  formula for a natural-valued random variable bounds the mean first exit by the
  geometric series, so the checker's certificate `c / q ≤ b` closes the claim.
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecificLimits.Basic
public import Core.Beobachtung.Wahrscheinlichkeit.PflichtBeweise

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog
open MeasureTheory

/-- The checker's geometric certificate in ENNReal: a nontrivial exit rate with
    contraction below one, and the bound `c / q ≤ b`. -/
theorem kostenZertifikat (cNum cDen qNum qDen bNum bDen : Nat)
    (hpruefe : pruefeProb (.kosten cNum cDen qNum qDen bNum bDen) = true) :
    0 < (qNum : ENNReal) / (qDen : ENNReal) ∧
      (qNum : ENNReal) / (qDen : ENNReal) ≤ 1 ∧
      1 - (qNum : ENNReal) / (qDen : ENNReal) < 1 ∧
      ((cNum : ENNReal) / (cDen : ENNReal)) /
          ((qNum : ENNReal) / (qDen : ENNReal)) ≤
        (bNum : ENNReal) / (bDen : ENNReal) := by
  simp only [pruefeProb, decide_eq_true_eq] at hpruefe
  have hcDen0Nat : cDen ≠ 0 := hpruefe.1
  have hqDen0Nat : qDen ≠ 0 := hpruefe.2.1
  have hbDen0Nat : bDen ≠ 0 := hpruefe.2.2.1
  have hqPosNat : 0 < qNum := hpruefe.2.2.2.1
  have hqLeNat : qNum ≤ qDen := hpruefe.2.2.2.2.1
  have hcertNat : cNum * qDen * bDen ≤ bNum * cDen * qNum := hpruefe.2.2.2.2.2
  have hcDen0 : (cDen : ENNReal) ≠ 0 := by exact_mod_cast hcDen0Nat
  have hqDen0 : (qDen : ENNReal) ≠ 0 := by exact_mod_cast hqDen0Nat
  have hbDen0 : (bDen : ENNReal) ≠ 0 := by exact_mod_cast hbDen0Nat
  have hqNum0 : (qNum : ENNReal) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqPosNat)
  have hcDenTop : (cDen : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top cDen
  have hqDenTop : (qDen : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top qDen
  have hbDenTop : (bDen : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top bDen
  have hqPos : 0 < (qNum : ENNReal) / (qDen : ENNReal) :=
    ENNReal.div_pos hqNum0 hqDenTop
  have hqLe : (qNum : ENNReal) / (qDen : ENNReal) ≤ 1 := by
    rw [ENNReal.div_le_iff hqDen0 hqDenTop]
    simpa only [one_mul] using (show (qNum : ENNReal) ≤ qDen from by exact_mod_cast hqLeNat)
  have hqTop : (qNum : ENNReal) / (qDen : ENNReal) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top qNum) hqDen0
  have hcertENN : (cNum : ENNReal) * qDen * bDen ≤
      (bNum : ENNReal) * cDen * qNum := by
    exact_mod_cast hcertNat
  refine ⟨hqPos, hqLe, ENNReal.sub_lt_self (by norm_num) (by norm_num) hqPos.ne', ?_⟩
  rw [ENNReal.div_le_iff hqPos.ne' hqTop]
  rw [ENNReal.div_le_iff hcDen0 hcDenTop]
  have hRhs : ((bNum : ENNReal) / (bDen : ENNReal)) *
        ((qNum : ENNReal) / (qDen : ENNReal)) * (cDen : ENNReal) =
      (((bNum : ENNReal) * qNum * cDen) / (bDen : ENNReal)) / (qDen : ENNReal) := by
    simp only [div_eq_mul_inv]
    ac_rfl
  rw [hRhs]
  rw [ENNReal.le_div_iff_mul_le (Or.inl hqDen0) (Or.inl hqDenTop)]
  rw [ENNReal.le_div_iff_mul_le (Or.inl hbDen0) (Or.inl hbDenTop)]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hcertENN

/-- `planned.probability.cost`: a checker-accepted certificate and a survivor
    family with geometric decay bound the expected cost of the lift. The cost
    premise holds at the first exit, so the bands outside the null survivor
    intersection are partitioned by that exit and the tail sum applies. -/
theorem kostenErwartung : kostenErwartungAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl Form _ E B S h hb
    kosten cNum cDen qNum qDen bNum bDen
  intro hpruefe ueberlebt hmeas hanti hdecay hkosten
  classical
  let q : ENNReal := (qNum : ENNReal) / (qDen : ENNReal)
  let c : ENNReal := (cNum : ENNReal) / (cDen : ENNReal)
  have hdaten := kostenZertifikat cNum cDen qNum qDen bNum bDen hpruefe
  have hqLe' : q ≤ 1 := by simpa only [q] using hdaten.2.1
  letI : MeasureTheory.IsProbabilityMeasure hb.mu := hb.istWMass
  let X : Band → Nat := fun band => if h : ∃ n, band ∉ ueberlebt n then Nat.find h else 0
  have hXspec : ∀ band : Band, (∃ n, band ∉ ueberlebt n) →
      band ∉ ueberlebt (X band) := by
    intro band hex
    dsimp only [X]
    rw [dif_pos hex]
    exact Nat.find_spec hex
  have hXmin : ∀ (band : Band) (m : Nat), (∃ n, band ∉ ueberlebt n) →
      m < X band → band ∈ ueberlebt m := by
    intro band m hex hm
    dsimp only [X] at hm
    rw [dif_pos hex] at hm
    exact not_not.mp (Nat.find_min hex hm)
  have hnull : hb.mu (⋂ n, ueberlebt n) = 0 :=
    schnittMassNull hb.mu ueberlebt hmeas hanti hdecay
      ⟨hdaten.1, hdaten.2.1, hdaten.2.2.1⟩
  have haeNicht : ∀ᵐ band ∂hb.mu, band ∉ ⋂ n, ueberlebt n := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using hnull
  have hae : ∀ᵐ band ∂hb.mu,
      (kosten (hb.replay band) : ENNReal) ≤ (X band : ENNReal) * c := by
    filter_upwards [haeNicht] with band hband
    have hex : ∃ n, band ∉ ueberlebt n := by
      simpa only [Set.mem_iInter, not_forall] using hband
    have hspec : band ∉ ueberlebt (X band) := hXspec band hex
    have hmin : ∀ m < X band, band ∈ ueberlebt m := fun m hm => hXmin band m hex hm
    simpa only [c] using hkosten band (X band) hspec hmin
  have hkInt : (∫⁻ band, (kosten (hb.replay band) : ENNReal) ∂hb.mu) ≤
      (∫⁻ band, (X band : ENNReal) * c ∂hb.mu) :=
    lintegral_mono_ae hae
  have hcDen0 : (cDen : ENNReal) ≠ 0 := by
    have hall := by
      simpa only [pruefeProb, decide_eq_true_eq] using hpruefe
    have hcDen0Nat : cDen ≠ 0 := hall.1
    exact_mod_cast hcDen0Nat
  have hcTop : c ≠ ⊤ := by
    dsimp only [c]
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top cNum) hcDen0
  have hkInt' : (∫⁻ band, (kosten (hb.replay band) : ENNReal) ∂hb.mu) ≤
      (∫⁻ band, (X band : ENNReal) ∂hb.mu) * c := by
    simpa only [lintegral_mul_const' (μ := hb.mu) c
      (fun band : Band => (X band : ENNReal)) hcTop] using hkInt
  let f : Nat → Band → ENNReal := fun n => (ueberlebt n).indicator (fun _ => (1 : ENNReal))
  have hfMeas : ∀ n, AEMeasurable (f n) hb.mu := fun n => by
    dsimp only [f]
    exact (measurable_const.indicator (hmeas n)).aemeasurable
  have hpoint : ∀ band : Band, (X band : ENNReal) ≤ ∑' n, f n band := by
    intro band
    by_cases hex : ∃ n, band ∉ ueberlebt n
    · calc
        (X band : ENNReal) = ∑ n ∈ Finset.range (X band), (1 : ENNReal) := by
          rw [Finset.sum_const, nsmul_one, Finset.card_range]
        _ = ∑ n ∈ Finset.range (X band), f n band := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnlt : n < X band := Finset.mem_range.mp hn
          have hmem : band ∈ ueberlebt n := hXmin band n hex hnlt
          simp only [f, Set.indicator_of_mem hmem]
        _ ≤ ∑' n, f n band := ENNReal.sum_le_tsum (Finset.range (X band))
    · have hx0 : X band = 0 := by
        dsimp only [X]
        rw [dif_neg hex]
      rw [hx0, Nat.cast_zero]
      exact bot_le
  have htail : (∫⁻ band, (X band : ENNReal) ∂hb.mu) ≤ ∑' n, hb.mu (ueberlebt n) := by
    calc
      (∫⁻ band, (X band : ENNReal) ∂hb.mu) ≤ ∫⁻ band, (∑' n, f n band) ∂hb.mu :=
        lintegral_mono hpoint
      _ = ∑' n, ∫⁻ band, f n band ∂hb.mu := by
        apply lintegral_tsum
        intro n
        exact hfMeas n
      _ = ∑' n, hb.mu (ueberlebt n) := by
        apply tsum_congr
        intro n
        change (∫⁻ band, (ueberlebt n).indicator (fun _ => (1 : ENNReal)) band ∂hb.mu) =
          hb.mu (ueberlebt n)
        rw [lintegral_indicator_const (hmeas n) (1 : ENNReal), one_mul]
  have hgeom : (∑' n, hb.mu (ueberlebt n)) ≤ q⁻¹ := by
    calc
      (∑' n, hb.mu (ueberlebt n)) ≤ ∑' n, (1 - q) ^ n := by
        apply ENNReal.tsum_le_tsum
        intro n
        simpa only [q] using hdecay n
      _ = (1 - (1 - q))⁻¹ := by rw [ENNReal.tsum_geometric]
      _ = q⁻¹ := by rw [ENNReal.sub_sub_cancel (by norm_num) hqLe']
  change (∫⁻ band, (kosten (hb.replay band) : ENNReal) ∂hb.mu) ≤
    (bNum : ENNReal) / (bDen : ENNReal)
  calc
    (∫⁻ band, (kosten (hb.replay band) : ENNReal) ∂hb.mu) ≤
        (∫⁻ band, (X band : ENNReal) ∂hb.mu) * c := hkInt'
    _ ≤ q⁻¹ * c := by
      simpa only [mul_comm] using (mul_le_mul_right (htail.trans hgeom) c)
    _ = ((cNum : ENNReal) / (cDen : ENNReal)) /
          ((qNum : ENNReal) / (qDen : ENNReal)) := by
      simp only [q, c, div_eq_mul_inv, mul_comm]
    _ ≤ (bNum : ENNReal) / (bDen : ENNReal) := hdaten.2.2.2

end Gabbro.Core.Beobachtung
