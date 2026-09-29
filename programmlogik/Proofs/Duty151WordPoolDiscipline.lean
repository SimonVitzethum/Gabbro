import Duty.Duty151WordPoolDiscipline
set_option autoImplicit false
open Gabbro.Body GabbroDuty.Duty151WordPoolDiscipline

/-  Written from `gabbro beweise --vorlage`. Every statement below is the unit's own
    logic; the hypotheses a proof needs stand in the statement. `gabbro_auto?` shows
    what the model leaves after its own steps. -/

theorem lies_byte_meets_done : lies_byte_meets_statement := by
  unfold lies_byte_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_i, e_i, lo_i, hi_i⟩ := shape_intIn s "i" _ _ (and_left _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [lies_byte_pre, e_i]
  gabbro_pipeline [lies_byte_body, lies_byte_pre, lies_byte_post, wellFormed, e_i, hall] using shapeOf
  -- what is left here is the unit's own logic (`gabbro_auto?` shows it)
  all_goals (exact absurd ‹Int.tdiv _ _ < 0› (Int.not_lt.mpr (Int.tdiv_nonneg ‹0 ≤ (_ : Int)› (Int.pow_nonneg (by decide)))))

theorem lies_wort_meets_done : lies_wort_meets_statement := by
  unfold lies_wort_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_w, e_w, lo_w, hi_w⟩ := shape_intIn s "w" _ _ (and_left _ _ _ hpre)
  obtain ⟨n_WPOOL_w_w, h_WPOOL_w_w, lo_WPOOL_w_w, hi_WPOOL_w_w⟩ := WF_intIn shapeOf s.world (.slot "WPOOL" w_w "w") _ _ hwf rfl
  have hall := hpre
  gabbro_simp_at hall [lies_wort_pre, e_w, h_WPOOL_w_w]
  gabbro_pipeline [lies_wort_body, lies_wort_pre, lies_wort_post, wellFormed, e_w, h_WPOOL_w_w, hall] using shapeOf
  -- what is left here is the unit's own logic (`gabbro_auto?` shows it)
  all_goals (exact absurd ‹Int.tdiv _ _ < 0› (Int.not_lt.mpr (Int.tdiv_nonneg ‹0 ≤ (_ : Int)› (Int.pow_nonneg (by decide)))))

