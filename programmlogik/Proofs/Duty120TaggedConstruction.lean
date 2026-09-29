import Duty.Duty120TaggedConstruction
set_option autoImplicit false
open Gabbro.Body GabbroDuty.Duty120TaggedConstruction

/-  Written from `gabbro beweise --vorlage`. Every statement below is the unit's own
    logic; the hypotheses a proof needs stand in the statement. `gabbro_auto?` shows
    what the model leaves after its own steps. -/

theorem baue_meets_done : baue_meets_statement := by
  unfold baue_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_kurz, e_kurz⟩ := shape_bool s "kurz" (and_left _ _ _ hpre)
  obtain ⟨w_x, e_x, lo_x, hi_x⟩ := shape_intIn s "x" _ _ (and_right _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [baue_pre, e_kurz, e_x]
  gabbro_pipeline [baue_body, baue_pre, baue_post, wellFormed, e_kurz, e_x, hall] using shapeOf
  -- what is left here is the unit's own logic (`gabbro_auto?` shows it)
  all_goals (refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩)
  all_goals first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr (Or.inl ⟨rfl, _, rfl, ‹_›, ‹_›⟩)

theorem nimm_meets_done : nimm_meets_statement := by
  unfold nimm_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_m, p_m, e_m, c_m⟩ := shape_sum s "m" _ hpre
  have hall := hpre
  gabbro_simp_at hall [nimm_pre, e_m]
  gabbro_pipeline [nimm_body, nimm_pre, nimm_post, wellFormed, e_m, c_m, hall] using shapeOf
  -- what is left here is the unit's own logic (`gabbro_auto?` shows it)
  all_goals (refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩)
  all_goals first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr (Or.inl ⟨rfl, _, rfl, ‹_›, ‹_›⟩)

