import Duty.DutyProbeTaggedWirdGebaut
set_option autoImplicit false
set_option maxHeartbeats 11300000
open Gabbro.Body GabbroDuty.DutyProbeTaggedWirdGebaut

/-  Written from `gabbro beweise --vorlage`. Every statement below is the unit's own
    logic; the hypotheses a proof needs stand in the statement. `gabbro_auto?` shows
    what the model leaves after its own steps. -/

theorem baut_bar_meets_done : baut_bar_meets_statement := by
  unfold baut_bar_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [baut_bar_pre]
  gabbro_pipeline [baut_bar_body, baut_bar_pre, baut_bar_post, wellFormed, hall] using shapeOf
  -- what is left here is the unit's own logic (`gabbro_auto?` shows it)
  all_goals (refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩)
  all_goals first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr (Or.inl ⟨rfl, _, rfl, ‹_›, ‹_›⟩)

