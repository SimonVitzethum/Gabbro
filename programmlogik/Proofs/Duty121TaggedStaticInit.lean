import Duty.Duty121TaggedStaticInit
set_option autoImplicit false
open Gabbro.Body GabbroDuty.Duty121TaggedStaticInit

/-  Written from `gabbro beweise --vorlage`. Every statement below is the unit's own
    logic; the hypotheses a proof needs stand in the statement. `gabbro_auto?` shows
    what the model leaves after its own steps. -/

theorem lies_meets_done : lies_meets_statement := by
  unfold lies_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [lies_pre]
  gabbro_pipeline [lies_body, lies_pre, lies_post, wellFormed, hall] using shapeOf
  -- what is left here is the unit's own logic (`gabbro_auto?` shows it)
  (obtain ⟨n, rfl, h0, h1⟩ := ‹∃ n, _ = some n ∧ _›)
  · exact ⟨_, rfl, hwf, n, by simp, h0, h1⟩

