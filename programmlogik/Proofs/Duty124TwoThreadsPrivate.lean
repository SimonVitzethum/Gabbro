import Duty.Duty124TwoThreadsPrivate
set_option autoImplicit false
set_option maxHeartbeats 11300000
open Gabbro.Body GabbroDuty.Duty124TwoThreadsPrivate

/-  Written from `gabbro beweise --vorlage`. Every statement below is the unit's own
    logic; the hypotheses a proof needs stand in the statement. `gabbro_auto?` shows
    what the model leaves after its own steps. -/

theorem hauptA_meets_done : hauptA_meets_statement := by
  unfold hauptA_meets_statement
  intro ρ s hwf hpre c_lock_acquire_L fr_lock_acquire_L c_lock_release_L fr_lock_release_L c_pruefeA fr_pruefeA c_setze fr_setze
  simp only [wellFormed] at hwf ⊢
  have hall := hpre
  gabbro_simp_at hall [hauptA_pre]
  gabbro_pipeline [hauptA_body, hauptA_pre, hauptA_post, wellFormed, lock_acquire_L_pre, lock_acquire_L_requires, lock_acquire_L_post, lock_acquire_L_writes, Frame_read _ _ _ fr_lock_acquire_L, lock_release_L_pre, lock_release_L_requires, lock_release_L_post, lock_release_L_writes, Frame_read _ _ _ fr_lock_release_L, pruefeA_pre, pruefeA_requires, pruefeA_post, pruefeA_writes, Frame_read _ _ _ fr_pruefeA, setze_pre, setze_requires, setze_post, setze_writes, Frame_read _ _ _ fr_setze, hall] using shapeOf
  -- what is left here is the unit's own logic (`gabbro_auto?` shows it)
  -- what is left is the frame chain: the private table survives the acquire, `setze` and the release
  all_goals (simp_all [Frame_read _ _ _ fr_lock_release_L, Frame_read _ _ _ fr_lock_acquire_L, Frame_read _ _ _ fr_setze, lock_release_L_writes, lock_acquire_L_writes, setze_writes, Place.carrier, Gabbro.Body.store_elsewhere, Gabbro.Body.store_here])
