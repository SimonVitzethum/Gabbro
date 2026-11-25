/-
  File:      core/Core/Fortschritt/VerdraengungLauf.lean
  Subject:   THE PREEMPTION RUN — the interrupt fires at tick zero, the handler steps forever,
             the worker hangs without ever returning.

  The implementation run `ρV` and its ideal mirror `ηV` share states and trace; only the step
  rules differ. The run is admissible (`laufV`) on the fair history (`fairV`), the worker hangs
  (`hangV`), the return premise fails (`nretV`), and the run is scheduler-fair (`sfV`): every
  other context is served and the worker is never continuously dispatched.
-/
module

public import Core.Fortschritt.Verdraengung
public import Core.Maschine.SchedulerFair

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

/-- The interrupt step at tick zero displaces the worker. -/
noncomputable def stepV0 : ImplSchritt E_v.einrichtung E_v.system E_v.katalog hwV 0 zV0
    (.interrupt (0, 0), ⟨esV, [Ereignis.interrupt 0 irqV Eintritt.handler]⟩) zV1 :=
  .interrupt rfl ⟨0, irqV, Hv, false, rfl,
    ⟨by decide, by decide, pendingV0, by decide, angebotV_auswahl⟩,
    NimmtUnterbrechung.handler_bei ⟨rfl, rfl⟩ (Nat.le_refl 0),
    zV0_ruht_Hv, rfl, by rw [rV_eq] at hmemV; rw [← labV]; exact hmemV, rfl⟩

/-- Handler steps from tick one on. -/
noncomputable def stepV (t : Nat) : ImplSchritt E_v.einrichtung E_v.system E_v.katalog hwV (t + 1)
    (ZV (t + 1)) (.kontext Hv (), ⟨[], []⟩) (toggleUpdate Hv (ZV (t + 1))) :=
  .kontext rfl ⟨0, rfl, by rw [ZV_kerne_succ]; exact zV1_dispatch,
    by rw [ZV_status_succ]; exact zV1_live_Hv⟩
    ⟨(), rfl, rfl, rfl⟩ (hvAusfuehr (t + 1) (ZV (t + 1)))

/-- The implementation steps, tick by tick. -/
noncomputable def taktV (t : Nat) : Takt (Lauffolge E_v hwV) (KeinSchritt (Lauffolge E_v hwV))
    t (some (ZV t)) (spurV t) (some (ZV (t + 1))) := by
  cases t with
  | zero => exact .schritt rfl (.schritt stepV0)
  | succ t => exact .schritt rfl (.schritt (stepV t))

/-- The ideal interrupt step at tick zero. -/
noncomputable def istepV0 : Maschine.I.Schritt E_v.einrichtung E_v.system E_v.katalog hwV 0 zV0
    (.interrupt (0, 0), ⟨esV, [Ereignis.interrupt 0 irqV Eintritt.handler]⟩) zV1 :=
  .interrupt rfl ⟨0, irqV, Hv, false, rfl,
    ⟨by decide, by decide, pendingV0, by decide, angebotV_auswahl⟩,
    NimmtUnterbrechung.handler_bei ⟨rfl, rfl⟩ (Nat.le_refl 0),
    zV0_ruht_Hv, rfl, by rw [rV_eq] at hmemV; rw [← labV]; exact hmemV, rfl⟩

/-- Ideal handler steps from tick one on. -/
noncomputable def istepV (t : Nat) : Maschine.I.Schritt E_v.einrichtung E_v.system E_v.katalog hwV (t + 1)
    (ZV (t + 1)) (.kontext Hv (), ⟨[], []⟩) (toggleUpdate Hv (ZV (t + 1))) :=
  .kontext rfl ⟨0, rfl, by rw [ZV_kerne_succ]; exact zV1_dispatch,
    by rw [ZV_status_succ]; exact zV1_live_Hv⟩
    ⟨(), rfl, rfl, rfl⟩ (hvAusfuehr (t + 1) (ZV (t + 1)))

/-- The ideal steps, tick by tick. -/
noncomputable def itaktV (t : Nat) : Takt
    (Maschine.I.Schritt E_v.einrichtung E_v.system E_v.katalog hwV)
    (fun t _ => ¬ AbsturzAngeboten E_v.katalog hwV t)
    t (ZV t) (spurV t) (ZV (t + 1)) := by
  cases t with
  | zero => exact .schritt rfl (.schritt istepV0)
  | succ t => exact .schritt rfl (.schritt (istepV t))

noncomputable def sV : AussenStart :=
  Classical.choose (zulStart_erfuellbar fairV.hardware wBildV_gueltig)

theorem zulV : E_v.ZulStart HV sV :=
  Classical.choose_spec (zulStart_erfuellbar fairV.hardware wBildV_gueltig)

/-- The implementation run: one preemption, then handler steps forever. -/
noncomputable def ρV : Maschine.Lauf E_v :=
  ⟨sV, hwV, ⟨fun t => some (ZV t), spurV, taktV⟩⟩

/-- The ideal mirror run. -/
noncomputable def ηV : Maschine.I.Lauf E_v :=
  ⟨sV, HV, hwV, ⟨ZV, spurV, itaktV⟩, fun _ => none⟩

theorem spurV_zero : spurV 0 =
    some (.interrupt (0, 0), ⟨esV, [Ereignis.interrupt 0 irqV Eintritt.handler]⟩) := rfl

theorem spurV_succ (t : Nat) : spurV (t + 1) = some (.kontext Hv (), ⟨[], []⟩) :=
  fun _ => rfl

theorem ρV_spur : ∀ t, ρV.zeit.spur t = spurV t := fun _ => rfl

theorem ηV_spur : ∀ t, ηV.zeit.spur t = spurV t := fun _ => rfl

theorem ηV_zustand : ∀ t, ηV.zeit.zustand t = ZV t := fun _ => rfl

/-- The run is admissible. -/
theorem laufV : Maschine.Laeufe E_v HV ρV :=
  ⟨fairV.hardware, fairV.konform, zulV, rfl⟩

/-- The worker is never discharged on the mirror run. -/
theorem nieV : ∀ t, ¬ Maschine.I.Erledigt ηV A t := by
  intro t herl
  rcases herl with ⟨w, spur, heq⟩ | hcrash | ⟨e, hend⟩
  · cases t with
    | zero =>
      rw [ηV_spur, spurV_zero] at heq
      have hfst := congrArg Prod.fst (Option.some.inj heq)
      cases hfst
    | succ t =>
      rw [ηV_spur, spurV_succ] at heq
      have hfst := congrArg Prod.fst (Option.some.inj heq)
      have hc : Hv = A := SchrittWahl.kontext.inj hfst |>.1
      cases hc
  · cases t with
    | zero =>
      rw [ηV_spur, spurV_zero] at hcrash
      have hfst := congrArg Prod.fst (Option.some.inj hcrash)
      cases hfst
    | succ t =>
      rw [ηV_spur, spurV_succ] at hcrash
      have hfst := congrArg Prod.fst (Option.some.inj hcrash)
      cases hfst
  · rw [ηV_zustand, zV_live_A] at hend
    cases hend

/-- The worker is open on the whole mirror run. -/
theorem offenV : Maschine.I.BleibtOffen ηV A () 0 :=
  ⟨⟨0, zV0_dispatch0⟩, fun t _ => ⟨rfl, zV_live_A t, nieV t⟩⟩

/-- The worker is always enabled on the mirror run. -/
theorem aktivV : Maschine.I.Aktiviert ηV A 0 :=
  Or.inl fun t _ => ⟨(), [togglePlan], toggleUpdate A (ZV t), (), rfl, rfl, rfl⟩

/-- The worker hangs: fair history, open, enabled, never discharged. -/
theorem hangV : Maschine.I.Haengt E_v ρV ηV A :=
  ⟨fairV, 0, (), offenV, aktivV⟩

/-- No return: the displaced worker is never dispatched again. -/
theorem nretV : ¬ Maschine.VerdraengungKehrtZurueck E_v ρV := by
  intro hret
  obtain ⟨t', ht', k', z', hz', hd⟩ := hret A 0 0
    ⟨zV0, rfl, zV0_dispatch0, zV0_live_A⟩ ⟨(0, 0), _, rfl⟩
  have hzz : ρV.zeit.zustand t' = some (ZV t') := rfl
  have hseq : z' = ZV t' := Option.some.inj (hzz.symm.trans hz')
  rw [hseq] at hd
  obtain ⟨m, rfl⟩ : ∃ m, t' = m + 1 := ⟨t' - 1, by omega⟩
  exact nirgendsV (m + 1) k' (Nat.succ_pos m) hd

/-- The run is scheduler-fair: the handler is served forever, the worker is never
    continuously dispatched, and no other context ever runs. -/
theorem sfV : Maschine.SchedulerFair E_v ρV := by
  intro a c ready opp n hn
  by_cases hcA : c = A
  · subst hcA
    obtain ⟨s, hs, dispJ, _, _, _, _, _, _, _, _, _⟩ :=
      ready (max a 1) (Nat.le_max_left _ _)
    have hseq : s = ZV (max a 1) := (Option.some.inj hs).symm
    obtain ⟨k, hk⟩ := dispJ
    rw [hseq] at hk
    have h1 : 0 < max a 1 := by omega
    exact (nirgendsV (max a 1) k h1 hk).elim
  · by_cases hcH : c = Hv
    · subst hcH
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (n := max n 1) (by omega)
      exact ⟨max n 1, Nat.le_max_left n 1, (), ⟨[], []⟩, by rw [hm]; rfl⟩
    · obtain ⟨s, hs, dispJ, _, _, _, _, _, _, _, _, _⟩ :=
        ready (max a 1) (Nat.le_max_left _ _)
      have hseq : s = ZV (max a 1) := (Option.some.inj hs).symm
      obtain ⟨k, hk⟩ := dispJ
      rw [hseq] at hk
      rcases nurV (max a 1) k c hk with ⟨h0, rfl⟩ | ⟨_, hc⟩
      · exact absurd h0 (by omega)
      · exact (hcH hc).elim

end Gabbro.Core.Fortschritt
