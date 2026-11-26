/-
  File:      Core/Fortschritt/SperrErfuellbar.lean
  Subject:   JOINT SATISFIABILITY OF THE TWO PREMISE BUNDLES (PERFECT-MODEL §3.7,
              step M8, Teil 2b): the handover run meets every release premise, and the
              ticket run meets every waiting-bound premise — no premise bundle is
              contradictory. Each witness also discharges the corresponding conclusion.
-/
module

public import Core.Fortschritt.SperrE2
public import Core.Fortschritt.SperrAnnahmeE1

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

/-- Every even cut steps `A` on the handover run. -/
theorem spur2_step_A {t : Nat} (h : t % 2 = 0) :
    ∃ w spur, spur2 t = some (.kontext A w, spur) := by
  cases t with
  | zero => exact ⟨(), _, spur2_0⟩
  | succ t =>
    cases t with
    | zero => exact absurd h (by decide)
    | succ n => exact ⟨(), _, spurw_ge2 n h⟩

/-- Every odd cut steps `B` on the handover run. -/
theorem spur2_step_B {t : Nat} (h : t % 2 = 1) :
    ∃ w spur, spur2 t = some (.kontext B w, spur) := by
  cases t with
  | zero => exact absurd h (by decide)
  | succ t =>
    cases t with
    | zero => exact ⟨(), _, spurw1⟩
    | succ n => exact ⟨(), _, spurw_ge2' n h⟩

/-- The handover trace never records an interrupt. -/
theorem spur2_kein_interrupt (t : Nat) (id : Nat × Nat)
    (spur : SchrittSpur Unit Unit) : spur2 t ≠ some (.interrupt id, spur) := by
  intro hcon
  cases t with
  | zero =>
    rw [spur2_0] at hcon
    have hfst := congrArg Prod.fst (Option.some.inj hcon)
    cases hfst
  | succ t =>
    rw [spur2_succ] at hcon
    cases t with
    | zero =>
      rw [spurw1] at hcon
      simp only [ticketB] at hcon
      have hfst := congrArg Prod.fst (Option.some.inj hcon)
      cases hfst
    | succ n =>
      by_cases h : (n + 2) % 2 = 0
      · rw [spurw_ge2 n h] at hcon
        simp only [ticketA] at hcon
        have hfst := congrArg Prod.fst (Option.some.inj hcon)
        cases hfst
      · have h1 : (n + 2) % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one (n + 2) with h0 | h1
          · exact (h h0).elim
          · exact h1
        rw [spurw_ge2' n h1] at hcon
        simp only [ticketB] at hcon
        have hfst := congrArg Prod.fst (Option.some.inj hcon)
        cases hfst

/-- The handover run is admissible. -/
theorem e2_lauf : Laeufe E_2 h2 ρ_2 :=
  ⟨fair2.hardware, fair2.konform, zul_2, rfl⟩

/-- The handover run is scheduler-fair: `A` and `B` step alternately forever. -/
theorem e2_sched : SchedulerFair E_2 ρ_2 := by
  intro a c hready _hopp n _
  by_cases hcA : c = A
  · subst hcA
    obtain ⟨t, ht1, ht2⟩ : ∃ t, n ≤ t ∧ t % 2 = 0 := ⟨n + n % 2, by omega, by omega⟩
    exact ⟨t, ht1, spur2_step_A ht2⟩
  · by_cases hcB : c = B
    · subst hcB
      obtain ⟨t, ht1, ht2⟩ : ∃ t, n ≤ t ∧ t % 2 = 1 := ⟨n + 1 - n % 2, by omega, by omega⟩
      exact ⟨t, ht1, spur2_step_B ht2⟩
    · obtain ⟨s, hzs, ⟨k, hdisp⟩, _, _, _⟩ := hready a (Nat.le_refl a)
      have hss : s = zs2 a := Option.some.inj (hzs.symm.trans rfl)
      subst hss
      rw [zs2_kerne] at hdisp
      have hdk : dispatch2 k = some c := hdisp
      cases k with
      | zero => exact absurd (Option.some.inj hdk).symm hcA
      | succ k =>
        cases k with
        | zero => exact absurd (Option.some.inj hdk).symm hcB
        | succ k =>
          have hnone : dispatch2 (Nat.succ (Nat.succ k)) = none := rfl
          rw [hdk] at hnone
          cases hnone

/-- The handover run never meets an interrupt. -/
theorem e2_ret : VerdraengungKehrtZurueck E_2 ρ_2 := by
  intro c k t _ hsp
  obtain ⟨id, spur, hsp⟩ := hsp
  exact absurd hsp (spur2_kein_interrupt t id spur)

/-- The holder meets its dispatch core infinitely often. -/
theorem e2_hausricht : ∀ n, 0 ≤ n → ∃ t, n ≤ t ∧ ∃ k, ρ_2.hw.gelegenheit t k ∧
    ∃ s, ρ_2.zeit.zustand t = some s ∧ (s.kerne k).laeuft = some A := by
  intro n _
  obtain ⟨t, ht1, ht2⟩ : ∃ t, n ≤ t ∧ t % 2 = 0 := ⟨n + n % 2, by omega, by omega⟩
  refine ⟨t, ht1, 0, hw2_opp0 ht2, _, rfl, ?_⟩
  cases t with
  | zero => exact s2_0_kerne0
  | succ t => exact s2_1_kerne0

/-- The release bundle holds jointly on the handover run, and the release follows. -/
theorem sperrFreigabe_erfuellbar :
    ∃ (E : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit) (hU : Umgebung)
      (ρ : Maschine.Lauf E) (l : Unit) (h : Kontext) (H b : Nat)
      (s : Zustand Unit Unit Unit Unit Bool Unit),
      (∀ t s', b ≤ t → ρ.zeit.zustand t = some s' → (s'.sperren l).besitzer = some h →
        SperrHalterBereit E s' l h) ∧
      HalteSchranken E ρ ∧ E.schranken.halten l = some H ∧ AbschnittWartefrei E ∧
      Laeufe E hU ρ ∧ FairLaeufe E.katalog hU ρ.hw ∧
      SchedulerFair E ρ ∧ VerdraengungKehrtZurueck E ρ ∧
      (∀ t s w plan u, b ≤ t → ρ.zeit.zustand t = some s →
        E.system.ISchritt h s w [plan] u → plan.aktion = .sperre l .geben →
        (s.sperren l).besitzer = some h →
        ∃ u', E.system.ImplSchritt h s w [plan] u' ∧
          ∃ spur s', FuehrtSchrittAus E.einrichtung t h s u' plan spur s') ∧
      (∀ n, b ≤ n → ∃ t, n ≤ t ∧ ∃ k, ρ.hw.gelegenheit t k ∧
        ∃ s, ρ.zeit.zustand t = some s ∧ (s.kerne k).laeuft = some h) ∧
      ρ.zeit.zustand b = some s ∧ (s.sperren l).besitzer = some h ∧
      (∀ k, b ≤ k → (ρ.hw.angebot k).crash = false) ∧
      ∃ r, b ≤ r ∧
        (∃ s₁ s₂, ρ.zeit.zustand r = some s₁ ∧ ρ.zeit.zustand (r + 1) = some s₂ ∧
          (s₁.sperren l).Gibt h (s₂.sperren l)) ∧
        Kontextkosten ρ h b (r + 1 - b) ≤ H + 1 := by
  refine ⟨E_2, h2, ρ_2, (), A, 5, 0, s2_0, e2_bereit, e2_halte, e2halten, e2_sec,
    e2_lauf, fair2, e2_sched, e2_ret, e2_hagree, e2_hausricht, rfl, rfl,
    fun k _ => hw2_crash k, ?_⟩
  exact sperr_freigabe_aus_scheduler E_2 ρ_2 h2 () A 5 0 s2_0 e2_bereit e2_halte
    e2halten e2_sec e2_lauf fair2 e2_sched e2_ret e2_hagree e2_hausricht rfl rfl
    (fun k _ => hw2_crash k)

/-- No lock is ever owned on the witness run, so holder readiness holds vacuously. -/
theorem e1_besitzer_frei_1 (t : Nat) (s : Zustand Unit Unit Unit Unit Bool Unit)
    (hzs : ρ_1.zeit.zustand t = some s) : (s.sperren ()).besitzer = none :=
  e1_besitzer_frei t s hzs

theorem e1_bereit_w : ∀ (h : Kontext) (t : Nat) (s' : Zustand Unit Unit Unit Unit Bool Unit),
    1 ≤ t → ρ_1.zeit.zustand t = some s' → (s'.sperren ()).besitzer = some h →
    SperrHalterBereit E_1 s' () h := by
  intro h t s' _ hzs hown
  have hfree := e1_besitzer_frei_1 t s' hzs
  rw [hfree] at hown
  cases hown

/-- No `geben` step is ever offered on the witness run, so the impl bridge holds
    vacuously. -/
theorem e1_hagree_w : ∀ (h : Kontext) (t : Nat) (s : Zustand Unit Unit Unit Unit Bool Unit)
    (w : Unit) (plan : SchrittPlan Unit Unit Unit Unit) (u : Zustand Unit Unit Unit Unit Bool Unit),
    1 ≤ t → ρ_1.zeit.zustand t = some s →
    E_1.system.ISchritt h s w [plan] u → plan.aktion = .sperre () .geben →
    (s.sperren ()).besitzer = some h →
    ∃ u', E_1.system.ImplSchritt h s w [plan] u' ∧
      ∃ spur s', FuehrtSchrittAus E_1.einrichtung t h s u' plan spur s' := by
  intro h t s w plan u _ _ hisch hakt _
  obtain ⟨i, _, himpl⟩ := hisch
  cases i with
  | unit =>
    have himpl' : e1Regel c s w [plan] u := himpl
    rcases himpl' with ⟨next, _, hpeq, _⟩ | ⟨hpeq, _⟩
    · obtain rfl := (List.cons.inj hpeq).1
      have htp : ticketPlan.aktion = .sperre () .ticket := rfl
      rw [htp] at hakt
      cases hakt
    · obtain rfl := (List.cons.inj hpeq).1
      have hsp : stutterPlan.aktion = .intern := rfl
      rw [hsp] at hakt
      cases hakt

/-- No lock is ever owned on the witness run, so the alignment holds vacuously. -/
theorem e1_hausricht_w : ∀ (h : Kontext) (b : Nat), 1 ≤ b →
    (∃ s, ρ_1.zeit.zustand b = some s ∧ (s.sperren ()).besitzer = some h) →
    ∀ n, b ≤ n → ∃ t, n ≤ t ∧ ∃ k, ρ_1.hw.gelegenheit t k ∧
      ∃ s, ρ_1.zeit.zustand t = some s ∧ (s.kerne k).laeuft = some h := by
  intro h b _ hown
  obtain ⟨s, hzs, hown⟩ := hown
  have hfree := e1_besitzer_frei_1 b s hzs
  rw [hfree] at hown
  cases hown

theorem e1_nodup_at : ∀ s, ρ_1.zeit.zustand 1 = some s → (s.sperren ()).schlange.Nodup := by
  intro s hzs
  have hss : s = S_c := Option.some.inj (hzs.symm.trans rfl)
  subst hss
  exact e1_nodup_Sc

/-- The waiting-bound bundle holds jointly on the ticket run, and the bound follows. -/
theorem sperrWarteFair_erfuellbar :
    ∃ (E : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit) (hU : Umgebung)
      (ρ : Maschine.Lauf E) (l : Unit) (c : Kontext) (i H a : Nat),
      Akzeptiert E ∧ HalteSchranken E ρ ∧ E.schranken.halten l = some H ∧
      Laeufe E hU ρ ∧ FairLaeufe E.katalog hU ρ.hw ∧
      SchedulerFair E ρ ∧ VerdraengungKehrtZurueck E ρ ∧
      (∀ h t s', a ≤ t → ρ.zeit.zustand t = some s' → (s'.sperren l).besitzer = some h →
        SperrHalterBereit E s' l h) ∧
      (∀ h t s w plan u, a ≤ t → ρ.zeit.zustand t = some s →
        E.system.ISchritt h s w [plan] u → plan.aktion = .sperre l .geben →
        (s.sperren l).besitzer = some h →
        ∃ u', E.system.ImplSchritt h s w [plan] u' ∧
          ∃ spur s', FuehrtSchrittAus E.einrichtung t h s u' plan spur s') ∧
      (∀ h b, a ≤ b → (∃ s, ρ.zeit.zustand b = some s ∧ (s.sperren l).besitzer = some h) →
        ∀ n, b ≤ n → ∃ t, n ≤ t ∧ ∃ k, ρ.hw.gelegenheit t k ∧
          ∃ s, ρ.zeit.zustand t = some s ∧ (s.kerne k).laeuft = some h) ∧
      (∃ s, ρ.zeit.zustand a = some s ∧ (s.sperren l).schlange[i]? = some c) ∧
      (∀ s, ρ.zeit.zustand a = some s → (s.sperren l).schlange.Nodup) ∧
      (∀ k, a ≤ k → (ρ.hw.angebot k).crash = false) ∧
      ∃ (b : Nat) (e : List Nat), a ≤ b ∧
        (∃ s, ρ.zeit.zustand b = some s ∧
          ((s.sperren l).besitzer = some c ∨
            (∃ h₀ r, (s.sperren l).besitzer = none ∧ (s.sperren l).schlange = h₀ :: r ∧
              ∃ s', (s.sperren l).Nimmt h₀ s'))) ∧
        e.length ≤ i + 1 ∧ (∀ x ∈ e, x ≤ H + 1) ∧ e.sum ≤ (i + 1) * (H + 1) := by
  refine ⟨E_1, h2, ρ_1, (), A, 0, 5, 1, akzeptiert_E_1, e1_halte, e1halten, e1_lauf,
    fair2, e1_sched, e1_ret, e1_bereit_w, e1_hagree_w, e1_hausricht_w,
    ⟨S_c, rfl, rfl⟩, e1_nodup_at, fun k _ => hw2_crash k, ?_⟩
  exact sperr_warte_fair_aus_freigabe E_1 ρ_1 h2 () A 0 5 1 akzeptiert_E_1 e1_halte
    e1halten e1_lauf fair2 e1_sched e1_ret e1_bereit_w e1_hagree_w e1_hausricht_w
    ⟨S_c, rfl, rfl⟩ e1_nodup_at (fun k _ => hw2_crash k)

end Gabbro.Core.Fortschritt
