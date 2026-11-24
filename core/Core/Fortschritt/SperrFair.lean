/-
  File:      Core/Fortschritt/SperrFair.lean
  Subject:   THE FAIR WAITING BOUND, ASSEMBLED (PERFECT-MODEL §3.7, step M8, Teil 2b).

  `sperr_warte_schranke_bis` (proved): the waiting bound of `SperrSchranke` with the UNSCOPED
  run premises replaced by what the machine actually guarantees — the scoped persistence and
  monotonicity of `SperrErhalt` (until first ownership, crash-free, duplicate-free), keeping
  `hgibt` as the one remaining run hypothesis. The induction splits on first acquisition:
  whoever owns first discharges the bound with an empty cost list; otherwise the scoped lemmas
  apply on the acquisition-free prefix.

  What this design does NOT close (pinned below for Hy4, with proof sketches):
  * `SperrFreigabeAussage`: `hgibt` from `Akzeptiert` + `HalteSchranken` + hardware fairness.
    `SperrGegenbeispiel.halte_gibt_nicht_ab` proves this needs a checker rule that does not
    exist yet (B13 remainder: holders stay live, dispatched and release-enabled). The `w_*`
    chain below fixes the exact handover shape the guard must admit.
  * `SperrWarteFairAussage`: the target sentence — `SperrFreigabeAussage` discharges `hgibt`
    of `sperr_warte_schranke_bis` (fuel `i`).
  * `StarkeWarteLaufAussage`: joint satisfiability with a real holder in front (position
    `1`, genuine handover) — the `E_2` witness data are fixed here, the run lifting is pinned.
-/
module

public import Core.Fortschritt.SperrErhalt
public import Core.Fortschritt.SperrGegenbeispiel
public import Core.Annahme.Annahme

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- The index-zero case with scoped premises: whoever owns first discharges the bound,
    otherwise the scoped lemmas apply on the acquisition-free prefix. -/
theorem sperr_warte_basis_bis {ρ : Maschine.Lauf E} {l : L} {c : Kontext} {H a : Nat}
    (halte : E.schranken.halten l = some H)
    (hhalte : HalteSchranken E ρ)
    (hqueue0 : ∃ s, ρ.zeit.zustand a = some s ∧ (s.sperren l).schlange[(0 : Nat)]? = some c)
    (hnodup : ∀ s, ρ.zeit.zustand a = some s → (s.sperren l).schlange.Nodup)
    (hcrash : ∀ k, a ≤ k → ρ.zeit.spur k ≠ some (.absturz, absturzSpur))
    (hgibt : ∀ h b s, a ≤ b → ρ.zeit.zustand b = some s → (s.sperren l).besitzer = some h →
      ∃ r, b ≤ r ∧
        (∃ s₁ s₂, ρ.zeit.zustand r = some s₁ ∧ ρ.zeit.zustand (r + 1) = some s₂ ∧
          (s₁.sperren l).Gibt h (s₂.sperren l)) ∧
        Kontextkosten ρ h b (r + 1 - b) ≤ H + 1) :
    ∃ (b : Nat) (e : List Nat), a ≤ b ∧ (∃ s, ρ.zeit.zustand b = some s ∧
      ((s.sperren l).besitzer = some c ∨
        (∃ h₀ r, (s.sperren l).besitzer = none ∧ (s.sperren l).schlange = h₀ :: r ∧
          ∃ s', (s.sperren l).Nimmt h₀ s'))) ∧
      e.length ≤ 0 + 1 ∧ (∀ x ∈ e, x ≤ H + 1) ∧ e.sum ≤ (0 + 1) * (H + 1) := by
  obtain ⟨s, hsa, hidx⟩ := hqueue0
  obtain ⟨r, hr⟩ := schlange_kopfform hidx
  cases hown : (s.sperren l).besitzer with
  | some h =>
    by_cases heq : h = c
    · subst heq
      refine ⟨a, [], Nat.le_refl _, ⟨s, hsa, Or.inl hown⟩, ?_, ?_, ?_⟩
      · calc ([] : List Nat).length = 0 := rfl
          _ ≤ 0 + 1 := Nat.zero_le _
      · intro x hx
        exact (List.not_mem_nil hx).elim
      · calc ([] : List Nat).sum = 0 := rfl
          _ ≤ (0 + 1) * (H + 1) := Nat.zero_le _
    · obtain ⟨r', hbr, hg, hcost⟩ := hgibt h a s (Nat.le_refl _) hsa hown
      obtain ⟨s₁, s₂, hr1, hr2, hgibt⟩ := hg
      by_cases hacq : ∃ k sk, a ≤ k ∧ k ≤ r' ∧ ρ.zeit.zustand k = some sk ∧
          (sk.sperren l).besitzer = some c
      · obtain ⟨k, sk, hk1, _, hzs, hownk⟩ := hacq
        refine ⟨k, [], hk1, ⟨sk, hzs, Or.inl hownk⟩, ?_, ?_, ?_⟩
        · calc ([] : List Nat).length = 0 := rfl
            _ ≤ 0 + 1 := Nat.zero_le _
        · intro x hx
          exact (List.not_mem_nil hx).elim
        · calc ([] : List Nat).sum = 0 := rfl
            _ ≤ (0 + 1) * (H + 1) := Nat.zero_le _
      · have hnie : ∀ k s', a ≤ k → k ≤ r' → ρ.zeit.zustand k = some s' →
          (s'.sperren l).besitzer ≠ some c := by
          intro k s' hk1 hk2 hzs hcon
          exact hacq ⟨k, s', hk1, hk2, hzs, hcon⟩
        have hmemq : c ∈ (s.sperren l).schlange := by
          rw [hr]
          exact List.mem_cons.mpr (Or.inl rfl)
        obtain ⟨i_r, hi_r⟩ := mem_getElem? (bleibt_bis_besitz ⟨s, hsa, hmemq⟩
          (fun k h1 _ => hcrash k h1) hnie hbr hr1)
        have hle : i_r ≤ 0 :=
          mono_bis_besitz ⟨s, hsa, hmemq⟩ hnodup (fun k h1 _ => hcrash k h1) hnie
            (Nat.le_refl _) hbr (Nat.le_refl _) hsa hr1 hidx hi_r
        have hi0 : i_r = 0 := by omega
        obtain ⟨q, hsq, hs2q⟩ := gibt_abgeben hgibt
        have hown_r : (s₁.sperren l).besitzer = some h := by rw [hsq]
        cases q with
        | nil =>
          have hmem_r : c ∈ ([] : List Kontext) := by
            have hmem := bleibt_bis_besitz ⟨s, hsa, hmemq⟩
              (fun k h1 _ => hcrash k h1) hnie hbr hr1
            rw [hsq] at hmem
            exact hmem
          exact (List.not_mem_nil hmem_r).elim
        | cons h₀ rest =>
          have hq0 : (s₁.sperren l).schlange[(0 : Nat)]? = some h₀ := by
            simp only [hsq, List.getElem?_cons_zero]
          have h2 : (s₁.sperren l).schlange[(0 : Nat)]? = some c := hi0 ▸ hi_r
          have h₀eq : h₀ = c := Option.some.inj (hq0.symm.trans h2)
          have hred : s₂.sperren l = ⟨some h₀, rest⟩ := hs2q
          refine ⟨r' + 1, [Kontextkosten ρ h a (r' + 1 - a)],
            hbr.trans (Nat.le_succ _), ⟨s₂, hr2, Or.inl ?_⟩, ?_, ?_, ?_⟩
          · simp only [hred]
            exact congrArg Option.some h₀eq
          · calc [Kontextkosten ρ h a (r' + 1 - a)].length = 1 := rfl
              _ ≤ 0 + 1 := by omega
          · intro x hx
            rcases List.mem_cons.mp hx with heq | hx'
            · subst heq
              exact hcost
            · exact (List.not_mem_nil hx').elim
          · have hbnd : ∀ x ∈ [Kontextkosten ρ h a (r' + 1 - a)], x ≤ H + 1 := by
              intro x hx
              have heq : x = Kontextkosten ρ h a (r' + 1 - a) :=
                List.mem_singleton.mp hx
              subst heq
              exact hcost
            have hsum := halter_summe_schranke [Kontextkosten ρ h a (r' + 1 - a)] H hbnd
            calc [Kontextkosten ρ h a (r' + 1 - a)].sum
                ≤ [Kontextkosten ρ h a (r' + 1 - a)].length * (H + 1) := hsum
              _ ≤ (0 + 1) * (H + 1) :=
                Nat.mul_le_mul_right _ (by simp only [List.length_cons, List.length_nil]; omega)
  | none =>
    refine ⟨a, [], Nat.le_refl _, ⟨s, hsa, Or.inr ⟨c, r, hown, hr, ?_⟩⟩, ?_, ?_, ?_⟩
    · cases hs : s.sperren l with
      | mk o qq =>
        rw [hs] at hown hr
        exact nimmt_am_kopf hown hr
    · calc ([] : List Nat).length = 0 := rfl
        _ ≤ 0 + 1 := Nat.zero_le _
    · intro x hx
      exact (List.not_mem_nil hx).elim
    · calc ([] : List Nat).sum = 0 := rfl
        _ ≤ (0 + 1) * (H + 1) := Nat.zero_le _

/-- The waiting bound with scoped premises: queued at `i`, the lock reaches the waiter within
    `i + 1` hand-offs, for at most `(i + 1) * (H + 1)` owner steps. -/
theorem sperr_warte_schranke_bis {ρ : Maschine.Lauf E} {l : L} {c : Kontext} {H : Nat} :
    ∀ (fuel i a : Nat), i ≤ fuel →
    E.schranken.halten l = some H →
    HalteSchranken E ρ →
    (∃ s, ρ.zeit.zustand a = some s ∧ (s.sperren l).schlange[i]? = some c) →
    (∀ s, ρ.zeit.zustand a = some s → (s.sperren l).schlange.Nodup) →
    (∀ k, a ≤ k → ρ.zeit.spur k ≠ some (.absturz, absturzSpur)) →
    (∀ h b s, a ≤ b → ρ.zeit.zustand b = some s → (s.sperren l).besitzer = some h →
      ∃ r, b ≤ r ∧
        (∃ s₁ s₂, ρ.zeit.zustand r = some s₁ ∧ ρ.zeit.zustand (r + 1) = some s₂ ∧
          (s₁.sperren l).Gibt h (s₂.sperren l)) ∧
        Kontextkosten ρ h b (r + 1 - b) ≤ H + 1) →
    ∃ (b : Nat) (e : List Nat), a ≤ b ∧ (∃ s, ρ.zeit.zustand b = some s ∧
      ((s.sperren l).besitzer = some c ∨
        (∃ h₀ r, (s.sperren l).besitzer = none ∧ (s.sperren l).schlange = h₀ :: r ∧
          ∃ s', (s.sperren l).Nimmt h₀ s'))) ∧
      e.length ≤ i + 1 ∧ (∀ x ∈ e, x ≤ H + 1) ∧ e.sum ≤ (i + 1) * (H + 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i a hle halte hhalte hqueue hnodup hcrash hgibt
    have hi0 : i = 0 := by omega
    subst hi0
    exact sperr_warte_basis_bis halte hhalte hqueue hnodup hcrash hgibt
  | succ fuel ih =>
    intro i a hle halte hhalte hqueue hnodup hcrash hgibt
    cases i with
    | zero => exact sperr_warte_basis_bis halte hhalte hqueue hnodup hcrash hgibt
    | succ i =>
      obtain ⟨s, hsa, hidx⟩ := hqueue
      cases hown : (s.sperren l).besitzer with
      | some h =>
        by_cases heq : h = c
        · subst heq
          refine ⟨a, [], Nat.le_refl _, ⟨s, hsa, Or.inl hown⟩, ?_, ?_, ?_⟩
          · calc ([] : List Nat).length = 0 := rfl
              _ ≤ i + 1 + 1 := Nat.zero_le _
          · intro x hx
            exact (List.not_mem_nil hx).elim
          · calc ([] : List Nat).sum = 0 := rfl
              _ ≤ (i + 1 + 1) * (H + 1) := Nat.zero_le _
        · obtain ⟨r, hbr, hg, hcost⟩ := hgibt h a s (Nat.le_refl _) hsa hown
          obtain ⟨s₁, s₂, hr1, hr2, hgibt_step⟩ := hg
          obtain ⟨q, hsq, hs2q⟩ := gibt_abgeben hgibt_step
          have hown_r : (s₁.sperren l).besitzer = some h := by rw [hsq]
          by_cases hacq : ∃ k sk, a ≤ k ∧ k ≤ r ∧ ρ.zeit.zustand k = some sk ∧
              (sk.sperren l).besitzer = some c
          · obtain ⟨k, sk, hk1, _, hzs, hownk⟩ := hacq
            refine ⟨k, [], hk1, ⟨sk, hzs, Or.inl hownk⟩, ?_, ?_, ?_⟩
            · calc ([] : List Nat).length = 0 := rfl
                _ ≤ i + 1 + 1 := Nat.zero_le _
            · intro x hx
              exact (List.not_mem_nil hx).elim
            · calc ([] : List Nat).sum = 0 := rfl
                _ ≤ (i + 1 + 1) * (H + 1) := Nat.zero_le _
          · have hnie : ∀ k s', a ≤ k → k ≤ r → ρ.zeit.zustand k = some s' →
              (s'.sperren l).besitzer ≠ some c := by
              intro k s' hk1 hk2 hzs hcon
              exact hacq ⟨k, s', hk1, hk2, hzs, hcon⟩
            have hmemq : c ∈ (s.sperren l).schlange := List.mem_of_getElem? hidx
            have hmem_r : c ∈ (s₁.sperren l).schlange :=
              bleibt_bis_besitz ⟨s, hsa, hmemq⟩ (fun k h1 _ => hcrash k h1)
                hnie hbr hr1
            cases hnew : (s₂.sperren l).besitzer with
            | some h' =>
              by_cases heq' : h' = c
              · subst heq'
                refine ⟨r + 1, [Kontextkosten ρ h a (r + 1 - a)],
                  hbr.trans (Nat.le_succ _), ⟨s₂, hr2, Or.inl hnew⟩, ?_, ?_, ?_⟩
                · calc [Kontextkosten ρ h a (r + 1 - a)].length = 1 := rfl
                    _ ≤ i + 1 + 1 := by omega
                · exact forall_mem_singleton_le hcost
                · have hsum := halter_summe_schranke [Kontextkosten ρ h a (r + 1 - a)] H
                    (forall_mem_singleton_le hcost)
                  calc [Kontextkosten ρ h a (r + 1 - a)].sum
                      ≤ [Kontextkosten ρ h a (r + 1 - a)].length * (H + 1) := hsum
                    _ ≤ (i + 1 + 1) * (H + 1) :=
                      Nat.mul_le_mul_right _ (by simp only [List.length_cons, List.length_nil]; omega)
              · -- The new owner differs: the waiter kept its queue place; induction below.
                have hnie1 : ∀ k s', a ≤ k → k ≤ r + 1 → ρ.zeit.zustand k = some s' →
                    (s'.sperren l).besitzer ≠ some c := by
                  intro k s' hk1 hk2 hzs hcon
                  by_cases hk : k ≤ r
                  · exact hnie k s' hk1 hk hzs hcon
                  · have hkr : k = r + 1 := by omega
                    subst hkr
                    have hss : s' = s₂ := Option.some.inj (hzs.symm.trans hr2)
                    subst hss
                    exact heq' (Option.some.inj (hnew.symm.trans hcon))
                have hmem2 : c ∈ (s₂.sperren l).schlange :=
                  bleibt_bis_besitz ⟨s, hsa, hmemq⟩ (fun k h1 _ => hcrash k h1)
                    hnie1 (by omega) hr2
                obtain ⟨j, hj⟩ := mem_getElem? hmem2
                have hqne : ∃ h₀ rest, q = h₀ :: rest := by
                  cases q with
                  | nil =>
                    rw [hsq] at hmem_r
                    exact (List.not_mem_nil hmem_r).elim
                  | cons h₀ rest => exact ⟨h₀, rest, rfl⟩
                obtain ⟨h₀, rest, hqcons⟩ := hqne
                have hq1 : (s₁.sperren l).schlange = h₀ :: rest := by rw [hsq, hqcons]
                have hq2 : (s₂.sperren l).schlange = rest := by
                  have hred : (SperrZustand.abgeben ⟨some h, h₀ :: rest⟩).schlange = rest := rfl
                  rw [hs2q, hqcons]
                  exact hred
                have hjr : (s₁.sperren l).schlange[j + 1]? = some c := by
                  rw [hq1, List.getElem?_cons_succ] at ⊢
                  rw [hq2] at hj
                  exact hj
                have hji : j + 1 ≤ i + 1 :=
                  mono_bis_besitz ⟨s, hsa, hmemq⟩ hnodup (fun k h1 _ => hcrash k h1)
                    hnie (Nat.le_refl _) hbr (Nat.le_refl _) hsa hr1 hidx hjr
                have hjle : j ≤ i := by omega
                have hjfuel : j ≤ fuel := by omega
                have hnd1 : (s₁.sperren l).schlange.Nodup :=
                  nodup_bleibt (t := r + 1) hnodup (fun k h1 _ => hcrash k h1)
                    hbr (Nat.le_succ _) hr1
                have hqq : q.Nodup := by
                  rw [hsq] at hnd1
                  exact hnd1
                have hnd2 : (s₂.sperren l).schlange.Nodup := by
                  rw [hs2q]
                  exact abgeben_nodup hqq
                obtain ⟨b, e', hb, hreach, hlen', hbound', hsum'⟩ :=
                  ih j (r + 1) hjfuel halte hhalte ⟨s₂, hr2, hj⟩
                    (fun s hzs => by
                      have hss : s = s₂ := Option.some.inj (hzs.symm.trans hr2)
                      subst hss
                      exact hnd2)
                    (fun k hk => hcrash k (by omega))
                    (fun h b s hb2 hzs hbs => hgibt h b s (by omega) hzs hbs)
                have hbnd : ∀ x ∈ Kontextkosten ρ h a (r + 1 - a) :: e', x ≤ H + 1 := by
                  intro x hx
                  rcases List.mem_cons.mp hx with heq | hx'
                  · subst heq
                    exact hcost
                  · exact hbound' x hx'
                refine ⟨b, Kontextkosten ρ h a (r + 1 - a) :: e',
                  Nat.le_trans (by omega) hb, hreach, ?_, hbnd, ?_⟩
                · simp only [List.length_cons]
                  omega
                · have hsum := halter_summe_schranke _ H hbnd
                  calc (Kontextkosten ρ h a (r + 1 - a) :: e').sum
                      ≤ (Kontextkosten ρ h a (r + 1 - a) :: e').length * (H + 1) := hsum
                    _ ≤ (i + 1 + 1) * (H + 1) :=
                      Nat.mul_le_mul_right _ (by simp only [List.length_cons]; omega)
            | none =>
              cases q with
              | nil =>
                -- No queue at the release, yet the waiter is queued — contradiction.
                have hmem_r' : c ∈ ([] : List Kontext) := by
                  have hmem := bleibt_bis_besitz ⟨s, hsa, hmemq⟩
                    (fun k h1 _ => hcrash k h1) hnie hbr hr1
                  rw [hsq] at hmem
                  exact hmem
                exact (List.not_mem_nil hmem_r').elim
              | cons h₀ rest =>
                -- No owner after the release, yet the queue is nonempty — the new head owns it.
                have hcontra : (s₂.sperren l).besitzer = some h₀ := by
                  have hred : (SperrZustand.abgeben ⟨some h, h₀ :: rest⟩).besitzer = some h₀ := rfl
                  rw [hs2q]
                  exact hred
                rw [hcontra] at hnew
                cases hnew
      | none =>
        cases hq : (s.sperren l).schlange with
        | nil =>
          rw [hq] at hidx
          simp only [List.getElem?_nil] at hidx
          cases hidx
        | cons h₀ rest =>
          refine ⟨a, [], Nat.le_refl _, ⟨s, hsa, Or.inr ⟨h₀, rest, hown, hq, ?_⟩⟩, ?_, ?_, ?_⟩
          · cases hs : s.sperren l with
            | mk o qq =>
              simp only [hs] at hown hq ⊢
              exact nimmt_am_kopf hown hq
          · calc ([] : List Nat).length = 0 := rfl
              _ ≤ i + 1 + 1 := Nat.zero_le _
          · intro x hx
            exact (List.not_mem_nil hx).elim
          · calc ([] : List Nat).sum = 0 := rfl
              _ ≤ (i + 1 + 1) * (H + 1) := Nat.zero_le _

/-- The exact two-deep handover shape the release guard must admit: the stuck holder in front,
    `A` at the head, the waiter `B` at position one — all by computation. -/
theorem w_pos1 : (⟨some stuckHalter, [A, B]⟩ : SperrZustand).schlange[1]? = some B := rfl

theorem w_besitzer :
    (⟨some stuckHalter, [A, B]⟩ : SperrZustand).besitzer = some stuckHalter := rfl

theorem w_besitzer_ne : stuckHalter ≠ B := by decide

theorem w_nodup : [A, B].Nodup :=
  List.nodup_cons.mpr ⟨by decide, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩

theorem w_ticketH : SperrSchritt .ticket stuckHalter SperrZustand.frei ⟨none, [stuckHalter]⟩ :=
  .ticket (by decide) List.not_mem_nil

theorem w_nimmtH : (⟨none, [stuckHalter]⟩ : SperrZustand).Nimmt stuckHalter
    ⟨some stuckHalter, []⟩ :=
  .frei _ _

theorem w_gibtH : (⟨some stuckHalter, [A, B]⟩ : SperrZustand).Gibt stuckHalter
    ⟨some A, [B]⟩ :=
  .besitzer _ _

theorem w_uebergabe1 : SperrZustand.abgeben ⟨some stuckHalter, [A, B]⟩ = ⟨some A, [B]⟩ :=
  rfl

theorem w_uebergabe2 : SperrZustand.abgeben ⟨some A, [B]⟩ = ⟨some B, []⟩ := rfl

/-- MISSING CHECKER RULE (B13 remainder), pinned for Hy4: an accepted unit hands every held
    lock off within the declared hold bound plus the release step, on crash-free fair runs.
    `SperrGegenbeispiel.halte_gibt_nicht_ab` proves `HalteSchranken` plus hardware fairness do
    NOT imply this — the proof needs the release-guard row in the checker table (holders stay
    live, dispatched and release-enabled until hand-off), which does not exist yet. -/
def SperrFreigabeAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F) (ρ : Maschine.Lauf E)
    (l : L) (h : Kontext) (H b : Nat) (s : Zustand L Ort Wert Raum Lok Grund),
    Akzeptiert E → HalteSchranken E ρ → E.schranken.halten l = some H →
    (∀ h', Laeufe E h' ρ → FairLaeufe E.katalog h' ρ.hw) →
    ρ.zeit.zustand b = some s → (s.sperren l).besitzer = some h →
    (∀ k, b ≤ k → ρ.zeit.spur k ≠ some (.absturz, absturzSpur)) →
    ∃ r, b ≤ r ∧
      (∃ s₁ s₂, ρ.zeit.zustand r = some s₁ ∧ ρ.zeit.zustand (r + 1) = some s₂ ∧
        (s₁.sperren l).Gibt h (s₂.sperren l)) ∧
      Kontextkosten ρ h b (r + 1 - b) ≤ H + 1

/-- THE TARGET SENTENCE of M8 Teil 2b, pinned for Hy4: every accepted unit with held bounds
    gives a waiter queued at `i` the lock within `(i + 1) * (H + 1)` owner steps under fair
    hardware — no run premises besides acceptance, hardware fairness and the bounds.
    Proof sketch: `SperrFreigabeAussage` discharges the `hgibt` premise of
    `sperr_warte_schranke_bis` (fuel `i`); the scoped persistence and monotonicity are
    already machine theorems (`bleibt_bis_besitz`, `mono_bis_besitz`, `nodup_bleibt`). -/
def SperrWarteFairAussage : Prop :=
  ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F) (ρ : Maschine.Lauf E)
    (l : L) (c : Kontext) (i H a : Nat),
    Akzeptiert E → HalteSchranken E ρ → E.schranken.halten l = some H →
    (∀ h', Laeufe E h' ρ → FairLaeufe E.katalog h' ρ.hw) →
    (∃ s, ρ.zeit.zustand a = some s ∧ (s.sperren l).schlange[i]? = some c) →
    (∀ s, ρ.zeit.zustand a = some s → (s.sperren l).schlange.Nodup) →
    (∀ k, a ≤ k → ρ.zeit.spur k ≠ some (.absturz, absturzSpur)) →
    ∃ (b : Nat) (e : List Nat), a ≤ b ∧
      (∃ s, ρ.zeit.zustand b = some s ∧
        ((s.sperren l).besitzer = some c ∨
          (∃ h₀ r, (s.sperren l).besitzer = none ∧ (s.sperren l).schlange = h₀ :: r ∧
            ∃ s', (s.sperren l).Nimmt h₀ s'))) ∧
      e.length ≤ i + 1 ∧ (∀ x ∈ e, x ≤ H + 1) ∧ e.sum ≤ (i + 1) * (H + 1)

/-- STRONG SATISFIABILITY with a real holder in front, pinned for Hy4: a run with the waiter
    at position one, a genuine holder ahead and genuine hand-overs. The lock-level chain is
    fixed above (`w_pos1`, `w_gibtH`, `w_uebergabe1`, `w_uebergabe2`).
    Proof sketch: extend `E_1`'s rule with `nehmen`/`geben` alternatives
    (`∃ next, SperrSchritt .nehmen c (s.sperren ()) next ∧ es = [nehmenPlan] ∧ u = s` and the
    `geben` analogue, `u = toggleUpdate c s` for tickets as in `e1Regel`); run the trace
    `frei → [H] → owner H → [H,A] → [H,A,B] → owner A → owner B` with stutter tail; the
    memory side of the owner-changing steps comes from `speicherzug_existiert`; fairness from
    `Umgebung.referenz_fair`; `HalteSchranken` by window analysis (holders own at most two
    ticks each); the release premises from the two `geben` steps with directly counted
    `Kontextkosten`. -/
def StarkeWarteLaufAussage : Prop :=
  ∃ (E : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit) (h : Umgebung)
    (ρ : Maschine.Lauf E) (c : Kontext) (H a : Nat),
    Laeufe E h ρ ∧ FairLaeufe E.katalog h ρ.hw ∧ HalteSchranken E ρ ∧
    E.schranken.halten () = some H ∧
    (∃ s, ρ.zeit.zustand a = some s ∧
      (∃ h', (s.sperren ()).besitzer = some h' ∧ h' ≠ c) ∧
      (s.sperren ()).schlange[1]? = some c) ∧
    (∀ s, ρ.zeit.zustand a = some s → (s.sperren ()).schlange.Nodup) ∧
    (∀ k, a ≤ k → ρ.zeit.spur k ≠ some (.absturz, absturzSpur)) ∧
    (∀ h' b s, a ≤ b → ρ.zeit.zustand b = some s → (s.sperren ()).besitzer = some h' →
      ∃ r, b ≤ r ∧
        (∃ s₁ s₂, ρ.zeit.zustand r = some s₁ ∧ ρ.zeit.zustand (r + 1) = some s₂ ∧
          (s₁.sperren ()).Gibt h' (s₂.sperren ())) ∧
        Kontextkosten ρ h' b (r + 1 - b) ≤ H + 1)

end Gabbro.Core.Fortschritt
