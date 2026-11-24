/-
  File:      Core/Fortschritt/SperrSchranke.lean
  Subject:   WAITING BOUND AND STARVATION FREEDOM FOR LOCK WAITS (PERFECT-MODEL §3.7, step M8,
             B13 on M9's hold bounds, constructor-independent part).

  From the ticket-lock hand-off (`Sperre`: `Nimmt`/`Gibt`/`anstellen`, strong fairness as
  `uebergabe_nach`) and M9's hold bounds (`HalteSchranken`: the owner's own steps while it
  continuously holds are bounded by the unit's declared `halten` data): a context queued at
  position `i` sees the lock within `i + 1` hand-offs; each hand-off costs its owner at most
   `H + 1` of the owner's own steps (the release step included), for `(i + 1) * (H + 1)` owner
   steps in total. Holder-side progress is counted on the holders' own steps and the final
   acquisition on the waiter's next opportunity. Hardware fairness supplies per-core
   opportunities only — which context runs on them is dispatch, a language obligation the
   checker carries (`SperrHalterHalten` keeps halten-holders live, dispatched and
   geben-offering until hand-off); no scheduler is assumed. A free lock with the waiter at
   the head has its take enabled (`nimmt_am_kopf`); the take itself is the waiter's own step.
-/
module

public import Core.Fortschritt.Klasse
public import Core.Fortschritt.SperrHilfen

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Beobachtung

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- The index-zero case: a head waiter sees the lock within one hand-off. -/
theorem sperr_warte_basis {ρ : Maschine.Lauf E} {l : L} {c : Kontext} {H a : Nat}
    (hqueue0 : ∃ s, ρ.zeit.zustand a = some s ∧ (s.sperren l).schlange[(0 : Nat)]? = some c)
    (hbleibt : ∀ t s, a ≤ t → ρ.zeit.zustand t = some s → (s.sperren l).besitzer ≠ some c →
      c ∈ (s.sperren l).schlange)
    (hgibt : ∀ h b s, a ≤ b → ρ.zeit.zustand b = some s → (s.sperren l).besitzer = some h →
      ∃ r, b ≤ r ∧
        (∃ s₁ s₂, ρ.zeit.zustand r = some s₁ ∧ ρ.zeit.zustand (r + 1) = some s₂ ∧
          (s₁.sperren l).Gibt h (s₂.sperren l)) ∧
        Kontextkosten ρ h b (r + 1 - b) ≤ H + 1)
    (hmono : ∀ t₁ t₂ s₁ s₂ (i₁ i₂ : Nat), a ≤ t₁ → t₁ ≤ t₂ → ρ.zeit.zustand t₁ = some s₁ →
      ρ.zeit.zustand t₂ = some s₂ → (s₁.sperren l).schlange[i₁]? = some c →
      (s₂.sperren l).schlange[i₂]? = some c → i₂ ≤ i₁) :
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
      obtain ⟨q, hsq, hs2q⟩ := gibt_abgeben hgibt
      have hown_r : (s₁.sperren l).besitzer = some h := by rw [hsq]
      have hmem_r :=
        hbleibt r' s₁ hbr hr1 (fun heq' => heq (Option.some.inj (hown_r.symm.trans heq')))
      obtain ⟨i_r, hi_r⟩ := mem_getElem? hmem_r
      have hle : i_r ≤ 0 := hmono a r' s s₁ 0 i_r (Nat.le_refl _) hbr hsa hr1 hidx hi_r
      have hi0 : i_r = 0 := by omega
      cases q with
      | nil =>
        rw [hsq] at hmem_r
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
            have heq : x = Kontextkosten ρ h a (r' + 1 - a) := List.mem_singleton.mp hx
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

/-- The waiting bound: queued at position `i`, the lock reaches the waiter within `i + 1`
    hand-offs, for at most `(i + 1) * (H + 1)` owner steps. -/
theorem sperr_warte_schranke {ρ : Maschine.Lauf E} {l : L} {c : Kontext} {H : Nat} :
    ∀ (fuel i a : Nat), i ≤ fuel →
    E.schranken.halten l = some H →
    HalteSchranken E ρ →
    (∃ s, ρ.zeit.zustand a = some s ∧ (s.sperren l).schlange[i]? = some c) →
    (∀ t s, a ≤ t → ρ.zeit.zustand t = some s → (s.sperren l).besitzer ≠ some c →
      c ∈ (s.sperren l).schlange) →
    (∀ h b s, a ≤ b → ρ.zeit.zustand b = some s → (s.sperren l).besitzer = some h →
      ∃ r, b ≤ r ∧
        (∃ s₁ s₂, ρ.zeit.zustand r = some s₁ ∧ ρ.zeit.zustand (r + 1) = some s₂ ∧
          (s₁.sperren l).Gibt h (s₂.sperren l)) ∧
        Kontextkosten ρ h b (r + 1 - b) ≤ H + 1) →
    (∀ t₁ t₂ s₁ s₂ (i₁ i₂ : Nat), a ≤ t₁ → t₁ ≤ t₂ → ρ.zeit.zustand t₁ = some s₁ →
      ρ.zeit.zustand t₂ = some s₂ → (s₁.sperren l).schlange[i₁]? = some c →
      (s₂.sperren l).schlange[i₂]? = some c → i₂ ≤ i₁) →
    ∃ (b : Nat) (e : List Nat), a ≤ b ∧ (∃ s, ρ.zeit.zustand b = some s ∧
      ((s.sperren l).besitzer = some c ∨
        (∃ h₀ r, (s.sperren l).besitzer = none ∧ (s.sperren l).schlange = h₀ :: r ∧
          ∃ s', (s.sperren l).Nimmt h₀ s'))) ∧
      e.length ≤ i + 1 ∧ (∀ x ∈ e, x ≤ H + 1) ∧ e.sum ≤ (i + 1) * (H + 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i a hle halte hhalte hqueue hbleibt hgibt hmono
    have hi0 : i = 0 := by omega
    subst hi0
    exact sperr_warte_basis hqueue hbleibt hgibt hmono
  | succ fuel ih =>
    intro i a hle halte hhalte hqueue hbleibt hgibt hmono
    cases i with
    | zero => exact sperr_warte_basis hqueue hbleibt hgibt hmono
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
          have hmem_r :=
            hbleibt r s₁ hbr hr1 (fun heq' => heq (Option.some.inj (hown_r.symm.trans heq')))
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
              have hmem2 := hbleibt (r + 1) s₂ (hbr.trans (Nat.le_succ _)) hr2
                (fun heq'' => heq' (Option.some.inj (hnew.symm.trans heq'')))
              obtain ⟨j, hj⟩ := mem_getElem? hmem2
              have hqne : ∃ h₀ rest, q = h₀ :: rest := by
                cases q with
                | nil =>
                  rw [hs2q] at hmem2
                  exact (List.not_mem_nil hmem2).elim
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
                hmono a r s s₁ (i + 1) (j + 1) (Nat.le_refl _) hbr hsa hr1 hidx hjr
              have hjle : j ≤ i := by omega
              have hjfuel : j ≤ fuel := by omega
              obtain ⟨b, e', hb, hreach, hlen', hbound', hsum'⟩ :=
                ih j (r + 1) hjfuel halte hhalte ⟨s₂, hr2, hj⟩
                  (fun t s ht hzs => hbleibt t s (by omega) hzs)
                  (fun h b s hb2 hzs hbs => hgibt h b s (by omega) hzs hbs)
                  (fun t₁ t₂ s₁ s₂ i₁ i₂ ht1 ht2 hz1 hz2 hq1 hq2 =>
                    hmono t₁ t₂ s₁ s₂ i₁ i₂ (by omega) ht2 hz1 hz2 hq1 hq2)
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
              have hmem_r :=
                hbleibt r s₁ hbr hr1 (fun heq' => heq (Option.some.inj (hown_r.symm.trans heq')))
              rw [hsq] at hmem_r
              exact (List.not_mem_nil hmem_r).elim
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

end Gabbro.Core.Fortschritt
