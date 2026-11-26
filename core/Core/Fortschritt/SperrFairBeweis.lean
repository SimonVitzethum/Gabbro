/-
  File:      Core/Fortschritt/SperrFairBeweis.lean
  Subject:   Discharge of the two non-vacuous progress sentences.

  The old vacuous discharge (through `faire_umgebung_nicht_eindeutig`) is deleted with the
  `∀ h'` premise it fed on. The substantive chain: `SperrHalterImplBereitAussage` (per-cut
  impl bridge, proved from its agreement premise) supplies `SchedulerFair` readiness; the
  opportunity-alignment premise supplies the second `SchedulerFair` antecedent; the stepped
  holder accumulates `H + 1` own steps and `sperr_freigabe_bedingt` releases with the bound.
  Where ownership breaks early, the hold bound itself discharges the release
  (`besitzwechsel_ist_gibt` + `HalteSchranken`). `SperrWarteFairAussage` follows:
  `SperrFreigabeAussage` discharges the `hgibt` premise of `sperr_warte_schranke_bis`
  (fuel `i`).
-/
module

public import Core.Fortschritt.SperrFair
public import Core.Fortschritt.SperrFreigabe

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

/-- Non-triviality of the impl bridge: the waiting twin satisfies every state-side premise
    at cut zero — live, dispatched, release-offering holder on a crash-free cut — yet no
    implementation step exists for the holder (its rule stays silent). The agreement premise
    of `SperrHalterImplBereitAussage` is hence load-bearing; the section row is covered by
    `sperr_freigabe_ohne_abschnitt_widerlegt`. -/
theorem sperrHalterImplBereit_nichtTrivial :
    (∃ s, ρ_w.zeit.zustand 0 = some s ∧ (s.sperren ()).besitzer = some stuckHalter ∧
      SperrHalterBereit E_wait s () stuckHalter ∧ s.status stuckHalter = .laeuft ∧
      (∃ k, (s.kerne k).laeuft = some stuckHalter) ∧ (ρ_w.hw.angebot 0).crash = false) ∧
    ¬ ∃ s w plan u spur s', ρ_w.zeit.zustand 0 = some s ∧
      E_wait.system.ImplSchritt stuckHalter s w [plan] u ∧
      FuehrtSchrittAus E_wait.einrichtung 0 stuckHalter s u plan spur s' := by
  refine ⟨⟨sW0, rfl, rfl, ew_halter_bereit, sW0_live _, ⟨0, sW0_kerne0⟩, hw2_crash 0⟩, ?_⟩
  rintro ⟨s, _, _, _, _, _, hzs, himpl, _⟩
  have hss : s = sW0 := Option.some.inj (hzs.symm.trans rfl)
  subst hss
  obtain ⟨i, _, himpl⟩ := himpl
  cases i
  exact absurd (Kontext.faden.inj himpl.1) (by decide)

/-- The impl bridge fires the ideal `geben` offer on the implementation side: eligibility
    unfolds the ideal step, the agreement premise turns it into the implementation step
    with its protocol execution. -/
theorem sperrHalterImplBereit_aus : SperrHalterImplBereitAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl ι inst E ρ t l h hsec hne hstate hagree
  obtain ⟨s, hzs, hown, hbereit, _, _, _⟩ := hstate
  obtain ⟨_, _, w, plan, u, hisch, hakt, _⟩ := hbereit hne
  obtain ⟨u', himpl, spur, s', hex⟩ := hagree s w plan u hzs hisch hakt hown
  exact ⟨s, w, plan, u', spur, s', hzs, himpl, hex⟩

/-- A marked cut inside the window forces the count up. -/
theorem zaehle_ge_one_of_mem (m : Nat → Bool) (a d t : Nat) (hlt : t < d)
    (h : m (a + t) = true) : 1 ≤ I.zaehle m a d := by
  induction d with
  | zero => exact absurd hlt (Nat.not_lt_zero t)
  | succ d ih =>
    by_cases heq : t = d
    · subst heq
      have hif : (if m (a + t) then 1 else 0) = 1 := if_pos h
      simp only [I.zaehle, hif]
      omega
    · have hlt' : t < d := by omega
      have hih := ih hlt'
      by_cases hif : m (a + d) = true
      · simp only [I.zaehle, if_pos hif]
        omega
      · simp only [I.zaehle, if_neg hif, Nat.add_zero]
        exact hih

/-- A hardware crash-free suffix never records a crash: a recorded crash step carries
    its hardware offer. -/
theorem spur_kein_absturz_aus_hw {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type}
    [DecidableEq L] {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}
    {ρ : Maschine.Lauf E} {b : Nat}
    (h : ∀ k, b ≤ k → (ρ.hw.angebot k).crash = false) :
    ∀ k, b ≤ k → ρ.zeit.spur k ≠ some (.absturz, absturzSpur) := by
  intro k hk hcon
  have htakt := ρ.zeit.takt k
  cases htakt with
  | wartet label _ _ =>
    rw [label] at hcon
    cases hcon
  | schritt label step =>
    cases step with
    | schritt h =>
      cases h with
      | kontext _ _ _ _ =>
        have heq := Option.some.inj (label.symm.trans hcon)
        have hfst := congrArg Prod.fst heq
        cases hfst
      | antwort _ _ =>
        have heq := Option.some.inj (label.symm.trans hcon)
        have hfst := congrArg Prod.fst heq
        cases hfst
      | interrupt _ _ =>
        have heq := Option.some.inj (label.symm.trans hcon)
        have hfst := congrArg Prod.fst heq
        cases hfst
      | absturz hab =>
        have hoffer := hab.1.2
        rw [h k hk] at hoffer
        exact Bool.false_ne_true hoffer

/-- The strengthened release sentence: with the impl bridge and the opportunity alignment,
    the holder is stepped until the hold bound forces its release. Where ownership breaks
    early, the hold bound itself discharges the release. -/
theorem sperr_freigabe_aus_scheduler : SperrFreigabeAussage := by
  classical
  intro L Ort Wert Raum Lok Grund Bedingung Wahl F inst E ρ hU l h H b s
    hbereit hhalte hhalten hsec hrun hfair hsched hret hagree hausricht hzs hown hcrash
  have hne : E.schranken.halten l ≠ none := by
    rw [hhalten]
    exact Option.some_ne_none H
  have hcrash_spur : ∀ k, b ≤ k → ρ.zeit.spur k ≠ some (.absturz, absturzSpur) :=
    spur_kein_absturz_aus_hw hcrash
  have hsome : ∀ t, b ≤ t → ∃ s', ρ.zeit.zustand t = some s' := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ⟨s, hzs⟩
    | succ m hm ih =>
      obtain ⟨sm, hsm⟩ := ih
      have htakt := ρ.zeit.takt m
      rw [hsm] at htakt
      cases htakt with
      | wartet _ heq _ => exact ⟨sm, heq⟩
      | schritt _ step =>
        obtain ⟨s', hs'⟩ := lauffolge_bleibt_some step
        exact ⟨s', hs'⟩
  by_cases hperp : ∀ t, b ≤ t → ∀ s', ρ.zeit.zustand t = some s' →
      (s'.sperren l).besitzer = some h
  · -- Perpetual ownership: readiness holds on the whole suffix, so the scheduler fires.
    have hready : ∀ t, b ≤ t → ∃ s, ρ.zeit.zustand t = some s ∧
        (∃ k, (s.kerne k).laeuft = some h) ∧ s.status h = .laeuft ∧
        (ρ.hw.angebot t).crash = false ∧
        ∃ w plan u spur s', E.system.ImplSchritt h s w [plan] u ∧
          FuehrtSchrittAus E.einrichtung t h s u plan spur s' := by
      intro t ht
      obtain ⟨s', hs'⟩ := hsome t ht
      have hownt := hperp t ht s' hs'
      have hb := hbereit t s' ht hs' hownt
      obtain ⟨hlive, hdisp, w, plan, u, hisch, hakt, _⟩ := hb hne
      obtain ⟨u', himpl, spur, s'', hex⟩ := hagree t s' w plan u ht hs' hisch hakt hownt
      exact ⟨s', hs', hdisp, hlive, hcrash t ht, w, plan, u', spur, s'', himpl, hex⟩
    have hsteps : ∀ n, b ≤ n → ∃ t, n ≤ t ∧ ∃ w spur,
        ρ.zeit.spur t = some (.kontext h w, spur) :=
      hsched b h hready hausricht
    have hmany : ∀ k, ∃ n, k ≤ Kontextkosten ρ h b n := by
      intro k
      induction k with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ k ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨t, ht, w, spur, hst⟩ := hsteps (b + n) (Nat.le_add_right b n)
        refine ⟨t + 1 - b, ?_⟩
        have hKT : ∀ m, Kontextkosten ρ h b m = I.zaehle (fun t => match ρ.zeit.spur t with
            | some (.kontext d _, _) => decide (h = d)
            | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false) b m :=
          fun m => rfl
        rw [hKT] at hn ⊢
        have hmt : (fun t => match ρ.zeit.spur t with
            | some (.kontext d _, _) => decide (h = d)
            | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false) t = true := by
          simp only [hst, decide_eq_true_eq]
        have heq : n + ((t + 1 - b) - n) = t + 1 - b := by omega
        have hadd : I.zaehle (fun t => match ρ.zeit.spur t with
            | some (.kontext d _, _) => decide (h = d)
            | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false)
            b (n + ((t + 1 - b) - n)) =
            I.zaehle (fun t => match ρ.zeit.spur t with
              | some (.kontext d _, _) => decide (h = d)
              | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false)
            b n + I.zaehle (fun t => match ρ.zeit.spur t with
              | some (.kontext d _, _) => decide (h = d)
              | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false)
            (b + n) ((t + 1 - b) - n) :=
          zaehle_add _ _ _ _
        rw [heq] at hadd
        have h1 : 1 ≤ I.zaehle (fun t => match ρ.zeit.spur t with
            | some (.kontext d _, _) => decide (h = d)
            | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false)
            (b + n) ((t + 1 - b) - n) := by
          refine zaehle_ge_one_of_mem _ _ _ (t - (b + n)) ?_ ?_
          · omega
          · have harg : b + n + (t - (b + n)) = t := by omega
            rw [harg]
            exact hmt
        omega
    obtain ⟨n, hn⟩ := hmany (H + 1)
    obtain ⟨r, hbr, _, hg, hcost'⟩ :=
      sperr_freigabe_bedingt hhalten hhalte hcrash_spur hzs hown hn
    exact ⟨r, hbr, hg, hcost'⟩
  · -- First ownership break: the hold bound discharges the release directly.
    have hex : ∃ t, b ≤ t ∧ ∃ s', ρ.zeit.zustand t = some s' ∧
        (s'.sperren l).besitzer ≠ some h := by
      by_contra hcon
      exact hperp (fun t ht s' hs' => by
        by_contra hne'
        exact hcon ⟨t, ht, s', hs', hne'⟩)
    set t₀ := Nat.find hex with ht0def
    have hspec := Nat.find_spec hex
    obtain ⟨hb0, s₂, hz0, hne0⟩ := hspec
    have hmin : ∀ t, t < t₀ → ¬(b ≤ t ∧ ∃ s', ρ.zeit.zustand t = some s' ∧
        (s'.sperren l).besitzer ≠ some h) :=
      fun t ht => Nat.find_min hex ht
    have htb : b < t₀ := by
      rcases eq_or_lt_of_le hb0 with heq | hlt
      · exfalso
        rw [heq] at hzs
        have hss : s₂ = s := Option.some.inj (hz0.symm.trans hzs)
        subst hss
        exact hne0 hown
      · exact hlt
    have hprev : ∀ t, b ≤ t → t < t₀ → ∀ s', ρ.zeit.zustand t = some s' →
        (s'.sperren l).besitzer = some h := by
      intro t hbt htt s' hs'
      by_contra hcon
      exact hmin t htt ⟨hbt, s', hs', hcon⟩
    set r := t₀ - 1 with hrdef
    have hr1 : r + 1 = t₀ := by omega
    have hbr : b ≤ r := by omega
    obtain ⟨sr, hsr⟩ := hsome r hbr
    have hownr : (sr.sperren l).besitzer = some h := hprev r hbr (by omega) sr hsr
    have hz0' : ρ.zeit.zustand (r + 1) = some s₂ := by
      rw [hr1]
      exact hz0
    obtain ⟨next, hg, hvn⟩ := besitzwechsel_ist_gibt hsr hz0' (hcrash_spur r hbr) hownr hne0
    have hcont : ∀ t, b ≤ t → t < b + (r + 1 - b) →
        ∃ s', ρ.zeit.zustand t = some s' ∧ (s'.sperren l).besitzer = some h := by
      intro t hbt htt
      obtain ⟨s', hs'⟩ := hsome t hbt
      exact ⟨s', hs', hprev t hbt (by omega) s' hs'⟩
    have hle : Kontextkosten ρ h b (r + 1 - b) ≤ H :=
      (hhalte l h b (r + 1 - b) hcont) H hhalten
    have hg' : (sr.sperren l).Gibt h (s₂.sperren l) := by
      rw [hvn]
      exact hg
    exact ⟨r, hbr, ⟨sr, s₂, hsr, hz0', hg'⟩, by omega⟩

/-- Acceptance carries the section row. -/
theorem akzeptiert_abschnitt [DecidableEq L]
    {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F} (h : Akzeptiert E) :
    AbschnittWartefrei E := by
  obtain ⟨lokal, _, _⟩ := h
  obtain ⟨_, _, _, _, _, hsec, _⟩ := lokal
  exact hsec

/-- The waiting-bound sentence: `SperrFreigabeAussage` discharges the `hgibt` premise of
    `sperr_warte_schranke_bis` (fuel `i`). -/
theorem sperr_warte_fair_aus_freigabe : SperrWarteFairAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl F inst E ρ hU l c i H a
    akz hhalte hhalten hrun hfair hsched hret hbereit hagree hausricht hqueue hnodup hcrash
  have hsec : AbschnittWartefrei E := akzeptiert_abschnitt akz
  have hcrash_spur : ∀ k, a ≤ k → ρ.zeit.spur k ≠ some (.absturz, absturzSpur) :=
    spur_kein_absturz_aus_hw hcrash
  refine sperr_warte_schranke_bis i i a (Nat.le_refl _) hhalten hhalte hqueue hnodup hcrash_spur ?_
  intro h b' s' hb hzs hown
  exact sperr_freigabe_aus_scheduler E ρ hU l h H b' s'
    (fun t s'' ht hzs' hown' => hbereit h t s'' (hb.trans ht) hzs' hown')
    hhalte hhalten hsec hrun hfair hsched hret
    (fun t s'' w plan u ht hzs' hisch hakt hown' =>
      hagree h t s'' w plan u (hb.trans ht) hzs' hisch hakt hown')
    (hausricht h b' hb ⟨s', hzs, hown⟩) hzs hown
    (fun k hk => hcrash k (hb.trans hk))

end Gabbro.Core.Fortschritt
