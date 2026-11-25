/-
  File:      Core/Fortschritt/Saetze.lean
  Subject:   GENERIC PROGRESS THEOREMS (PERFECT-MODEL §3.7, step M8): from the per-form
             obligations every checked class holds on every fair run; `waitFree` from the
             run match; `waitFree` excludes weak hangs.

  (a) `klassen_fortschritt_aus_pflichten`: from `FortschrittsPflichten` on a fair run,
  `starvationFree` and `lockFree` hold, hence the per-cut alternatives
  (`Laufabgleich.fortschritt`, `fortschritt_im_lauf`).
  `deadlockFrei_aus_waechter`: `deadlockFree` from the generated guards (`WaechterHalten`:
  no reachable cut, maximal cuts included, holds a closed waiting set).
  `waitfrei_aus_abgleich`: `waitFree` from the run match and the checked stutter bound —
  once a waiting context took more own steps than the bound, one of them discharged it.
  `waitfrei_schliesst_schwaches_haengen_aus`: `waitFree` leaves no weakly hanging context.
-/
module

public import Core.Fortschritt.Klasse

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung
open Gabbro.Core.Ideal

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- Monotonicity of the tick count in the marked predicate. -/
theorem zaehle_mono (m k : Nat → Bool) (a n : Nat)
    (h : ∀ t, a ≤ t → t < a + n → m t = true → k t = true) :
    I.zaehle m a n ≤ I.zaehle k a n := by
  induction n generalizing a with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hsub : ∀ t, a ≤ t → t < a + n → m t = true → k t = true :=
      fun t le lt hm => h t le (by omega) hm
    have le := ih a hsub
    by_cases hm : m (a + n) = true
    · have hk : k (a + n) = true := h (a + n) (Nat.le_add_right _ _) (Nat.lt_succ_self _) hm
      simp only [I.zaehle, if_pos hm, if_pos hk]
      exact Nat.succ_le_succ le
    · simp only [I.zaehle, if_neg hm, Nat.add_zero]
      exact Nat.le_trans le (Nat.le_add_right _ _)

/-- The tick count splits over consecutive intervals. -/
theorem zaehle_add (m : Nat → Bool) (a n₁ n₂ : Nat) :
    I.zaehle m a (n₁ + n₂) = I.zaehle m a n₁ + I.zaehle m (a + n₁) n₂ := by
  induction n₂ with
  | zero => simp only [Nat.add_zero, I.zaehle]
  | succ n₂ ih =>
    have h1 : n₁ + (n₂ + 1) = (n₁ + n₂) + 1 := (Nat.add_assoc n₁ n₂ 1).symm
    have h2 : a + (n₁ + n₂) = (a + n₁) + n₂ := (Nat.add_assoc a n₁ n₂).symm
    rw [h1]
    simp only [I.zaehle]
    rw [h2, ih]
    omega

/-- Distinct marked ticks inside a window are counted. -/
theorem zaehle_ge_length (m : Nat → Bool) (a n : Nat) (L : List Nat)
    (hpair : L.Pairwise (· < ·))
    (hmem : ∀ t ∈ L, a ≤ t ∧ t < a + n ∧ m t = true) :
    L.length ≤ I.zaehle m a n := by
  induction L with
  | nil => exact Nat.zero_le _
  | cons x L ih =>
    have hpair' : L.Pairwise (· < ·) := (List.pairwise_cons.mp hpair).2
    have hfirst : ∀ y ∈ L, x < y := (List.pairwise_cons.mp hpair).1
    have hmem' : ∀ t ∈ L, a ≤ t ∧ t < a + n ∧ m t = true :=
      fun t h => hmem t (List.mem_cons.mpr (Or.inr h))
    have hx := hmem x (List.mem_cons.mpr (Or.inl rfl))
    have hsplit : I.zaehle m a n =
        I.zaehle m a (x + 1 - a) + I.zaehle m (x + 1) (a + n - (x + 1)) := by
      have h1 : (x + 1 - a) + (a + n - (x + 1)) = n := by omega
      have h2 : a + (x + 1 - a) = x + 1 := by omega
      calc I.zaehle m a n
          = I.zaehle m a ((x + 1 - a) + (a + n - (x + 1))) := by rw [h1]
        _ = I.zaehle m a (x + 1 - a) + I.zaehle m (a + (x + 1 - a)) (a + n - (x + 1)) :=
          zaehle_add m a _ _
        _ = I.zaehle m a (x + 1 - a) + I.zaehle m (x + 1) (a + n - (x + 1)) := by rw [h2]
    have htail : L.length ≤ I.zaehle m (x + 1) (a + n - (x + 1)) := by
      apply zaehle_ge_length _ _ _ _ hpair'
      intro t ht
      have h := hmem' t ht
      have hlt := hfirst t ht
      exact ⟨by omega, by omega, h.2.2⟩
    have hhead : 1 ≤ I.zaehle m a (x + 1 - a) := by
      have hxa : a + (x - a) = x := by omega
      have hx1 : x + 1 - a = (x - a) + 1 := by omega
      have hif : (if m (a + (x - a)) then 1 else 0) = 1 := by rw [hxa]; exact if_pos hx.2.2
      calc 1 = 0 + 1 := by omega
        _ ≤ I.zaehle m a (x - a) + 1 := Nat.add_le_add_right (Nat.zero_le _) 1
        _ = I.zaehle m a (x - a) + (if m (a + (x - a)) then 1 else 0) := by rw [hif]
        _ = I.zaehle m a ((x - a) + 1) := by simp only [I.zaehle]
        _ = I.zaehle m a (x + 1 - a) := by rw [hx1]
    simp only [List.length_cons]
    omega

/-- From the per-form obligations on a fair run, `starvationFree` and `lockFree` hold, hence
    the per-cut alternatives — the proof leg of §3.7 over `Laufabgleich.fortschritt`. -/
theorem klassen_fortschritt_aus_pflichten {ρ : Maschine.Lauf E} {η : I.Lauf E}
    {formen : F → Prop} {nutzbar : Nat → Kontext → Prop}
    (matched : I.Laufabgleich ρ η) (valid : I.Laeufe E η)
    (bound : I.StotterSchranke η)
    (pf : I.FortschrittsPflichten (.lockFree formen) ρ η nutzbar)
    (fair : FairLaeufe E.katalog η.umgebung ρ.hw) :
    StarvationFrei ρ η ∧ LockFrei formen η ∧ PerCutFrei η := by
  obtain ⟨nohang, klasse⟩ := matched.fortschritt valid bound pf fair
  exact ⟨nohang, klasse, klasse.1⟩

/-- The per-cut alternatives follow from the rule obligations alone, on every run. -/
theorem fortschritt_am_aus_pflichten {η : I.Lauf E}
    (valid : I.Laeufe E η)
    (fertig : ∀ s c, E.system.kopf s c = none → E.system.fertig s c)
    (regeln : ∀ f, RegelFortschritt E.system f)
    (komponierbar : ∀ f, I.RegelKomponierbar E.einrichtung E.system f) :
    PerCutFrei η := by
  intro t c live disp
  exact I.fortschritt_im_lauf valid fertig regeln komponierbar t c live disp

/-- `deadlockFree` from the generated guards: every cut of the run is a prefix cut with the
    same state, and `WaechterHalten` excludes a closed waiting set at every one of them. -/
theorem deadlockfrei_aus_waechter {η : I.Lauf E}
    (valid : I.Laeufe E η) (h : WaechterHalten E) :
    DeadlockFrei η := by
  intro t hC
  obtain ⟨C, hC⟩ := hC
  obtain ⟨k, _, same⟩ := Zeitlauf.schnitt_deckt η.zeit t
  rw [← same] at hC
  exact (h.2.1 η valid k) ⟨C, hC⟩

/-- `waitFree` from the run match and the checked stutter bound: an open interval without
    discharge is a stutter interval, so the context's own steps on it are private occupancy —
    bounded by the unit's checked length. Exceeding it forces a discharging step. -/
theorem waitfrei_aus_abgleich {ρ : Maschine.Lauf E} {η : I.Lauf E}
    (matched : I.Laufabgleich ρ η) (bound : I.StotterSchranke η) :
    WaitFrei ρ η := by
  intro c f a hhead0 hlive0 hdisp0 hhead hlive hbereit n hcount
  by_contra hcon
  push_neg at hcon
  have hintervall : I.Stotterintervall η c f a n := by
    intro t h1 h2
    refine ⟨hhead t h1, ?_, ?_⟩
    · intro w spur heq
      exact hcon t h1 h2 (Or.inl ⟨w, spur, heq⟩)
    · intro hcrash
      exact hcon t h1 h2 (Or.inr (Or.inl hcrash))
  have hbound := bound c f a n hintervall
  have hbelegt : ∀ t, a ≤ t → t < a + n →
      (match ρ.zeit.spur t with
        | some (.kontext d _, _) => decide (c = d)
        | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false) = true →
      η.belegt t = some c := by
    intro t h1 h2 himp
    cases himp_eq : ρ.zeit.spur t with
    | none => simp only [himp_eq, Bool.false_eq_true] at himp
    | some ev =>
      cases ev with
      | mk wahl spur =>
        cases wahl with
        | kontext d w =>
          simp only [himp_eq] at himp
          have hdc : c = d := decide_eq_true_eq.mp himp
          subst hdc
          have hmatch := matched.spur t
          rw [himp_eq] at hmatch
          rcases hmatch.ideales_etikett with idle | step
          · cases mark : η.belegt t with
            | none =>
              rcases (matched.frei t).mp mark with no | used
              · rw [himp_eq] at no; cases no
              · exact (used idle).elim
            | some d' =>
              obtain ⟨w', _, event, _⟩ := matched.belegt t d' mark
              have hdd : d' = c :=
                (SchrittWahl.kontext.inj
                  (congrArg Prod.fst (Option.some.inj (event.symm.trans himp_eq)))).1
              rw [← hdd]
          · exact (hcon t h1 h2 (Or.inl ⟨w, spur, step⟩)).elim
        | antwort _ => simp only [himp_eq, Bool.false_eq_true] at himp
        | interrupt _ => simp only [himp_eq, Bool.false_eq_true] at himp
        | absturz => simp only [himp_eq, Bool.false_eq_true] at himp
  have himpl_le : Kontextkosten ρ c a n ≤ I.zaehle (fun t => decide (η.belegt t = some c)) a n := by
    have hkk : Kontextkosten ρ c a n =
        I.zaehle (fun t => match ρ.zeit.spur t with
          | some (.kontext d _, _) => decide (c = d)
          | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false) a n := rfl
    rw [hkk]
    apply zaehle_mono
    intro t h1 h2 hm
    have hb : η.belegt t = some c := hbelegt t h1 h2 hm
    show decide (η.belegt t = some c) = true
    rw [hb, decide_eq_true_eq]
  omega

/-- `waitFree` leaves no weakly hanging context: service ticks from `individuell` become own
    implementation steps through `vollzug`, and past the bound one of them discharges the
    open instance. (Strong lock-acquisition hangs are bounded by `SperrSchranke`, not here.) -/
theorem waitfrei_schliesst_schwaches_haengen_aus {ρ : Maschine.Lauf E} {η : I.Lauf E}
    {nutzbar : Nat → Kontext → Prop}
    (hwf : WaitFrei (E := E) ρ η)
    (matched : I.Laufabgleich ρ η) (valid : I.Laeufe E η)
    (bound : I.StotterSchranke η)
    (pf : I.FortschrittsPflichten (.blockierend : I.FortschrittsKlasse F) ρ η nutzbar)
    (fair : FairLaeufe E.katalog η.umgebung ρ.hw)
    {c f a} (opened : I.BleibtOffen η c f a)
    (enabled : ∀ t, a ≤ t → I.Bereit (E := E) (η.zeit.zustand t) c) :
    False := by
  have hact : I.Aktiviert η c a := Or.inl enabled
  -- A chain of bound+1 strictly increasing serviced ticks.
  have build : ∀ k : Nat, ∃ U : Nat, ∃ L : List Nat, L.length = k ∧
      (∀ t ∈ L, a ≤ t ∧ nutzbar t c ∧ I.Bereit (E := E) (η.zeit.zustand t) c) ∧
      L.Pairwise (· < ·) ∧ ∀ t ∈ L, t < U := by
    intro k
    induction k with
    | zero => exact ⟨0, [], rfl, fun t h => (List.not_mem_nil h).elim,
        List.Pairwise.nil, fun t h => (List.not_mem_nil h).elim⟩
    | succ k ih =>
      obtain ⟨U, L, hlen, hmem, hpair, hbound⟩ := ih
      obtain ⟨t, htle, hnut, hber⟩ :=
        pf.individuell fair a c f opened hact (max U a) (Nat.le_max_right _ _)
      have hU : U ≤ t := Nat.le_trans (Nat.le_max_left _ _) htle
      refine ⟨t + 1, L ++ [t], ?_, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
      · intro s hs
        rw [List.mem_append] at hs
        rcases hs with h | h
        · exact hmem s h
        · rw [List.mem_singleton.mp h]
          exact ⟨Nat.le_trans (Nat.le_max_right _ _) htle, hnut, hber⟩
      · rw [List.pairwise_append]
        refine ⟨hpair, List.pairwise_singleton _ _, fun y hy _ hmem' => ?_⟩
        rw [List.mem_singleton.mp hmem']
        exact Nat.lt_of_lt_of_le (hbound y hy) hU
      · intro s hs
        rw [List.mem_append] at hs
        rcases hs with h | h
        · exact Nat.lt_of_lt_of_le (hbound s h) (Nat.le_succ_of_le hU)
        · rw [List.mem_singleton.mp h]
          exact Nat.lt_succ_self _
  obtain ⟨U, L, hlen, hmem, hpair, hbound⟩ := build (E.stotterLaenge f + 1)
  -- Every serviced tick is an own implementation step or discharges at once.
  have hstep : ∀ t ∈ L, (match ρ.zeit.spur t with
      | some (.kontext d _, _) => decide (c = d)
      | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false) = true := by
    intro t ht
    have h := hmem t ht
    have hlive : (η.zeit.zustand t).status c = .laeuft :=
      (opened.2 t h.1).2.1
    rcases pf.vollzug valid h.2.1 hlive h.2.2 with hcrash | ⟨w, spur, chosen⟩
    · have herl : I.Erledigt η c t := Or.inr (Or.inl hcrash)
      exact ((opened.2 t h.1).2.2 herl).elim
    · simp only [chosen, decide_eq_true_eq]
  have hcount : E.stotterLaenge f < Kontextkosten ρ c a (U - a) := by
    have hkk : Kontextkosten ρ c a (U - a) =
        I.zaehle (fun t => match ρ.zeit.spur t with
          | some (.kontext d _, _) => decide (c = d)
          | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false) a (U - a) := rfl
    rw [hkk]
    have hlen' : L.length ≤ I.zaehle (fun t => match ρ.zeit.spur t with
        | some (.kontext d _, _) => decide (c = d)
        | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false) a (U - a) := by
      apply zaehle_ge_length _ _ _ _ hpair
      intro t ht
      have h := hmem t ht
      have hb := hbound t ht
      exact ⟨h.1, by omega, hstep t ht⟩
    omega
  obtain ⟨t, h1, _, herl⟩ := hwf c f a (opened.2 a (Nat.le_refl _)).1
    (opened.2 a (Nat.le_refl _)).2.1 (opened.1 a (Nat.le_refl _))
    (fun t h => (opened.2 t h).1) (fun t h => (opened.2 t h).2.1) enabled
    (U - a) hcount
  exact (opened.2 t h1).2.2 herl

/-- Counting lemma: an everywhere-true marker fills the window. -/
theorem zaehle_all_true (m : Nat → Bool) (a n : Nat) (hall : ∀ t, m (a + t) = true) :
    I.zaehle m a n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hif : (if m (a + n) then 1 else 0) = 1 := if_pos (hall n)
    simp only [I.zaehle, hif]
    rw [ih]

end Gabbro.Core.Fortschritt
