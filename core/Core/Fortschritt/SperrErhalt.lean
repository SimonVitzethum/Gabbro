/-
  File:      Core/Fortschritt/SperrErhalt.lean
  Subject:   LOCK-QUEUE PERSISTENCE FROM THE MACHINE RULES (PERFECT-MODEL §3.7, step M8, Teil 2b):
              what the machine already guarantees, and what it does not.

  Positive part (proved, generic, no checker involved):
  * a protocol step leaves every lock alone or moves exactly one lock by one lock rule
    (`kontextSchritt_sperren`, `antwortSchritt_sperren`, `interruptSchritt_sperren`), lifted to
    whole ticks (`lauf_schritt_sperren`); a crash wipes every lock (`absturz_leert_schlange`);
  * a queued waiter stays queued until it first owns the lock (`bleibt_bis_besitz`), its queue
    position does not grow until then (`mono_bis_besitz`, needs a duplicate-free queue, which
    the steps preserve: `nodup_bleibt`, `abgeben_nodup`), all on crash-free intervals.

  Negative part (proved): the UNSCOPED premises of `sperr_warte_schranke` are not run-generic —
  a handover with a later release refutes them (`bleibt_bricht_nach_abgabe`), and so does any
  crash (`bleibt_bricht_bei_absturz`). A release changes the lock (`gibt_wechselt`).
  Consequence for the design: the final bound must use the scoped versions proved here; the
  release itself (`hgibt`) is not among them — see `SperrGegenbeispiel` and `SperrFair`.
-/
module

public import Core.Fortschritt.Beweise.SperrHilfen

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Beobachtung

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- A restart wipes every lock: the queue is empty and nobody owns it. -/
theorem wiederanlauf_sperren_frei (s : Zustand L Ort Wert Raum Lok Grund)
    (w : Wiederanlauf Ort Wert Raum Lok Grund) (t : Nat) (p : PersistZustand) (l : L) :
    (Zustand.wiederanlauf s w t p).sperren l = SperrZustand.frei := rfl

/-- A crash step empties every lock queue and frees every owner. -/
theorem absturz_leert_schlange {s s' : Zustand L Ort Wert Raum Lok Grund}
    {spur : SchrittSpur Ort Wert} {l : L} {region w k run t}
    (h : AbsturzSchritt region w k run t s spur s') :
    (s'.sperren l).schlange = [] ∧ (s'.sperren l).besitzer = none := by
  obtain ⟨_, rfl⟩ := h.genau
  exact ⟨rfl, rfl⟩

/-- Inversion for takes: the head takes a free lock and leaves the tail. -/
theorem nimmt_inv {s s' : SperrZustand} {c : Kontext} (h : s.Nimmt c s') :
    ∃ r, s = ⟨none, c :: r⟩ ∧ s' = ⟨some c, r⟩ := by
  cases h with
  | frei c r => exact ⟨r, rfl, rfl⟩

/-- A duplicate-free queue stays duplicate-free over a hand-off. -/
theorem abgeben_nodup {o : Option Kontext} {q : List Kontext} (h : q.Nodup) :
    (SperrZustand.abgeben ⟨o, q⟩).schlange.Nodup := by
  cases q with
  | nil => exact List.nodup_nil
  | cons h₀ rest =>
    have hab : SperrZustand.abgeben ⟨o, h₀ :: rest⟩ = ⟨some h₀, rest⟩ := rfl
    rw [hab]
    exact (List.nodup_cons.mp h).2

/-- A release changes the lock state. -/
theorem gibt_wechselt {s s' : SperrZustand} {h : Kontext} (hg : s.Gibt h s') : s ≠ s' := by
  cases hg with
  | besitzer c r =>
    intro heq
    cases r with
    | nil =>
      have hbes := congrArg SperrZustand.besitzer heq
      nomatch hbes
    | cons h₀ rest =>
      have hq := congrArg SperrZustand.schlange heq
      have hlen : (h₀ :: rest).length = rest.length := congrArg List.length hq
      simp only [List.length_cons] at hlen
      omega

/-- Inversion for the lock part of a `sperre` protocol step. -/
theorem fuehrtAus_sperre_inv {t c s u mem ev v} {l a}
    (h : FuehrtAus E.einrichtung t c s u (.sperre l a) mem ev v) :
    ∃ next, SperrSchritt a c (s.sperren l) next ∧ v.sperren l = next ∧
      ∀ m, m ≠ l → v.sperren m = s.sperren m := by
  cases h with
  | sperre h' _ =>
    exact ⟨_, h', Function.update_self _ _ _,
      fun m hm => Function.update_of_ne hm _ _⟩

/-- A protocol step leaves every lock alone or moves exactly one lock by one lock rule. -/
theorem kontextSchritt_sperren {t c s u} {plan : SchrittPlan L Ort Wert Bedingung}
    {sperren_ev ev v} {m : L}
    (hrahmen : Zustandsrahmen s u)
    (haus : FuehrtAus E.einrichtung t c s u plan.aktion sperren_ev ev v) :
    v.sperren m = s.sperren m ∨
      ∃ a d next, SperrSchritt a d (s.sperren m) next ∧ v.sperren m = next := by
  match hplan : plan.aktion with
  | .intern =>
    rw [hplan] at haus
    cases haus
    exact Or.inl (congrFun hrahmen.sperren m)
  | .warte _ =>
    rw [hplan] at haus
    cases haus
    exact Or.inl (congrFun hrahmen.sperren m)
  | .sperre l a =>
    rw [hplan] at haus
    obtain ⟨next, hss, heq, hne⟩ := fuehrtAus_sperre_inv haus
    by_cases hm : m = l
    · subst hm
      exact Or.inr ⟨a, _, next, hss, heq⟩
    · exact Or.inl (hne m hm)
  | .frage _ =>
    rw [hplan] at haus
    cases haus
    exact Or.inl (congrFun hrahmen.sperren m)
  | .verbrauche _ =>
    rw [hplan] at haus
    cases haus
    exact Or.inl (congrFun hrahmen.sperren m)
  | .rueckkehr =>
    rw [hplan] at haus
    cases haus
    exact Or.inl (congrFun hrahmen.sperren m)
  | .starte | .verbinde _ | .beende | .wechsle _ _ =>
    rw [hplan] at haus
    cases haus
    exact Or.inl (congrFun hrahmen.sperren m)

/-- An answer arrival preserves every lock. -/
theorem antwortSchritt_sperren {s s' : Zustand L Ort Wert Raum Lok Grund}
    {spur : SchrittSpur Ort Wert} {a : AntwortEreignis} {m : L} {k run t}
    (h : AntwortSchritt E.einrichtung k run t a s spur s') :
    s'.sperren m = s.sperren m :=
  (congrArg (fun z : Zustand L Ort Wert Raum Lok Grund => z.sperren m) h.2.2.2).trans rfl

/-- An interrupt entry preserves every lock. -/
theorem interruptSchritt_sperren {s s' : Zustand L Ort Wert Raum Lok Grund}
    {spur : SchrittSpur Ort Wert} {id : Nat × Nat} {m : L} {run t}
    (h : UnterbrechungsSchritt E.einrichtung run t id s spur s') :
    s'.sperren m = s.sperren m := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq⟩ := h
  exact (congrArg (fun z : Zustand L Ort Wert Raum Lok Grund => z.sperren m) heq).trans rfl

/-- One tick leaves every lock alone or moves exactly one lock by one lock rule,
    unless the tick is a crash. -/
theorem lauf_schritt_sperren {ρ : Maschine.Lauf E} {l : L} {k : Nat}
    {sk s : Zustand L Ort Wert Raum Lok Grund}
    (hzk : ρ.zeit.zustand k = some sk) (hzk1 : ρ.zeit.zustand (k + 1) = some s)
    (hfrei : ρ.zeit.spur k ≠ some (.absturz, absturzSpur)) :
    s.sperren l = sk.sperren l ∨
      ∃ a d next, SperrSchritt a d (sk.sperren l) next ∧ s.sperren l = next := by
  cases htakt : ρ.zeit.takt k with
  | wartet _ heq _ =>
    have hss : s = sk := Option.some.inj (hzk1.symm.trans (heq.trans hzk))
    subst hss
    exact Or.inl rfl
  | schritt label step =>
    rw [hzk, hzk1] at step
    cases step with
    | schritt himp =>
      cases himp with
      | kontext _ _ _ aus =>
        obtain ⟨hrahmen, _, _, v, haus, _, heq⟩ := aus
        have hvv : s.sperren l =
            v.sperren l := (congrArg
            (fun z : Zustand L Ort Wert Raum Lok Grund => z.sperren l) heq).trans rfl
        rcases kontextSchritt_sperren hrahmen haus with huv | ⟨a', d', next, hss, hvn⟩
        · exact Or.inl (hvv.trans huv)
        · exact Or.inr ⟨a', d', next, hss, hvv.trans hvn⟩
      | antwort _ h =>
        exact Or.inl (antwortSchritt_sperren h)
      | interrupt _ h =>
        exact Or.inl (interruptSchritt_sperren h)
      | absturz h =>
        exact (hfrei (by rw [label, h.genau.1])).elim

/-- A queued waiter stays queued until it first owns the lock, on a crash-free interval. -/
theorem bleibt_bis_besitz {ρ : Maschine.Lauf E} {l : L} {c : Kontext} {a t : Nat}
    (hqueue : ∃ s, ρ.zeit.zustand a = some s ∧ c ∈ (s.sperren l).schlange)
    (hfrei : ∀ k, a ≤ k → k < t → ρ.zeit.spur k ≠ some (.absturz, absturzSpur))
    (hnie : ∀ k s', a ≤ k → k ≤ t → ρ.zeit.zustand k = some s' →
      (s'.sperren l).besitzer ≠ some c)
    {s : Zustand L Ort Wert Raum Lok Grund} (hat : a ≤ t)
    (hzt : ρ.zeit.zustand t = some s) :
    c ∈ (s.sperren l).schlange := by
  obtain ⟨s₀, hs₀, hmem₀⟩ := hqueue
  suffices key : ∀ d s, a + d ≤ t → ρ.zeit.zustand (a + d) = some s →
      c ∈ (s.sperren l).schlange by
    have hkk : a + (t - a) = t := by omega
    rw [← hkk] at hzt
    exact key (t - a) s (by omega) hzt
  intro d
  induction d with
  | zero =>
    intro s _ hzs
    rw [Nat.add_zero] at hzs
    have hss : s = s₀ := Option.some.inj (hzs.symm.trans hs₀)
    subst hss
    exact hmem₀
  | succ d ih =>
    intro s hle hzs
    cases hzk : ρ.zeit.zustand (a + d) with
    | none =>
      cases htakt : ρ.zeit.takt (a + d) with
      | schritt _ step =>
        rw [hzk] at step
        cases step
      | wartet _ heq _ =>
        have hkk : a + d + 1 = a + (d + 1) := by omega
        rw [hkk, hzs, hzk] at heq
        nomatch heq
    | some sk =>
      have hmem : c ∈ (sk.sperren l).schlange := ih sk (by omega) hzk
      have hown1 : (s.sperren l).besitzer ≠ some c :=
        hnie _ s (by omega) (by omega) hzs
      have hown0 : (sk.sperren l).besitzer ≠ some c :=
        hnie _ sk (by omega) (by omega) hzk
      have hzk1 : ρ.zeit.zustand (a + d + 1) = some s := by
        rw [show a + d + 1 = a + (d + 1) from by omega]
        exact hzs
      rcases lauf_schritt_sperren (l := l) hzk hzk1
          (hfrei _ (by omega) (by omega)) with heq | ⟨a', d', next, hss, hvn⟩
      · rw [heq]
        exact hmem
      · rw [hvn]
        cases hss with
        | ticket _ keinTicket =>
          have happ : ((sk.sperren l).anstellen d').schlange =
              (sk.sperren l).schlange ++ [d'] := rfl
          rw [happ]
          exact List.mem_append_left _ hmem
        | nehmen hn =>
          obtain ⟨r, hsq, hnx⟩ := nimmt_inv hn
          rw [hsq] at hmem
          have hmem' : c = d' ∨ c ∈ r := List.mem_cons.mp hmem
          rcases hmem' with hcd | hr
          · have hown' : (s.sperren l).besitzer = some c := by
              rw [hvn, hnx, hcd]
            exact (hown1 hown').elim
          · rw [hnx]
            exact hr
        | geben hg =>
          obtain ⟨q, hsq, hs2q⟩ := gibt_abgeben hg
          rw [hsq] at hmem
          have hgoal : c ∈ (SperrZustand.abgeben ⟨some d', q⟩).schlange := by
            cases q with
            | nil => exact (List.not_mem_nil hmem).elim
            | cons h₀ rest =>
              by_cases heq' : h₀ = c
              · have hred : (SperrZustand.abgeben ⟨some d', c :: rest⟩).besitzer
                  = some c := rfl
                have hown' : (s.sperren l).besitzer = some c := by
                  rw [hvn, hs2q, heq', hred]
                exact (hown1 hown').elim
              · have hmem' : c = h₀ ∨ c ∈ rest := List.mem_cons.mp hmem
                rcases hmem' with hcontra | hr
                · exact (heq' hcontra.symm).elim
                · exact hr
          rw [hs2q]
          exact hgoal

/-- A duplicate-free queue stays duplicate-free over crash-free steps. -/
theorem nodup_bleibt {ρ : Maschine.Lauf E} {l : L} {a t : Nat}
    (hod : ∀ s, ρ.zeit.zustand a = some s → (s.sperren l).schlange.Nodup)
    (hfrei : ∀ k, a ≤ k → k < t → ρ.zeit.spur k ≠ some (.absturz, absturzSpur))
    {k : Nat} {s : Zustand L Ort Wert Raum Lok Grund}
    (hle : a ≤ k) (hkt : k ≤ t) (hzk : ρ.zeit.zustand k = some s) :
    (s.sperren l).schlange.Nodup := by
  suffices key : ∀ d s, a + d ≤ t → ρ.zeit.zustand (a + d) = some s →
      (s.sperren l).schlange.Nodup by
    have hkk : a + (k - a) = k := by omega
    have hle' : a + (k - a) ≤ t := by omega
    rw [← hkk] at hzk
    exact key (k - a) s hle' hzk
  intro d
  induction d with
  | zero =>
    intro s _ hzs
    rw [Nat.add_zero] at hzs
    exact hod _ hzs
  | succ d ih =>
    intro s hle hzs
    cases hzk : ρ.zeit.zustand (a + d) with
    | none =>
      cases htakt : ρ.zeit.takt (a + d) with
      | schritt _ step =>
        rw [hzk] at step
        cases step
      | wartet _ heq _ =>
        have hkk : a + d + 1 = a + (d + 1) := by omega
        rw [hkk, hzs, hzk] at heq
        nomatch heq
    | some sk =>
      have hnd : (sk.sperren l).schlange.Nodup := ih sk (by omega) hzk
      have hzk1 : ρ.zeit.zustand (a + d + 1) = some s := by
        rw [show a + d + 1 = a + (d + 1) from by omega]
        exact hzs
      rcases lauf_schritt_sperren (l := l) hzk hzk1
          (hfrei _ (by omega) (by omega)) with heq | ⟨a', d', next, hss, hvn⟩
      · rw [heq]
        exact hnd
      · cases hss with
        | ticket _ keinTicket =>
          have happ : ((sk.sperren l).anstellen d').schlange =
              (sk.sperren l).schlange ++ [d'] := rfl
          rw [hvn, happ]
          refine List.nodup_append.mpr ⟨hnd,
            List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
          intro x hx b hb
          rw [List.mem_singleton] at hb
          subst hb
          exact fun he => (keinTicket (he ▸ hx)).elim
        | nehmen hn =>
          obtain ⟨r, hsq, hnx⟩ := nimmt_inv hn
          rw [hsq] at hnd
          have hcdr : (d' :: r).Nodup := hnd
          rw [hvn, hnx]
          exact (List.nodup_cons.mp hcdr).2
        | geben hg =>
          obtain ⟨q, hsq, hs2q⟩ := gibt_abgeben hg
          rw [hsq] at hnd
          cases q with
          | nil =>
            rw [hvn, hs2q]
            exact List.nodup_nil
          | cons h₀ rest =>
            have hab : SperrZustand.abgeben ⟨some d', h₀ :: rest⟩ =
                ⟨some h₀, rest⟩ := rfl
            have hcdr : (h₀ :: rest).Nodup := hnd
            rw [hvn, hs2q, hab]
            exact (List.nodup_cons.mp hcdr).2

/-- One queue step does not grow the position of a waiter that does not take over. -/
theorem schritt_index_mono {c : Kontext} {q q' : List Kontext} {i₁ i₂ : Nat}
    (hnd : q.Nodup) (hq1 : q[i₁]? = some c) (hq2 : q'[i₂]? = some c)
    (hstep : q' = q ∨ ∃ a d o next, SperrSchritt a d ⟨o, q⟩ next ∧
      q' = next.schlange ∧ next.besitzer ≠ some c) :
    i₂ ≤ i₁ := by
  rcases hstep with hqq | ⟨a, d, o, next, hss, hqq, hown⟩
  · rw [hqq] at hq2
    have hei : i₁ = i₂ := List.Nodup.eq_of_getElem?_eq hnd
      (List.getElem?_eq_some_iff.mp hq1).1 (hq1.trans hq2.symm)
    omega
  · rw [hqq] at hq2
    cases hss with
    | ticket _ keinTicket =>
      have happ : ((⟨o, q⟩ : SperrZustand).anstellen d).schlange = q ++ [d] := rfl
      rw [happ] at hq2
      by_cases hlt : i₂ < q.length
      · rw [List.getElem?_append_left hlt] at hq2
        have hei : i₁ = i₂ := List.Nodup.eq_of_getElem?_eq hnd
          (List.getElem?_eq_some_iff.mp hq1).1 (hq1.trans hq2.symm)
        omega
      · have hlen : (q ++ [d]).length = q.length + 1 := by
          rw [List.length_append, List.length_cons, List.length_nil]
        have hi₂ : i₂ < (q ++ [d]).length :=
          (List.getElem?_eq_some_iff.mp hq2).1
        have heq2 : i₂ = q.length := by omega
        subst heq2
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons, if_pos rfl] at hq2
        have hdc : d = c := Option.some.inj hq2
        have hmem : c ∈ q := List.mem_of_getElem? hq1
        rw [← hdc] at hmem
        exact (keinTicket hmem).elim
    | nehmen hn =>
      obtain ⟨r, hsq, hnx⟩ := nimmt_inv hn
      have hqq' : q = d :: r := congrArg SperrZustand.schlange hsq
      rw [hqq'] at hq1 hnd
      have hqr' : next.schlange = r := by rw [hnx]
      rw [hqr'] at hq2
      have hown' : (⟨some d, r⟩ : SperrZustand).besitzer ≠ some c := by
        rw [← hnx]
        exact hown
      cases i₁ with
      | zero =>
        have hdc : d = c := Option.some.inj hq1
        have hown'' : (⟨some d, r⟩ : SperrZustand).besitzer = some c := by
          rw [hdc]
        exact (hown' hown'').elim
      | succ j =>
        have hjr : r[j]? = some c := hq1
        have hr : r.Nodup := (List.nodup_cons.mp hnd).2
        have hej : j = i₂ := List.Nodup.eq_of_getElem?_eq hr
          (List.getElem?_eq_some_iff.mp hjr).1 (hjr.trans hq2.symm)
        omega
    | geben hg =>
      obtain ⟨qq, hsq, hs2q⟩ := gibt_abgeben hg
      have hqq' : q = qq := congrArg SperrZustand.schlange hsq
      rw [hqq'] at hq1 hnd
      cases qq with
      | nil =>
        have hmem : c ∈ ([] : List Kontext) :=
          List.mem_of_getElem? (show ([] : List Kontext)[i₁]? = some c from hq1)
        exact (List.not_mem_nil hmem).elim
      | cons h₀ rest =>
        have hab : SperrZustand.abgeben ⟨some d, h₀ :: rest⟩ = ⟨some h₀, rest⟩ := rfl
        have hqr' : next.schlange = rest := by rw [hs2q, hab]
        rw [hqr'] at hq2
        have hq1' : (h₀ :: rest)[i₁]? = some c := hq1
        have hown' : (⟨some h₀, rest⟩ : SperrZustand).besitzer ≠ some c := by
          rw [← hab, ← hs2q]
          exact hown
        cases i₁ with
        | zero =>
          have h0c : h₀ = c := Option.some.inj hq1'
          have hown'' : (⟨some h₀, rest⟩ : SperrZustand).besitzer = some c := by
            rw [h0c]
          exact (hown' hown'').elim
        | succ j =>
          have hjr : rest[j]? = some c := hq1'
          have hr : rest.Nodup := (List.nodup_cons.mp hnd).2
          have hej : j = i₂ := List.Nodup.eq_of_getElem?_eq hr
            (List.getElem?_eq_some_iff.mp hjr).1 (hjr.trans hq2.symm)
          omega

/-- Queue positions do not grow until the waiter first owns the lock. -/
theorem mono_bis_besitz {ρ : Maschine.Lauf E} {l : L} {c : Kontext} {a t t₁ t₂ i₁ i₂ : Nat}
    (hqueue : ∃ s, ρ.zeit.zustand a = some s ∧ c ∈ (s.sperren l).schlange)
    (hod : ∀ s, ρ.zeit.zustand a = some s → (s.sperren l).schlange.Nodup)
    (hfrei : ∀ k, a ≤ k → k < t → ρ.zeit.spur k ≠ some (.absturz, absturzSpur))
    (hnie : ∀ k s', a ≤ k → k ≤ t → ρ.zeit.zustand k = some s' →
      (s'.sperren l).besitzer ≠ some c)
    (hle : a ≤ t₁) (hlt : t₁ ≤ t₂) (htt : t₂ ≤ t)
    {s₁ s₂ : Zustand L Ort Wert Raum Lok Grund}
    (hz1 : ρ.zeit.zustand t₁ = some s₁) (hz2 : ρ.zeit.zustand t₂ = some s₂)
    (hq1 : (s₁.sperren l).schlange[i₁]? = some c)
    (hq2 : (s₂.sperren l).schlange[i₂]? = some c) :
    i₂ ≤ i₁ := by
  suffices key : ∀ d i', t₁ + d ≤ t₂ → ∀ s', ρ.zeit.zustand (t₁ + d) = some s' →
      (s'.sperren l).schlange[i']? = some c → i' ≤ i₁ by
    have hkk : t₁ + (t₂ - t₁) = t₂ := by omega
    rw [← hkk] at hz2
    exact key (t₂ - t₁) i₂ (by omega) s₂ hz2 hq2
  intro d
  induction d with
  | zero =>
    intro i' _ s' hzs hq'
    rw [Nat.add_zero] at hzs
    have hss : s' = s₁ := Option.some.inj (hzs.symm.trans hz1)
    rw [hss] at hq'
    have hnd : (s₁.sperren l).schlange.Nodup :=
      nodup_bleibt hod hfrei hle (by omega) hz1
    have hei : i' = i₁ := List.Nodup.eq_of_getElem?_eq hnd
      (List.getElem?_eq_some_iff.mp hq').1 (hq'.trans hq1.symm)
    omega
  | succ d ih =>
    intro i'' hle' s' hzs hq''
    cases hzk : ρ.zeit.zustand (t₁ + d) with
    | none =>
      cases htakt : ρ.zeit.takt (t₁ + d) with
      | schritt _ step =>
        rw [hzk] at step
        cases step
      | wartet _ heq _ =>
        have hkk : t₁ + d + 1 = t₁ + (d + 1) := by omega
        rw [hkk, hzs, hzk] at heq
        nomatch heq
    | some sk =>
      have hmem' : c ∈ (sk.sperren l).schlange :=
        bleibt_bis_besitz hqueue
          (fun k h1 h2 => hfrei k (by omega) (by omega))
          (fun k s'' h1 h2 h3 => hnie k s'' (by omega) (by omega) h3)
          (by omega) hzk
      obtain ⟨i', hi'⟩ := mem_getElem? hmem'
      have hnd : (sk.sperren l).schlange.Nodup :=
        nodup_bleibt hod hfrei (by omega) (by omega) hzk
      have hle1 : i' ≤ i₁ := ih i' (by omega) sk hzk hi'
      have hown1 : (s'.sperren l).besitzer ≠ some c :=
        hnie _ s' (by omega) (by omega) hzs
      have hzk1 : ρ.zeit.zustand (t₁ + d + 1) = some s' := by
        rw [show t₁ + d + 1 = t₁ + (d + 1) from by omega]
        exact hzs
      rcases lauf_schritt_sperren (l := l) hzk hzk1
          (hfrei _ (by omega) (by omega)) with heq | ⟨a', d', next, hss, hvn⟩
      · rw [heq] at hq''
        have hei : i' = i'' := List.Nodup.eq_of_getElem?_eq hnd
          (List.getElem?_eq_some_iff.mp hi').1 (hi'.trans hq''.symm)
        omega
      · have hown' : next.besitzer ≠ some c := by
          rw [← hvn]
          exact hown1
        have hstate : (⟨(sk.sperren l).besitzer,
            (sk.sperren l).schlange⟩ : SperrZustand) = sk.sperren l := rfl
        have hss' : SperrSchritt a' d' ⟨(sk.sperren l).besitzer,
            (sk.sperren l).schlange⟩ next := by
          rw [hstate]
          exact hss
        have hq2' : next.schlange[i'']? = some c := by
          rw [← hvn]
          exact hq''
        have hle2 := schritt_index_mono (q := (sk.sperren l).schlange) hnd hi' hq2'
          (Or.inr ⟨a', d', _, next, hss', rfl, hown'⟩)
        omega

end Gabbro.Core.Fortschritt
