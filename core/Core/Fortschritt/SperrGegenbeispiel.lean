/-
  File:      Core/Fortschritt/SperrGegenbeispiel.lean
  Subject:   HOLD BOUNDS DO NOT IMPLY RELEASE (PERFECT-MODEL §3.7, step M8, Teil 2b): the
              counterexample the design brief asks for.

  `E_h` is `E_1` with one lock held by a stuck holder `H` that never steps and never releases.
  On the fair two-core schedule `hw2`, two other contexts stutter forever; the lock never moves.
  The run is admissible (`lauf_h`) on a fair history (`fair2`), satisfies `HalteSchranken`
  (`eh_halte`: the holder takes no own steps, nobody else ever owns), declares hold bound five
  (`eh_halten`) — and no release step ever occurs. Hence no `hgibt`-shaped conclusion follows
  from `HalteSchranken` plus hardware fairness alone (`halte_gibt_nicht_ab`).

  The checker-side release obligation for lock holders (B13 remainder) now lives in
  `WaechterHalten` as `SperrHalterHalten`: an accepted unit keeps a holder live, dispatched
  and geben-offering until it hands the lock off. It is discharged as `SperrFreigabeAussage`
  in `SperrFair`. This counterexample stays as the negative leg: bounds plus fairness alone
  do not imply release.
-/
module

public import Core.Fortschritt.SperrErhalt
public import Core.Fortschritt.WarteBeispiel
public import Core.Annahme.Annahme

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

/-- The stuck holder: never dispatched, never steps, never releases. -/
def stuckHalter : Kontext := .faden 2

/-- The held start state: `E_1`'s start with the lock owned by the stuck holder. -/
def sH0 : Zustand Unit Unit Unit Unit Bool Unit :=
  { zE0 with sperren := fun _ => ⟨some stuckHalter, []⟩ }

/-- The stuck-holder unit: `E_1` with the held start loaded. -/
def E_h : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  { E_1 with laden := fun _ _ => some sH0 }

theorem eh_halten : E_h.schranken.halten () = some 5 := rfl

theorem wBild_format : wBild.format = .elf := rfl

theorem wBild_bytes : wBild.bytes = fun a => if a = 0 then some 0 else none := rfl

theorem wBild_entries : wBild.entries = [0] := rfl

/-- `wBild` is a valid image for the x86-64 platform. -/
theorem wBild_gueltig : wBild.gueltig E_1.katalog.plattform.ziel := by
  have hplat : E_1.katalog.plattform = Plattform.x86_64 := rfl
  rw [hplat]
  refine ⟨(ziele_gut _).2.2.2.2.2.2.2.2.2, ?_, ?_⟩
  · intro a v h
    rw [wBild_bytes] at h
    have h' : (if a = 0 then some (0 : UInt8) else none) = some v := h
    by_cases ha : a = 0
    · subst ha
      exact pow_pos (by decide : (0 : Nat) < 2) _
    · rw [if_neg ha] at h'
      nomatch h'
  · intro entry hmem
    rw [wBild_entries, List.mem_singleton] at hmem
    subst hmem
    exact ⟨0, rfl⟩

noncomputable def s_h : AussenStart :=
  Classical.choose (zulStart_erfuellbar fair2.hardware wBild_gueltig)

def zul_h : Katalog.ZulStart Plattform.x86_64.katalog h2 wBild s_h :=
  Classical.choose_spec (zulStart_erfuellbar fair2.hardware wBild_gueltig)

def spur_h (t : Nat) : Option (SchrittWahl Unit × SchrittSpur Unit Unit) :=
  if t % 2 = 0 then some posLabel else some bLabel

theorem sH0_dispatch0 : (sH0.kerne 0).laeuft = some A := rfl

theorem sH0_dispatch1 : (sH0.kerne 1).laeuft = some B := rfl

theorem sH0_live : ∀ c, sH0.status c = .laeuft := fun _ => rfl

def takt_h (t : Nat) : Takt (Lauffolge E_h hw2) (KeinSchritt (Lauffolge E_h hw2))
    t (some sH0) (spur_h t) (some sH0) := by
  by_cases h : t % 2 = 0
  · have hsp : spur_h t = some posLabel := by simp only [spur_h, if_pos h]
    rw [hsp]
    exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash t)
      ⟨0, hw2_opp0 h, sH0_dispatch0, sH0_live _⟩
      ⟨(), rfl, Or.inr ⟨rfl, rfl⟩⟩
      (e1StotterAusfuehr t A sH0)))
  · have h1 : t % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
      · exact (h h0).elim
      · exact h1
    have hsp : spur_h t = some bLabel := by simp only [spur_h, if_neg h]
    rw [hsp]
    exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash t)
      ⟨1, hw2_opp1 h1, sH0_dispatch1, sH0_live _⟩
      ⟨(), rfl, Or.inr ⟨rfl, rfl⟩⟩
      (e1StotterAusfuehr t B sH0)))

noncomputable def ρ_h : Maschine.Lauf E_h :=
  ⟨s_h, hw2, ⟨fun _ => some sH0, spur_h, takt_h⟩⟩

/-- Only the two stutterers are ever dispatched: core zero runs `A`, core one
    runs `B`, every higher core idles. -/
theorem sH0_dispatchN (m : Nat) : (sH0.kerne (Nat.succ (Nat.succ m))).laeuft = none := rfl

/-- The alternating run is scheduler-fair: a context ready on a whole suffix is
    dispatched, hence `A` or `B`, and each of them steps on every other tick. -/
theorem fairH : SchedulerFair E_h ρ_h := by
  intro a c ready _opp n _hn
  obtain ⟨s, hs, dispJ, _, _, _, _, _, _, _, _, _⟩ := ready (max n a) (Nat.le_max_right _ _)
  have hseq : s = sH0 := (Option.some.inj hs).symm
  obtain ⟨j, hj⟩ := dispJ
  rw [hseq] at hj
  cases j with
  | zero =>
    have hcA : c = A := (Option.some.inj (sH0_dispatch0.symm.trans hj)).symm
    subst hcA
    match hm : (max n a) % 2 with
    | 0 =>
      have hsp : spur_h (max n a) = some posLabel := by simp only [spur_h, if_pos hm]
      exact ⟨max n a, Nat.le_max_left _ _, (), ⟨[], []⟩, hsp⟩
    | m + 1 =>
      have heven : (max n a + 1) % 2 = 0 := by omega
      have hsp : spur_h (max n a + 1) = some posLabel := by simp only [spur_h, if_pos heven]
      exact ⟨max n a + 1, Nat.le_succ_of_le (Nat.le_max_left _ _), (), ⟨[], []⟩, hsp⟩
  | succ j =>
    cases j with
    | zero =>
      have hcB : c = B := (Option.some.inj (sH0_dispatch1.symm.trans hj)).symm
      subst hcB
      match hm : (max n a) % 2 with
      | 0 =>
        have hodd : (max n a + 1) % 2 = 1 := by omega
        have hn : ¬ (max n a + 1) % 2 = 0 := by omega
        have hsp : spur_h (max n a + 1) = some bLabel := by simp only [spur_h, if_neg hn]
        exact ⟨max n a + 1, Nat.le_succ_of_le (Nat.le_max_left _ _), (), ⟨[], []⟩, hsp⟩
      | m + 1 =>
        have h1 : (max n a) % 2 = 1 := by omega
        have hn : ¬ (max n a) % 2 = 0 := by omega
        have hsp : spur_h (max n a) = some bLabel := by simp only [spur_h, if_neg hn]
        exact ⟨max n a, Nat.le_max_left _ _, (), ⟨[], []⟩, hsp⟩
    | succ m =>
      rw [sH0_dispatchN m] at hj
      cases hj

/-- The stuck run is admissible. -/
theorem lauf_h : Laeufe E_h h2 ρ_h :=
  ⟨fair2.hardware, fair2.konform, zul_h, rfl, fairH⟩

/-- The lock stays with the stuck holder at every cut. -/
theorem eh_besitzer (t : Nat) (s : Zustand Unit Unit Unit Unit Bool Unit) (l : Unit)
    (hzs : ρ_h.zeit.zustand t = some s) : (s.sperren l).besitzer = some stuckHalter := by
  have hss : s = sH0 := Option.some.inj (hzs.symm.trans rfl)
  subst hss
  cases l
  rfl

/-- The lock state never changes. -/
theorem eh_lock (t : Nat) (s : Zustand Unit Unit Unit Unit Bool Unit) (l : Unit)
    (hzs : ρ_h.zeit.zustand t = some s) :
    s.sperren l = ⟨some stuckHalter, []⟩ := by
  have hss : s = sH0 := Option.some.inj (hzs.symm.trans rfl)
  subst hss
  cases l
  rfl

/-- An everywhere-false marker fills no window. -/
theorem zaehle_null (m : Nat → Bool) (a n : Nat) (hall : ∀ t, m (a + t) = false) :
    I.zaehle m a n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hrec : I.zaehle m a (n + 1) =
        I.zaehle m a n + (if m (a + n) then 1 else 0) := rfl
    have hif : (if m (a + n) then (1 : Nat) else 0) = 0 := by
      rw [hall n]
      exact if_neg (by decide)
    rw [hrec, hif]
    omega

/-- The stuck holder takes no own steps. -/
theorem eh_kosten_null (a n : Nat) : Kontextkosten ρ_h stuckHalter a n = 0 := by
  unfold Kontextkosten
  apply zaehle_null
  intro t
  have hsp : ρ_h.zeit.spur (a + t) = some posLabel ∨
      ρ_h.zeit.spur (a + t) = some bLabel := by
    by_cases h : (a + t) % 2 = 0
    · left
      show spur_h (a + t) = some posLabel
      simp only [spur_h, if_pos h]
    · right
      show spur_h (a + t) = some bLabel
      simp only [spur_h, if_neg h]
  rcases hsp with hsp | hsp
  · rw [hsp]
    rfl
  · rw [hsp]
    rfl

/-- The stuck run meets every hold bound. -/
theorem eh_halte : HalteSchranken E_h ρ_h := by
  intro l c a n hcont H' hH
  have h5 : E_h.schranken.halten l = some 5 := by cases l; rfl
  have hH5 : H' = 5 := Option.some.inj (hH.symm.trans h5)
  subst hH5
  by_cases hcH : c = stuckHalter
  · subst hcH
    have hcost := eh_kosten_null a n
    omega
  · by_cases hn0 : n = 0
    · subst hn0
      have hcost : Kontextkosten ρ_h c a 0 = 0 := rfl
      omega
    · have hlt : a < a + n := by omega
      obtain ⟨s, hzs, hown⟩ := hcont a (Nat.le_refl _) hlt
      have hownH := eh_besitzer a s l hzs
      rw [hownH] at hown
      exact absurd (Option.some.inj hown) (Ne.symm hcH)

/-- No release step ever occurs on the stuck run. -/
theorem eh_kein_gibt (r : Nat) (s₁ s₂ : Zustand Unit Unit Unit Unit Bool Unit)
    (hr1 : ρ_h.zeit.zustand r = some s₁) (hr2 : ρ_h.zeit.zustand (r + 1) = some s₂)
    (h : Kontext) : ¬ (s₁.sperren ()).Gibt h (s₂.sperren ()) := by
  intro hg
  have e1 := eh_lock r s₁ () hr1
  have e2 := eh_lock (r + 1) s₂ () hr2
  have hne := gibt_wechselt hg
  exact hne (by rw [e1, e2])

/-- Hold bounds plus hardware fairness do not imply release: the stuck holder keeps its lock
    forever on an admissible fair run, so no `hgibt`-shaped conclusion follows. -/
theorem halte_gibt_nicht_ab :
    ∃ (E : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit) (h : Umgebung)
      (ρ : Maschine.Lauf E) (l : Unit) (hh : Kontext) (H : Nat) (b : Nat)
      (s : Zustand Unit Unit Unit Unit Bool Unit),
      Laeufe E h ρ ∧ FairLaeufe E.katalog h ρ.hw ∧ HalteSchranken E ρ ∧
      E.schranken.halten l = some H ∧ ρ.zeit.zustand b = some s ∧
      (s.sperren l).besitzer = some hh ∧
      ¬ ∃ r, b ≤ r ∧ (∃ s₁ s₂, ρ.zeit.zustand r = some s₁ ∧
        ρ.zeit.zustand (r + 1) = some s₂ ∧
        (s₁.sperren l).Gibt hh (s₂.sperren l)) ∧
        Kontextkosten ρ hh b (r + 1 - b) ≤ H + 1 := by
  refine ⟨E_h, h2, ρ_h, (), stuckHalter, 5, 0, sH0, lauf_h, fair2, eh_halte,
    eh_halten, rfl, rfl, ?_⟩
  rintro ⟨r, _, ⟨s₁, s₂, hr1, hr2, hg⟩, _⟩
  exact eh_kein_gibt r s₁ s₂ hr1 hr2 _ hg

/-- The waiting twin's dispatch: the holder on core zero, a stutterer on core one. -/
def dispatchW : Kern → Option Kontext
  | 0 => some stuckHalter
  | 1 => some A
  | _ + 2 => none

/-- The waiting start state: the holder owns the lock, both contexts live. -/
def sW0 : Zustand Unit Unit Unit Unit Bool Unit :=
  let base : Zustand Unit Unit Unit Unit Bool Unit :=
    Zustand.start (fun _ => false) (fun _ => .laeuft)
      (fun j => ⟨dispatchW j, .nutzer, (), fun _ => false, 0, false, []⟩)
      ⟨fun _ => false, fun _ => 0⟩ (fun _ => ()) (.leer (fun _ => 0))
  { base with sperren := fun _ => (⟨some stuckHalter, []⟩ : SperrZustand) }

theorem sW0_kerne0 : (sW0.kerne 0).laeuft = some stuckHalter := rfl

theorem sW0_kerne1 : (sW0.kerne 1).laeuft = some A := rfl

theorem sW0_live : ∀ c, sW0.status c = .laeuft := fun _ => rfl

/-- The release plan at the lock, for the ideal rule. -/
def wGebenPlan : SchrittPlan Unit Unit Unit Unit :=
  ⟨.sperre () .geben, [], [], fun _ => false, fun _ => .na, fun _ => ()⟩

/-- The implementation rule: silent for the holder, stutter for the waiter. -/
def wImpl (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) (w : Unit)
    (es : List (SchrittPlan Unit Unit Unit Unit))
    (u : Zustand Unit Unit Unit Unit Bool Unit) : Prop :=
  c = A ∧ es = [stutterPlan] ∧ u = s

/-- The ideal rule: the holder offers the release, everyone may stutter. -/
def wIdeal (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) (w : Unit)
    (es : List (SchrittPlan Unit Unit Unit Unit))
    (u : Zustand Unit Unit Unit Unit Bool Unit) : Prop :=
  (∃ next, (s.sperren ()).Gibt c next ∧ es = [wGebenPlan] ∧ u = s) ∨
  (es = [stutterPlan] ∧ u = s)

/-- The waiting report: the holder waits on a never-enabled condition. -/
def wBlockiert : Zustand Unit Unit Unit Unit Bool Unit → Kontext → Blockade Unit Unit →
    Prop :=
  fun _ c b => c = stuckHalter ∧ b = .warten ()

/-- The waiting system: divergent rules, honest head, the waiting report. -/
def wSystem : MaschinenSystem Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  ⟨fun _ => ⟨wImpl, wIdeal⟩, fun _ _ => some (), fun _ _ => False, wBlockiert⟩

/-- The waiting twin: `E_1` with the waiting system and the waiting start loaded. -/
def E_wait : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  { E_1 with system := wSystem, laden := fun _ _ => some sW0 }

theorem ew_halten : E_wait.schranken.halten () = some 5 := rfl

/-- The waiting trace: the waiter stutters on odd ticks, the holder's ticks pause. -/
def spur_w (t : Nat) : Option (SchrittWahl Unit × SchrittSpur Unit Unit) :=
  if t % 2 = 0 then none else some posLabel

theorem spur_w_even {t : Nat} (h : t % 2 = 0) : spur_w t = none := by
  simp only [spur_w, if_pos h]

theorem spur_w_odd {t : Nat} (h : t % 2 = 1) : spur_w t = some posLabel := by
  have hn : ¬ t % 2 = 0 := fun h0 => (by decide : (0 : Nat) ≠ 1) (h0.symm.trans h)
  simp only [spur_w, if_neg hn]

/-- The hardware never raises an interrupt. -/
theorem hw2_interrupts_leer (t id : Nat) : (hw2.angebot t).interrupts[id]? = none := by
  have hempty : (hw2.angebot t).interrupts = [] := rfl
  rw [hempty]
  exact List.getElem?_nil

/-- On the holder's ticks no transition exists: the holder's rule is silent, the waiter
    has no opportunity, no question is pending, no interrupt is raised, no crash is
    offered. -/
theorem keinSchritt_w {t : Nat} (h : t % 2 = 0) :
    KeinSchritt (Lauffolge E_wait hw2) t (some sW0) := by
  intro _ _ hstep
  cases hstep with
  | schritt himp =>
    cases himp with
    | kontext _ hbereit hregel _ =>
      obtain ⟨k, hopp, hdisp, _hlive⟩ := hbereit
      obtain ⟨i, _, himpl⟩ := hregel
      cases i
      cases k with
      | zero =>
        have hd : (sW0.kerne 0).laeuft = some stuckHalter := rfl
        rw [hd] at hdisp
        obtain rfl := Option.some.inj hdisp
        have hHA : stuckHalter = A := himpl.1
        have h20 : (2 : Nat) = 0 := Kontext.faden.inj hHA
        exact absurd h20 (Nat.succ_ne_zero 1)
      | succ k =>
        cases k with
        | zero =>
          have hd : (sW0.kerne 1).laeuft = some A := rfl
          rw [hd] at hdisp
          have h1 : t % 2 = 1 := Option.some.inj hopp
          exact (by decide : (0 : Nat) ≠ 1) (h.symm.trans h1)
        | succ n =>
          have hd : (sW0.kerne (Nat.succ (Nat.succ n))).laeuft = none := rfl
          rw [hd] at hdisp
          simp only [reduceCtorEq] at hdisp
    | antwort _ h =>
      have hq := h.1.2.2.2.1
      obtain ⟨q, hmem, _⟩ := hq
      rw [show sW0.fragen = [] from rfl] at hmem
      exact List.not_mem_nil hmem
    | interrupt _ h =>
      obtain ⟨_, _, _, _, _, haus, _⟩ := h
      have hinter := haus.2.2.1
      rw [hw2_interrupts_leer] at hinter
      simp only [List.getElem?_nil, reduceCtorEq] at hinter
    | absturz h =>
      have hc := h.1.2
      rw [hw2_crash t] at hc
      exact Bool.false_ne_true hc

def takt_w (t : Nat) : Takt (Lauffolge E_wait hw2) (KeinSchritt (Lauffolge E_wait hw2))
    t (some sW0) (spur_w t) (some sW0) := by
  by_cases h : t % 2 = 0
  · rw [spur_w_even h]
    exact .wartet rfl rfl (keinSchritt_w h)
  · have h1 : t % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
      · exact (h h0).elim
      · exact h1
    rw [spur_w_odd h1]
    exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash t)
      ⟨1, hw2_opp1 h1, sW0_kerne1, sW0_live _⟩
      ⟨(), rfl, ⟨rfl, rfl, rfl⟩⟩
      (e1StotterAusfuehr t A sW0)))

noncomputable def s_w : AussenStart :=
  Classical.choose (zulStart_erfuellbar fair2.hardware wBild_gueltig)

def zul_w : Katalog.ZulStart Plattform.x86_64.katalog h2 wBild s_w :=
  Classical.choose_spec (zulStart_erfuellbar fair2.hardware wBild_gueltig)

noncomputable def ρ_w : Maschine.Lauf E_wait :=
  ⟨s_w, hw2, ⟨fun _ => some sW0, spur_w, takt_w⟩⟩

/-- The waiting run is scheduler-fair: only the waiter has an implementation
    step, so every suffix-ready context is `A`, served on every odd tick. -/
theorem fairW : SchedulerFair E_wait ρ_w := by
  intro a c ready _opp n _hn
  obtain ⟨_, _, _, _, _, _, _, _, _, _, regel, _⟩ := ready (max n a) (Nat.le_max_right _ _)
  obtain ⟨i, _, himpl⟩ := regel
  have hcA : c = A := himpl.1
  subst hcA
  match hm : (max n a) % 2 with
  | 0 =>
    have h1 : (max n a + 1) % 2 = 1 := by omega
    exact ⟨max n a + 1, Nat.le_succ_of_le (Nat.le_max_left _ _), (),
      ⟨[], []⟩, spur_w_odd h1⟩
  | m + 1 =>
    have h1 : (max n a) % 2 = 1 := by omega
    exact ⟨max n a, Nat.le_max_left _ _, (), ⟨[], []⟩, spur_w_odd h1⟩

theorem lauf_w : Laeufe E_wait h2 ρ_w :=
  ⟨fair2.hardware, fair2.konform, zul_w, rfl, fairW⟩

/-- The lock stays with the waiting holder at every cut. -/
theorem ew_besitzer (t : Nat) (s : Zustand Unit Unit Unit Unit Bool Unit)
    (hzs : ρ_w.zeit.zustand t = some s) : (s.sperren ()).besitzer = some stuckHalter := by
  have hss : s = sW0 := Option.some.inj (hzs.symm.trans rfl)
  subst hss
  rfl

/-- The lock state never changes. -/
theorem ew_lock (t : Nat) (s : Zustand Unit Unit Unit Unit Bool Unit)
    (hzs : ρ_w.zeit.zustand t = some s) :
    s.sperren () = ⟨some stuckHalter, []⟩ := by
  have hss : s = sW0 := Option.some.inj (hzs.symm.trans rfl)
  subst hss
  rfl

/-- The waiting holder takes no own steps. -/
theorem ew_kosten_null (a n : Nat) : Kontextkosten ρ_w stuckHalter a n = 0 := by
  unfold Kontextkosten
  apply zaehle_null
  intro t
  by_cases h : (a + t) % 2 = 0
  · have hsp : ρ_w.zeit.spur (a + t) = none := spur_w_even h
    rw [hsp]
  · have h1 : (a + t) % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (a + t) with h0 | h1
      · exact (h h0).elim
      · exact h1
    have hsp : ρ_w.zeit.spur (a + t) = some posLabel := spur_w_odd h1
    rw [hsp]
    rfl

/-- The waiting run meets every hold bound. -/
theorem ew_halte : HalteSchranken E_wait ρ_w := by
  intro l c a n hcont H' hH
  have h5 : E_wait.schranken.halten l = some 5 := by cases l; rfl
  have hH5 : H' = 5 := Option.some.inj (hH.symm.trans h5)
  subst hH5
  by_cases hcH : c = stuckHalter
  · subst hcH
    have hcost := ew_kosten_null a n
    omega
  · by_cases hn0 : n = 0
    · subst hn0
      have hcost : Kontextkosten ρ_w c a 0 = 0 := rfl
      omega
    · have hlt : a < a + n := by omega
      obtain ⟨s, hzs, hown⟩ := hcont a (Nat.le_refl _) hlt
      have hownH := ew_besitzer a s hzs
      rw [hownH] at hown
      exact absurd (Option.some.inj hown) (Ne.symm hcH)

/-- No release step ever occurs on the waiting run. -/
theorem ew_kein_gibt (r : Nat) (s₁ s₂ : Zustand Unit Unit Unit Unit Bool Unit)
    (hr1 : ρ_w.zeit.zustand r = some s₁) (hr2 : ρ_w.zeit.zustand (r + 1) = some s₂)
    (h : Kontext) : ¬ (s₁.sperren ()).Gibt h (s₂.sperren ()) := by
  intro hg
  have e1 := ew_lock r s₁ hr1
  have e2 := ew_lock (r + 1) s₂ hr2
  have hne := gibt_wechselt hg
  exact hne (by rw [e1, e2])

/-- The waiting holder stays checker-eligible: live, dispatched, release-offering. -/
theorem ew_halter_bereit : SperrHalterBereit E_wait sW0 () stuckHalter := by
  intro hne
  refine ⟨sW0_live _, ⟨0, sW0_kerne0⟩, (), wGebenPlan, sW0, ?_, rfl, fun _ _ _ => trivial⟩
  exact ⟨(), rfl, Or.inl ⟨_, .besitzer stuckHalter [], rfl, rfl⟩⟩

/-- The holder-readiness holds at every cut of the waiting run. -/
theorem ew_bereit : ∀ t s', 0 ≤ t → ρ_w.zeit.zustand t = some s' →
    (s'.sperren ()).besitzer = some stuckHalter →
    SperrHalterBereit E_wait s' () stuckHalter := by
  intro t s' _ hzs _
  have hss : s' = sW0 := Option.some.inj (hzs.symm.trans rfl)
  subst hss
  exact ew_halter_bereit

/-- The waiting trace never hits the crash label. -/
theorem spur_w_kein_absturz (t : Nat) : spur_w t ≠ some (.absturz, absturzSpur) := by
  by_cases h : t % 2 = 0
  · rw [spur_w_even h]
    intro hcon
    have h01 : (0 : Nat) = 1 :=
      congrArg (fun o => match o with | none => 0 | some _ => 1) hcon
    omega
  · have h1 : t % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
      · exact (h h0).elim
      · exact h1
    rw [spur_w_odd h1]
    intro hcon
    have h01 : (0 : Nat) = 1 :=
      congrArg (fun o => match o with
        | some (.kontext _ _, _) => 0 | _ => 1) hcon
    omega

/-- The waiting run is crash-free. -/
theorem ew_crashfrei :
    ∀ k, 0 ≤ k → ρ_w.zeit.spur k ≠ some (.absturz, absturzSpur) := by
  intro k _
  exact spur_w_kein_absturz k

/-- The waiting run violates the section row: the holder waits on an await. -/
theorem ew_abschnitt_verletzt : ¬ AbschnittWartefrei E_wait := by
  intro hsec
  have h5 : E_wait.schranken.halten () = some 5 := rfl
  have hne : E_wait.schranken.halten () ≠ none := by
    rw [h5]
    exact Option.some_ne_none 5
  have hown : (sW0.sperren ()).besitzer = some stuckHalter := rfl
  have hb : wBlockiert sW0 stuckHalter (.warten ()) := ⟨rfl, rfl⟩
  have hbl := hsec sW0 stuckHalter () hne hown (.warten ()) hb
  exact hbl

/-- **Non-triviality (MK-05): without the section row, release is refutable.** The
    waiting twin satisfies holder-readiness, every hold bound and existential hardware
    fairness, holds its lock on a crash-free run — but waits on a never-enabled
    condition (violating `AbschnittWartefrei`), its implementation rule stays silent,
    and no release ever occurs. Uses `SperrGegenbeispiel`'s stuck-holder pattern with a
    live, dispatched, release-offering holder. -/
theorem sperr_freigabe_ohne_abschnitt_widerlegt :
    ¬ ∀ {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
      (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F) (ρ : Maschine.Lauf E)
      (l : L) (h : Kontext) (H b : Nat) (s : Zustand L Ort Wert Raum Lok Grund),
      (∀ t s', b ≤ t → ρ.zeit.zustand t = some s' → (s'.sperren l).besitzer = some h →
        SperrHalterBereit E s' l h) →
      HalteSchranken E ρ → E.schranken.halten l = some H →
      (∃ h', Laeufe E h' ρ ∧ FairLaeufe E.katalog h' ρ.hw) →
      ρ.zeit.zustand b = some s → (s.sperren l).besitzer = some h →
      (∀ k, b ≤ k → ρ.zeit.spur k ≠ some (.absturz, absturzSpur)) →
      ∃ r, b ≤ r ∧
        (∃ s₁ s₂, ρ.zeit.zustand r = some s₁ ∧ ρ.zeit.zustand (r + 1) = some s₂ ∧
          (s₁.sperren l).Gibt h (s₂.sperren l)) ∧
        Kontextkosten ρ h b (r + 1 - b) ≤ H + 1 := by
  intro hall
  have hinst := hall (E := E_wait) (ρ := ρ_w) (l := ()) (h := stuckHalter) (H := 5)
    (b := 0) (s := sW0)
  obtain ⟨r, _, ⟨s₁, s₂, hr1, hr2, hg⟩, _⟩ :=
    hinst ew_bereit ew_halte ew_halten ⟨h2, lauf_w, fair2⟩ rfl rfl ew_crashfrei
  exact ew_kein_gibt r s₁ s₂ hr1 hr2 _ hg

end Gabbro.Core.Fortschritt
