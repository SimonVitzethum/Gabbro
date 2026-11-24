/-
  File:      Core/Fortschritt/Beispiele.lean
  Subject:   RUN WITNESSES FOR THE PROGRESS CLASSES (PERFECT-MODEL §3.7, step M8): one stepping
             run where every class holds, and the starvation run where `deadlockFree` and
             `lockFree` hold but `starvationFree` and `waitFree` fail.

  The unit `E_w` toggles one local bit per step on every core (`toggleRegel`, the same shape
  as the `fortschritt_erfuellbar` witness); nothing is assumed about a scheduler — dispatch,
  opportunities and steps are explicit run data. The positive run steps its single context on
  every tick under fair hardware; the AB run steps `A` on even ticks while `B` waits with a
  continuously enabled step on a fair two-core schedule.
-/
module

public import Core.Fortschritt.Saetze

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

/-- The two witness contexts. -/
def A : Kontext := Kontext.faden 0

def B : Kontext := Kontext.faden 1

/-- One local toggle per step; the memory side is empty. -/
def toggleUpdate (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) :
    Zustand Unit Unit Unit Unit Bool Unit :=
  { s with lokal := Function.update s.lokal c (!s.lokal c) }

def togglePlan : SchrittPlan Unit Unit Unit :=
  ⟨.intern, [], [], fun _ => false, fun _ => .na, fun _ => ()⟩

def toggleRegel (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) (w : Unit)
    (es : List (SchrittPlan Unit Unit Unit)) (u : Zustand Unit Unit Unit Unit Bool Unit) :
    Prop :=
  es = [togglePlan] ∧ u = toggleUpdate c s

def toggleSystem : MaschinenSystem Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  ⟨fun _ => ⟨toggleRegel, toggleRegel⟩, fun _ _ => some (), fun _ _ => False,
    fun _ _ _ => False⟩

def wDaten (Dispatch : Kern → Option Kontext) : Startdaten Unit Unit Bool Unit :=
  ⟨fun _ => false, fun _ => .laeuft,
    fun j => ⟨Dispatch j, .nutzer, (), fun _ => false, 0, false, []⟩,
    ⟨fun _ => false, fun _ => 0⟩⟩

def wEinrichtung (Dispatch : Kern → Option Kontext) :
    Einrichtung Unit Unit Unit Unit Bool Unit Unit :=
  ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ _ _ => False, fun _ _ => True,
    ⟨0, 1⟩, ⟨A, 0, fun _ => wDaten Dispatch, fun _ _ => ()⟩, fun _ => 0, fun _ _ _ => none⟩

def wBild : Bild := ⟨.elf, fun a => if a = 0 then some 0 else none, [0]⟩

def dispatch1 : Kern → Option Kontext
  | 0 => some A
  | _ + 1 => none

def dispatch2 : Kern → Option Kontext
  | 0 => some A
  | 1 => some B
  | _ + 2 => none

/-- The witness unit: toggle steps, no blocked reasons, checked stutter length one. -/
def E_w (Dispatch : Kern → Option Kontext) : Einheit Unit Unit Unit Unit Bool Unit Unit Unit :=
  ⟨Plattform.x86_64.katalog, wBild, wEinrichtung Dispatch, toggleSystem,
    fun _ => wDaten Dispatch, fun _ => 0,
    fun _ _ => some (Zustand.start (fun _ => false) (fun _ => .laeuft)
      (fun j => ⟨Dispatch j, .nutzer, (), fun _ => false, 0, false, []⟩)
      ⟨fun _ => false, fun _ => 0⟩ (fun _ => ()) (.leer (fun _ => 0))),
    Eq, fun _ => 1, .leer, .leer, .leer, .leer⟩

def sicht0 : Nat → AussenVerlauf → AussenSicht :=
  fun _ _ => ⟨fun _ => ⟨0, false, false, [], fun _ => 0⟩, fun _ _ => none, fun _ _ => none⟩

def s0 : AussenStart := ⟨0, fun _ => some 0, [], fun _ => none, sicht0 0 []⟩

def z1 : Zustand Unit Unit Unit Unit Bool Unit := (I.start (E_w dispatch1) s0).2

def Z1 : Nat → Zustand Unit Unit Unit Unit Bool Unit
  | 0 => z1
  | t + 1 => toggleUpdate A (Z1 t)

theorem z1_kerne : ∀ t, (Z1 t).kerne = z1.kerne := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => exact ih

theorem z1_status : ∀ t, (Z1 t).status = z1.status := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => exact ih

def posLabel : SchrittWahl Unit × SchrittSpur Unit Unit :=
  (.kontext A (), ⟨[], []⟩)

def bLabel : SchrittWahl Unit × SchrittSpur Unit Unit :=
  (.kontext B (), ⟨[], []⟩)

def hw1 : HwLauf := Umgebung.referenzLauf Plattform.x86_64.katalog 1 sicht0

def h1 : Umgebung := Umgebung.referenz Plattform.x86_64.katalog 1 sicht0

theorem hw1_core (t : Nat) : (hw1.angebot t).core = some (t % 1) := rfl

theorem hw1_crash (t : Nat) : (hw1.angebot t).crash = false := rfl

theorem hw1_opp0 (t : Nat) : hw1.gelegenheit t 0 := by
  show (hw1.angebot t).core = some 0
  rw [hw1_core, Nat.mod_one t]

def posAusfuehr (t : Nat) (c : Kontext) (x : Zustand Unit Unit Unit Unit Bool Unit) :
    FuehrtSchrittAus (E_w dispatch1).einrichtung t c x (toggleUpdate c x) togglePlan ⟨[], []⟩
      (toggleUpdate c x) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, [], toggleUpdate c x, .intern, .nil _, rfl⟩

def posTakt (t : Nat) : Takt
    (I.Schritt (E_w dispatch1).einrichtung (E_w dispatch1).system
      (E_w dispatch1).katalog hw1)
    (fun t _ => ¬ AbsturzAngeboten (E_w dispatch1).katalog hw1 t)
    (Z1 t) (some posLabel) (Z1 (t + 1)) :=
  .schritt rfl (I.Schritt.kontext (hw1_crash t)
    ⟨0, hw1_opp0 t, by rw [z1_kerne], by rw [z1_status]⟩
    ⟨(), rfl, rfl, rfl⟩ (posAusfuehr t A (Z1 t)))

def posTaktK (t : Nat) : Takt
    (Lauffolge (E_w dispatch1) hw1) (some (Z1 t)) (some posLabel) (some (Z1 (t + 1))) :=
  .schritt rfl (.schritt (ImplSchritt.kontext (hw1_crash t)
    ⟨0, hw1_opp0 t, by rw [z1_kerne], by rw [z1_status]⟩
    ⟨(), rfl, rfl, rfl⟩ (posAusfuehr t A (Z1 t))))

def ρ1 : Maschine.Lauf (E_w dispatch1) :=
  ⟨s0, hw1, ⟨fun t => some (Z1 t), fun _ => some posLabel, posTaktK⟩⟩

def η1 : I.Lauf (E_w dispatch1) :=
  ⟨s0, h1, hw1, ⟨Z1, fun _ => some posLabel, posTakt⟩, fun _ => none⟩

/-- Counting lemma: an everywhere-true marker fills the window. -/
theorem zaehle_all_true (m : Nat → Bool) (a n : Nat) (hall : ∀ t, m (a + t) = true) :
    I.zaehle m a n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hif : (if m (a + n) then 1 else 0) = 1 := if_pos (hall n)
    simp only [I.zaehle, hif]
    rw [ih]

/-- The stepping run has no closed waiting set: nothing ever blocks. -/
theorem pos_deadlockfrei : DeadlockFrei (E := E_w dispatch1) η1 := by
  intro t C hC
  obtain ⟨c, hc⟩ := hC.1
  obtain ⟨b, hb, _, _, _⟩ := hC.2 c hc
  cases hb

/-- The stepping run hangs nowhere: the dispatched context discharges every tick, and no
    other context is ever dispatched. -/
theorem pos_starvationfrei : StarvationFrei (E := E_w dispatch1) ρ1 η1 := by
  intro c hhang
  obtain ⟨-, a, f, hopen, hen⟩ := hhang
  obtain ⟨k, hdisp⟩ := hopen.1
  rw [z1_kerne] at hdisp
  have hdis : dispatch1 k = some c := hdisp
  cases k with
  | zero =>
    have hcA : c = A := (Option.some.inj hdis).symm
    subst hcA
    have herl : I.Erledigt η1 A a := Or.inl ⟨(), ⟨[], []⟩, rfl⟩
    exact ((hopen.2 a (Nat.le_refl _)).2.2 herl).elim
  | succ n =>
    have hnone : dispatch1 (n + 1) = none := rfl
    rw [hnone] at hdis
    cases hdis

/-- The stepping run is lock-free for every form: each cut steps, and steps never stop. -/
theorem pos_lockfrei : LockFrei (E := E_w dispatch1) (fun _ => True) η1 := by
  constructor
  · intro t c hlive hdisp
    obtain ⟨k, hdispk⟩ := hdisp
    rw [z1_kerne] at hdispk
    cases k with
    | zero =>
      have hcA : c = A := (Option.some.inj hdispk).symm
      subst hcA
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(), ⟨[], []⟩, _,
        I.Schritt.kontext (hw1_crash t)
          ⟨0, hw1_opp0 t, by rw [z1_kerne], hlive⟩
          ⟨(), rfl, rfl, rfl⟩ (posAusfuehr t A (Z1 t))⟩)))
    | succ n =>
      have hnone : dispatch1 (n + 1) = none := rfl
      rw [hnone] at hdispk
      cases hdispk
  · intro a _
    exact ⟨a, Nat.le_refl _, Or.inr ⟨A, (), (), ⟨[], []⟩, trivial, rfl, rfl⟩⟩

/-- The stepping run is wait-free: every tick discharges the waiter within the bound. -/
theorem pos_waitfrei : WaitFrei (E := E_w dispatch1) ρ1 η1 := by
  intro c f a hhead hlive hdisp hheadall hliveall hbereit n hcount
  obtain ⟨k, hdispk⟩ := hdisp
  rw [z1_kerne] at hdispk
  cases k with
  | succ n =>
    have hnone : dispatch1 (n + 1) = none := rfl
    rw [hnone] at hdispk
    cases hdispk
  | zero =>
    have hcA : c = A := (Option.some.inj hdispk).symm
    subst hcA
    have hnn : Kontextkosten ρ1 A a n = n := by
      have hkk : Kontextkosten ρ1 A a n =
          I.zaehle (fun t => match ρ1.zeit.spur t with
            | some (.kontext d _, _) => decide (A = d)
            | some (.antwort _, _) | some (.interrupt _, _) | some (.absturz, _) | none => false) a n := rfl
      rw [hkk]
      apply zaehle_all_true
      intro t
      simp only [decide_eq_true_eq]
    refine ⟨a, Nat.le_refl _, by omega, Or.inl ⟨(), ⟨[], []⟩, rfl⟩⟩

-- The starvation run: `A` steps on even ticks, `B` waits with an enabled step. --

def hw2 : HwLauf := Umgebung.referenzLauf Plattform.x86_64.katalog 2 sicht0

def h2 : Umgebung := Umgebung.referenz Plattform.x86_64.katalog 2 sicht0

theorem hw2_valid : KatalogWohlgeformt Plattform.x86_64.katalog :=
  Plattform.x86_64.katalog_wohlgeformt

theorem fair2 : FairLaeufe Plattform.x86_64.katalog h2 hw2 :=
  Umgebung.referenz_fair _ _ _ hw2_valid (by decide)

theorem hw2_core (t : Nat) : (hw2.angebot t).core = some (t % 2) := rfl

theorem hw2_crash (t : Nat) : (hw2.angebot t).crash = false := rfl

theorem hw2_opp0 {t : Nat} (h : t % 2 = 0) : hw2.gelegenheit t 0 := by
  show (hw2.angebot t).core = some 0
  rw [hw2_core, h]

theorem hw2_opp1 {t : Nat} (h : t % 2 = 1) : hw2.gelegenheit t 1 := by
  show (hw2.angebot t).core = some 1
  rw [hw2_core, h]

theorem hw2_opp0_neg {t : Nat} (h : t % 2 = 1) : ¬ hw2.gelegenheit t 0 := by
  intro ho
  have ho' : (hw2.angebot t).core = some 0 := ho
  rw [hw2_core, h] at ho'
  cases ho'

theorem hw2_opp1_neg {t : Nat} (h : t % 2 = 0) : ¬ hw2.gelegenheit t 1 := by
  intro ho
  have ho' : (hw2.angebot t).core = some 1 := ho
  rw [hw2_core, h] at ho'
  cases ho'

def zAB0 : Zustand Unit Unit Unit Unit Bool Unit := (I.start (E_w dispatch2) s0).2

def ctxAB : Nat → Kontext := fun t => if t % 2 = 0 then A else B

def ZAB : Nat → Zustand Unit Unit Unit Unit Bool Unit
  | 0 => zAB0
  | t + 1 => toggleUpdate (ctxAB t) (ZAB t)

theorem zAB_kerne : ∀ t, (ZAB t).kerne = zAB0.kerne := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => exact ih

theorem zAB_status : ∀ t, (ZAB t).status = zAB0.status := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => exact ih

theorem zAB0_dispatch0 : (zAB0.kerne 0).laeuft = some A := rfl

theorem zAB0_dispatch1 : (zAB0.kerne 1).laeuft = some B := rfl

theorem zAB0_dispatchN (m : Nat) : (zAB0.kerne (m + 2)).laeuft = none := rfl

def spurAB (t : Nat) : Option (SchrittWahl Unit × SchrittSpur Unit Unit) :=
  if t % 2 = 0 then some posLabel else none

def spurABρ (t : Nat) : Option (SchrittWahl Unit × SchrittSpur Unit Unit) :=
  if t % 2 = 0 then some posLabel else some bLabel

def belegtAB (t : Nat) : Option Kontext :=
  if t % 2 = 0 then none else some B

theorem spurAB_eq {t : Nat} (h : t % 2 = 0) : spurAB t = some posLabel := by
  simp only [spurAB, if_pos h]

theorem spurAB_ne {t : Nat} (h : ¬ t % 2 = 0) : spurAB t = none := by
  simp only [spurAB, if_neg h]

theorem spurABρ_eq {t : Nat} (h : t % 2 = 0) : spurABρ t = some posLabel := by
  simp only [spurABρ, if_pos h]

theorem spurABρ_ne {t : Nat} (h : ¬ t % 2 = 0) : spurABρ t = some bLabel := by
  simp only [spurABρ, if_neg h]

def abAusfuehr (t : Nat) (c : Kontext) (x : Zustand Unit Unit Unit Unit Bool Unit) :
    FuehrtSchrittAus (E_w dispatch2).einrichtung t c x (toggleUpdate c x) togglePlan ⟨[], []⟩
      (toggleUpdate c x) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, [], toggleUpdate c x, .intern, .nil _, rfl⟩

def taktAB (t : Nat) : Takt
    (I.Schritt (E_w dispatch2).einrichtung (E_w dispatch2).system
      (E_w dispatch2).katalog hw2)
    (fun t _ => ¬ AbsturzAngeboten (E_w dispatch2).katalog hw2 t)
    (ZAB t) (spurAB t) (ZAB (t + 1)) := by
  by_cases h : t % 2 = 0
  · rw [spurAB_eq h]
    exact .schritt rfl (I.Schritt.kontext (hw2_crash t)
      ⟨0, hw2_opp0 h, by rw [zAB_kerne]; exact zAB0_dispatch0,
        by rw [zAB_status]⟩
      ⟨(), rfl, rfl, rfl⟩ (abAusfuehr t A (ZAB t)))
  · rw [spurAB_ne h]
    exact .wartet rfl rfl (fun ho => Bool.false_ne_true ((hw2_crash t).symm.trans ho.2))

def taktABρ (t : Nat) : Takt
    (Lauffolge (E_w dispatch2) hw2)
    (ZAB t) (spurABρ t) (ZAB (t + 1)) := by
  by_cases h : t % 2 = 0
  · rw [spurABρ_eq h]
    exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash t)
      ⟨0, hw2_opp0 h, by rw [zAB_kerne]; exact zAB0_dispatch0,
        by rw [zAB_status]⟩
      ⟨(), rfl, rfl, rfl⟩ (abAusfuehr t A (ZAB t))))
  · have h1 : t % 2 = 1 := by omega
    rw [spurABρ_ne h]
    exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash t)
      ⟨1, hw2_opp1 h1, by rw [zAB_kerne]; exact zAB0_dispatch1,
        by rw [zAB_status]⟩
      ⟨(), rfl, rfl, rfl⟩ (abAusfuehr t B (ZAB t))))

def ηAB : I.Lauf (E_w dispatch2) :=
  ⟨s0, h2, hw2, ⟨ZAB, spurAB, taktAB⟩, belegtAB⟩

def ρAB : Maschine.Lauf (E_w dispatch2) :=
  ⟨s0, hw2, ⟨fun t => some (ZAB t), spurABρ, taktABρ⟩⟩

/-- `B` is never discharged on the starvation run. -/
theorem nie_erledigt_B : ∀ t, ¬ I.Erledigt ηAB B t := by
  intro t herl
  rcases herl with ⟨w, spur, heq⟩ | hcrash | ⟨e, hend⟩
  · by_cases h : t % 2 = 0
    · rw [spurAB_eq h] at heq
      have hctx := congrArg Prod.fst (Option.some.inj heq)
      have hAB : A = B := SchrittWahl.kontext.inj hctx |>.1
      cases hAB
    · rw [spurAB_ne h] at heq
      cases heq
  · by_cases h : t % 2 = 0
    · rw [spurAB_eq h] at hcrash
      have hcontra := Option.some.inj hcrash
      cases congrArg Prod.fst hcontra
    · rw [spurAB_ne h] at hcrash
      cases hcrash
  · rw [zAB_status] at hend
    cases hend

/-- `B` is always enabled on the starvation run. -/
theorem bereit_B (t : Nat) (_ : 0 ≤ t) : I.Bereit (E := E_w dispatch2) (ZAB t) B :=
  ⟨(), [togglePlan], toggleUpdate B (ZAB t), (), rfl, rfl, rfl⟩

/-- `B` hangs on the fair schedule: dispatched, open, enabled, never discharged. -/
theorem hang_B : I.Haengt (E_w dispatch2) ρAB ηAB B := by
  refine ⟨fair2, 0, (), ⟨⟨1, rfl⟩, fun t _ => ⟨rfl, by rw [zAB_status], ?_⟩⟩, Or.inl ?_⟩
  · intro herl
    exact nie_erledigt_B t herl
  · intro t _
    exact bereit_B t (Nat.zero_le t)

/-- On the starvation run `starvationFree` fails … -/
theorem ab_starvationfrei_neg : ¬ StarvationFrei (E := E_w dispatch2) ρAB ηAB := by
  intro h
  exact h B hang_B

/-- … while `deadlockFree` holds: nothing ever blocks. -/
theorem ab_deadlockfrei : DeadlockFrei (E := E_w dispatch2) ηAB := by
  intro t C hC
  obtain ⟨c, hc⟩ := hC.1
  obtain ⟨b, hb, _, _, _⟩ := hC.2 c hc
  cases hb

/-- … and `lockFree` holds: every cut has its alternative and `A` steps forever. -/
theorem ab_lockfrei : LockFrei (E := E_w dispatch2) (fun _ => True) ηAB := by
  constructor
  · intro t c hlive hdisp
    obtain ⟨k, hdispk⟩ := hdisp
    rw [zAB_kerne] at hdispk
    cases k with
    | zero =>
      have hcA : c = A := (Option.some.inj hdispk).symm
      subst hcA
      by_cases h : t % 2 = 0
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(), ⟨[], []⟩, _,
          I.Schritt.kontext (hw2_crash t)
            ⟨0, hw2_opp0 h, by rw [zAB_kerne]; exact zAB0_dispatch0, hlive⟩
            ⟨(), rfl, rfl, rfl⟩ (abAusfuehr t A (ZAB t))⟩)))
      · refine Or.inr (Or.inr (Or.inr (Or.inr
          ⟨⟨(), [togglePlan], toggleUpdate A (ZAB t), (), rfl, rfl, rfl⟩, ?_⟩)))
        intro kern hk
        have hk0 : kern = 0 := by
          cases kern with
          | zero => rfl
          | succ n =>
            rw [zAB_kerne] at hk
            cases n with
            | zero =>
              have hAB : B = A := Option.some.inj (zAB0_dispatch1.symm.trans hk)
              cases hAB
            | succ m =>
              rw [zAB0_dispatchN m] at hk
              cases hk
        have h1 : t % 2 = 1 := by omega
        exact hw2_opp0_neg h1 (hk0 ▸ hk)
    | succ n =>
      cases n with
      | zero =>
        have hcB : c = B := (Option.some.inj hdispk).symm
        subst hcB
        by_cases h : t % 2 = 0
        · refine Or.inr (Or.inr (Or.inr (Or.inr
            ⟨⟨(), [togglePlan], toggleUpdate B (ZAB t), (), rfl, rfl, rfl⟩, ?_⟩)))
          intro kern hk
          have hk1 : kern = 1 := by
            cases kern with
            | zero =>
              rw [zAB_kerne] at hk
              have hAB : A = B := Option.some.inj (zAB0_dispatch0.symm.trans hk)
              cases hAB
            | succ m =>
              cases m with
              | zero => rfl
              | succ m =>
                rw [zAB_kerne, zAB0_dispatchN m] at hk
                cases hk
          exact hw2_opp1_neg h (hk1 ▸ hk)
        · have h1 : t % 2 = 1 := by omega
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(), ⟨[], []⟩, _,
            I.Schritt.kontext (hw2_crash t)
              ⟨1, hw2_opp1 h1, by rw [zAB_kerne]; exact zAB0_dispatch1, hlive⟩
              ⟨(), rfl, rfl, rfl⟩ (abAusfuehr t B (ZAB t))⟩)))
      | succ m =>
        have hnone : (zAB0.kerne (m + 2)).laeuft = none := rfl
        rw [hnone] at hdispk
        cases hdispk
  · intro a hactive
    by_cases ha : a % 2 = 0
    · exact ⟨a, Nat.le_refl _, Or.inr ⟨A, (), (), ⟨[], []⟩, trivial, rfl, spurAB_eq ha⟩⟩
    · have h1 : (a + 1) % 2 = 0 := by omega
      exact ⟨a + 1, Nat.le_succ _, Or.inr ⟨A, (), (), ⟨[], []⟩, trivial, rfl, spurAB_eq h1⟩⟩

/-- … but `waitFree` fails for `B`: unboundedly many own steps, never discharged. -/
theorem ab_waitfrei_neg : ¬ WaitFrei (E := E_w dispatch2) ρAB ηAB := by
  intro hwf
  have h1 : (E_w dispatch2).stotterLaenge () = 1 := rfl
  have hcc : Kontextkosten ρAB B 0 4 = 2 := rfl
  obtain ⟨t, _, _, herl⟩ := hwf B () 0 rfl rfl ⟨1, rfl⟩
    (fun t _ => rfl) (fun t _ => by rw [zAB_status]) (fun t _ => bereit_B t (Nat.zero_le t)) 4
    (by rw [h1, hcc]; omega)
  exact (nie_erledigt_B t herl).elim

end Gabbro.Core.Fortschritt
