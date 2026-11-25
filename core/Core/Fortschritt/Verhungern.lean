/-
  File:      Core/Fortschritt/Verhungern.lean
  Subject:   THE STARVATION RUN (PERFECT-MODEL §3.7, step M8): `A` steps on even ticks while `B`
             waits with a continuously enabled step on a fair two-core schedule. `deadlockFree`
             and `lockFree` hold on it; `starvationFree` and `waitFree` fail on `B`.
-/
module

public import Core.Fortschritt.Beispiele

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

-- The starvation run: `A` steps on even ticks, `B` waits with an enabled step. --


def zAB0 : Zustand Unit Unit Unit Unit Bool Unit := (I.start (E_w dispatch2) s0).2

def ctxAB : Nat → Kontext := fun t => if t % 2 = 0 then A else B

def ZAB : Nat → Zustand Unit Unit Unit Unit Bool Unit
  | 0 => zAB0
  | t + 1 => if t % 2 = 0 then toggleUpdate A (ZAB t) else ZAB t

def ZABρ : Nat → Zustand Unit Unit Unit Unit Bool Unit
  | 0 => zAB0
  | t + 1 => toggleUpdate (ctxAB t) (ZABρ t)

theorem zAB_kerne : ∀ t, (ZAB t).kerne = zAB0.kerne := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases h : t % 2 = 0
    · have hz : ZAB (t + 1) = toggleUpdate A (ZAB t) := by simp only [ZAB, if_pos h]
      rw [hz]
      exact ih
    · have hz : ZAB (t + 1) = ZAB t := by simp only [ZAB, if_neg h]
      rw [hz]
      exact ih

theorem zAB_status : ∀ t, (ZAB t).status = zAB0.status := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases h : t % 2 = 0
    · have hz : ZAB (t + 1) = toggleUpdate A (ZAB t) := by simp only [ZAB, if_pos h]
      rw [hz]
      exact ih
    · have hz : ZAB (t + 1) = ZAB t := by simp only [ZAB, if_neg h]
      rw [hz]
      exact ih

theorem zABρ_kerne : ∀ t, (ZABρ t).kerne = zAB0.kerne := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => exact ih

theorem zABρ_status : ∀ t, (ZABρ t).status = zAB0.status := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => exact ih

theorem zAB0_dispatch0 : (zAB0.kerne Nat.zero).laeuft = some A := rfl

theorem zAB0_dispatch1 : (zAB0.kerne (Nat.succ Nat.zero)).laeuft = some B := rfl

theorem zAB0_live : ∀ c, zAB0.status c = .laeuft := fun _ => rfl

theorem zAB0_dispatchN (m : Nat) : (zAB0.kerne (Nat.succ (Nat.succ m))).laeuft = none := rfl

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
    t (ZAB t) (spurAB t) (ZAB (t + 1)) := by
  by_cases h : t % 2 = 0
  · rw [spurAB_eq h]
    have hz : ZAB (t + 1) = toggleUpdate A (ZAB t) := by simp only [ZAB, if_pos h]
    rw [hz]
    exact .schritt rfl (I.Schritt.kontext (hw2_crash t)
      ⟨0, hw2_opp0 h, by rw [zAB_kerne]; exact zAB0_dispatch0,
        by rw [zAB_status]; exact zAB0_live _⟩
      ⟨(), rfl, rfl, rfl⟩ (abAusfuehr t A (ZAB t)))
  · have hz : ZAB (t + 1) = ZAB t := by simp only [ZAB, if_neg h]
    rw [spurAB_ne h, hz]
    exact .wartet rfl rfl (fun ho => Bool.false_ne_true ((hw2_crash t).symm.trans ho.2))

def taktABρ (t : Nat) : Takt
    (Lauffolge (E_w dispatch2) hw2) (KeinSchritt (Lauffolge (E_w dispatch2) hw2))
    t (some (ZABρ t)) (spurABρ t) (some (ZABρ (t + 1))) := by
  by_cases h : t % 2 = 0
  · rw [spurABρ_eq h]
    have hz : ZABρ (t + 1) = toggleUpdate A (ZABρ t) := by
      have : ctxAB t = A := by simp only [ctxAB, if_pos h]
      simp only [ZABρ, this]
    rw [hz]
    exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash t)
      ⟨0, hw2_opp0 h, by rw [zABρ_kerne]; exact zAB0_dispatch0,
        by rw [zABρ_status]; exact zAB0_live _⟩
      ⟨(), rfl, rfl, rfl⟩ (abAusfuehr t A (ZABρ t))))
  · have h1 : t % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
      · exact (h h0).elim
      · exact h1
    have hz : ZABρ (t + 1) = toggleUpdate B (ZABρ t) := by
      have : ctxAB t = B := by simp only [ctxAB, if_neg h]
      simp only [ZABρ, this]
    rw [spurABρ_ne h, hz]
    exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash t)
      ⟨1, hw2_opp1 h1, by rw [zABρ_kerne]; exact zAB0_dispatch1,
        by rw [zABρ_status]; exact zAB0_live _⟩
      ⟨(), rfl, rfl, rfl⟩ (abAusfuehr t B (ZABρ t))))

def ηAB : I.Lauf (E_w dispatch2) :=
  ⟨s0, h2, hw2, ⟨ZAB, spurAB, taktAB⟩, belegtAB⟩

theorem ηAB_zustand : ∀ t, ηAB.zeit.zustand t = ZAB t := fun _ => rfl

theorem ηAB_spur : ∀ t, ηAB.zeit.spur t = spurAB t := fun _ => rfl

def ρAB : Maschine.Lauf (E_w dispatch2) :=
  ⟨s0, hw2, ⟨fun t => some (ZABρ t), spurABρ, taktABρ⟩⟩

theorem ρAB_spur : ∀ t, ρAB.zeit.spur t = spurABρ t := fun _ => rfl

/-- `B` is never discharged on the starvation run. -/
theorem nie_erledigt_B : ∀ t, ¬ I.Erledigt ηAB B t := by
  intro t herl
  rcases herl with ⟨w, spur, heq⟩ | hcrash | ⟨e, hend⟩
  · by_cases h : t % 2 = 0
    · rw [ηAB_spur, spurAB_eq h] at heq
      have hctx := congrArg Prod.fst (Option.some.inj heq)
      have hAB : A = B := SchrittWahl.kontext.inj hctx |>.1
      cases hAB
    · rw [ηAB_spur, spurAB_ne h] at heq
      cases heq
  · by_cases h : t % 2 = 0
    · rw [ηAB_spur, spurAB_eq h] at hcrash
      have hcontra := Option.some.inj hcrash
      cases congrArg Prod.fst hcontra
    · rw [ηAB_spur, spurAB_ne h] at hcrash
      cases hcrash
  · rw [ηAB_zustand, zAB_status] at hend
    cases hend

/-- `B` is always enabled on the starvation run. -/
theorem bereit_B (t : Nat) (_ : 0 ≤ t) : I.Bereit (E := E_w dispatch2) (ZAB t) B :=
  ⟨(), [togglePlan], toggleUpdate B (ZAB t), (), rfl, rfl, rfl⟩

/-- `B` hangs on the fair schedule: dispatched, open, enabled, never discharged. -/
theorem hang_B : I.Haengt (E_w dispatch2) ρAB ηAB B := by
  refine ⟨fair2, 0, (), ⟨fun t _ => ⟨1, by rw [ηAB_zustand, zAB_kerne]; exact zAB0_dispatch1⟩,
    fun t _ => ⟨rfl, by rw [ηAB_zustand, zAB_status]; exact zAB0_live _, ?_⟩⟩, Or.inl ?_⟩
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
  intro t hC
  obtain ⟨C, hC⟩ := hC
  obtain ⟨c, hc⟩ := hC.1
  obtain ⟨b, hb, _, _, _⟩ := hC.2 c hc
  cases hb

/-- … and `lockFree` holds: every cut has its alternative and `A` steps forever. -/
theorem ab_lockfrei : LockFrei (E := E_w dispatch2) (fun _ => True) ηAB := by
  constructor
  · intro t c hlive hdisp
    obtain ⟨k, hdispk⟩ := hdisp
    rw [ηAB_zustand, zAB_kerne] at hdispk
    cases k with
    | zero =>
      have hcA : c = A := (Option.some.inj hdispk).symm
      subst hcA
      by_cases h : t % 2 = 0
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(), ⟨[], []⟩, _,
          I.Schritt.kontext (hw2_crash t)
            ⟨0, hw2_opp0 h, by rw [ηAB_zustand, zAB_kerne]; exact zAB0_dispatch0, hlive⟩
            ⟨(), rfl, rfl, rfl⟩ (abAusfuehr t A (ZAB t))⟩)))
      · refine Or.inr (Or.inr (Or.inr (Or.inr
          ⟨⟨(), [togglePlan], toggleUpdate A (ZAB t), (), rfl, rfl, rfl⟩, ?_⟩)))
        intro kern hk
        have hk0 : kern = 0 := by
          cases kern with
          | zero => rfl
          | succ n =>
            rw [ηAB_zustand, zAB_kerne] at hk
            cases n with
            | zero =>
              have hAB : B = A := Option.some.inj (zAB0_dispatch1.symm.trans hk)
              cases hAB
            | succ m =>
              rw [zAB0_dispatchN m] at hk
              cases hk
        have h1 : t % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
          · exact (h h0).elim
          · exact h1
        rw [hk0]
        exact hw2_opp0_neg h1
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
              rw [ηAB_zustand, zAB_kerne] at hk
              have hAB : A = B := Option.some.inj (zAB0_dispatch0.symm.trans hk)
              cases hAB
            | succ m =>
              cases m with
              | zero => rfl
              | succ m =>
                rw [ηAB_zustand, zAB_kerne, zAB0_dispatchN m] at hk
                cases hk
          rw [hk1]
          exact hw2_opp1_neg h
        · have h1 : t % 2 = 1 := by
            rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
            · exact (h h0).elim
            · exact h1
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(), ⟨[], []⟩, _,
            I.Schritt.kontext (hw2_crash t)
              ⟨1, hw2_opp1 h1, by rw [ηAB_zustand, zAB_kerne]; exact zAB0_dispatch1, hlive⟩
              ⟨(), rfl, rfl, rfl⟩ (abAusfuehr t B (ZAB t))⟩)))
      | succ m =>
        have hnone : (zAB0.kerne (Nat.succ (Nat.succ m))).laeuft = none := rfl
        rw [hnone] at hdispk
        cases hdispk
  · intro a hactive
    match hm : a % 2 with
    | 0 => exact ⟨a, Nat.le_refl _, Or.inr ⟨A, (), (), ⟨[], []⟩, trivial, rfl, spurAB_eq hm⟩⟩
    | _ + 1 =>
      have ha1 : a % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one a with ha0 | ha1
        · rw [ha0] at hm
          cases hm
        · exact ha1
      have h1 : (a + 1) % 2 = 0 := by
        rw [← Nat.mod_add_mod a 2 1, ha1]
      exact ⟨a + 1, Nat.le_succ _, Or.inr ⟨A, (), (), ⟨[], []⟩, trivial, rfl, spurAB_eq h1⟩⟩

/-- … but `waitFree` fails for `B`: unboundedly many own steps, never discharged. -/
theorem ab_waitfrei_neg : ¬ WaitFrei (E := E_w dispatch2) ρAB ηAB := by
  intro hwf
  have h1 : (E_w dispatch2).stotterLaenge () = 1 := rfl
  have hcc : Kontextkosten ρAB B 0 4 = 2 := rfl
  obtain ⟨t, _, _, herl⟩ := hwf B () 0 rfl rfl ⟨1, rfl⟩
    (fun t _ => rfl) (fun t _ => by rw [ηAB_zustand, zAB_status]; exact zAB0_live _) (fun t _ => bereit_B t (Nat.zero_le t)) 4
    (by rw [h1, hcc]; omega)
  exact (nie_erledigt_B t herl).elim
end Gabbro.Core.Fortschritt
