/-
  File:      Core/Fortschritt/Sackgasse.lean
  Subject:   THE DEADLOCK COUNTEREXAMPLE AND THE STALL (PERFECT-MODEL §3.7, step M8): a run
             with a closed waiting set where `deadlockFree` fails but `starvationFree` and
             `lockFree` hold, and a run where `lockFree` fails but `deadlockFree` holds.

  `E_dead` is a two-lock unit whose only rules never step; `A` waits on the lock `B` holds
  and `B` waits on the lock `A` holds. `B` in the AB setup never hangs for hardware reasons —
  the schedule is unfair — so `starvationFree` holds vacuously while the closed set stands.
  The stall run never steps although steps stay enabled: per-cut alternatives hold, but no
  system step ever happens.
-/
module

public import Core.Fortschritt.Beispiele

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

/-- The stalled run: enabled steps, but none is ever taken. -/
def ηstall : I.Lauf (E_w dispatch2) :=
  ⟨s0, h2, hw2, ⟨fun _ => zAB0, fun _ => none, fun t =>
    .wartet rfl rfl (fun ho => Bool.false_ne_true ((hw2_crash t).symm.trans ho.2))⟩,
    fun _ => none⟩

/-- On the stall `lockFree` fails (no system step ever happens) … -/
theorem stall_lockfrei_neg : ¬ LockFrei (E := E_w dispatch2) (fun _ => True) ηstall := by
  intro h
  have hactive : SystemAktiv (fun _ => True) ηstall 0 := by
    intro n _
    exact ⟨n, Nat.le_refl _, A, (), trivial, rfl, rfl,
      ⟨(), [togglePlan], toggleUpdate A zAB0, (), rfl, rfl, rfl⟩⟩
  obtain ⟨t, _, hor⟩ := h.2 0 hactive
  have hnone : ηstall.zeit.spur t = none := rfl
  rcases hor with hcrash | ⟨c, f, w, spur, _, _, heq⟩
  · rw [hnone] at hcrash
    cases hcrash
  · rw [hnone] at heq
    cases heq

/-- … while `deadlockFree` holds: nothing ever blocks. -/
theorem stall_deadlockfrei_pos : DeadlockFrei (E := E_w dispatch2) ηstall := by
  intro t C hC
  obtain ⟨c, hc⟩ := hC.1
  obtain ⟨b, hb, _, _, _⟩ := hC.2 c hc
  cases hb

/-- The deadlocked unit: two locks, rules that never step, cross-held locks. -/
def deadBlockiert (s : Zustand Bool Unit Unit Unit Bool Unit) (c : Kontext)
    (b : Blockade Bool Unit) : Prop :=
  (c = A ∧ b = .sperre true) ∨ (c = B ∧ b = .sperre false)

def deadRegel (c : Kontext) (s : Zustand Bool Unit Unit Unit Bool Unit) (w : Unit)
    (es : List (SchrittPlan Unit Unit Unit)) (u : Zustand Bool Unit Unit Unit Bool Unit) :
    Prop :=
  False

def deadSystem : MaschinenSystem Bool Unit Unit Unit Bool Unit Unit Unit Unit :=
  ⟨fun _ => ⟨deadRegel, deadRegel⟩, fun _ _ => some (), fun _ _ => False, deadBlockiert⟩

def deadEinrichtung : Einrichtung Bool Unit Unit Unit Bool Unit Unit :=
  ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ _ _ => False, fun _ _ => True,
    ⟨0, 1⟩, ⟨A, 0, fun _ => wDaten dispatch1, fun _ _ => ()⟩, fun _ => 0, fun _ _ _ => none⟩

def deadStart : Zustand Bool Unit Unit Unit Bool Unit :=
  { (Zustand.start (fun _ => false) (fun _ => .laeuft)
      (fun j => ⟨dispatch1 j, .nutzer, (), fun _ => false, 0, false, []⟩)
      ⟨fun _ => false, fun _ => 0⟩ (fun _ => ()) (.leer (fun _ => 0))) with
    sperren := fun l => if l then ⟨some B, []⟩ else ⟨some A, []⟩ }

def E_dead : Einheit Bool Unit Unit Unit Bool Unit Unit Unit :=
  ⟨Plattform.x86_64.katalog, wBild, deadEinrichtung, deadSystem,
    fun _ => wDaten dispatch1, fun _ => 0, fun _ _ => some deadStart,
    Eq, fun _ => 1, .leer, .leer, .leer, .leer⟩

def hwDead : HwLauf :=
  ⟨fun _ => ⟨none, fun _ => false, [], fun _ => false, false, false, 0⟩,
    (Umgebung.referenz Plattform.x86_64.katalog 1 sicht0).politik⟩

def ηdead : I.Lauf E_dead :=
  ⟨s0, h1, hwDead, ⟨fun _ => deadStart, fun _ => none, fun t =>
    .wartet rfl rfl (fun ho => Bool.false_ne_true ho.2)⟩, fun _ => none⟩

def ρdead : Maschine.Lauf E_dead :=
  ⟨s0, hwDead, ⟨fun _ => none, fun _ => none,
    fun t => .wartet rfl rfl (fun _ _ step => by cases step)⟩⟩

theorem unfair_dead : ¬ FairLaeufe E_dead.katalog h1 hwDead := by
  intro fair
  obtain ⟨i, _, ho⟩ := fair.kerne.2 0 (Nat.zero_lt_succ 0) 0
  cases ho

/-- On the deadlocked run `deadlockFree` fails: `A` and `B` form a closed waiting set. -/
theorem dead_deadlockfrei_neg : ¬ DeadlockFrei (E := E_dead) ηdead := by
  intro h
  have hC : GeschlossenWartend E_dead deadStart (fun c => c = A ∨ c = B) := by
    refine ⟨⟨A, Or.inl rfl⟩, fun c hc => ?_⟩
    rcases hc with rfl | rfl
    · refine ⟨.sperre true, Or.inl ⟨rfl, rfl⟩, trivial, ?_, ?_⟩
      · intro l hl
        cases hl
        exact ⟨B, Or.inr rfl, rfl⟩
      · intro k hk
        cases hk
    · refine ⟨.sperre false, Or.inr ⟨rfl, rfl⟩, trivial, ?_, ?_⟩
      · intro l hl
        cases hl
        exact ⟨A, Or.inl rfl, rfl⟩
      · intro k hk
        cases hk
  exact h 0 ⟨_, hC⟩

/-- … while `starvationFree` holds: the schedule is unfair, so nothing hangs on it. -/
theorem dead_starvationfrei_pos : StarvationFrei (E := E_dead) ρdead ηdead := by
  intro c hhang
  exact unfair_dead hhang.1

/-- … and `lockFree` holds: blocked cuts have their alternative, and nothing is enabled. -/
theorem dead_lockfrei_pos : LockFrei (E := E_dead) (fun _ => True) ηdead := by
  constructor
  · intro t c hlive hdisp
    obtain ⟨k, hdispk⟩ := hdisp
    have hker : (ηdead.zeit.zustand t).kerne = deadStart.kerne := rfl
    rw [hker] at hdispk
    cases k with
    | zero =>
      have hcA : c = A := (Option.some.inj hdispk).symm
      subst hcA
      exact Or.inr (Or.inl ⟨.sperre true, Or.inl ⟨rfl, rfl⟩⟩)
    | succ n =>
      have hnone : (deadStart.kerne (n + 1)).laeuft = none := rfl
      rw [hnone] at hdispk
      cases hdispk
  · intro a hactive
    obtain ⟨t, hta, c, f, _, _, _, hber⟩ := hactive a (Nat.le_refl _)
    obtain ⟨w, plans, u, i, _, himp⟩ := hber
    cases himp

end Gabbro.Core.Fortschritt
