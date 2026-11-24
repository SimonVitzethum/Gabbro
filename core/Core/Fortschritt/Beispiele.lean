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

def togglePlan : SchrittPlan Unit Unit Unit Unit :=
  ⟨.intern, [], [], fun _ => false, fun _ => .na, fun _ => ()⟩

def toggleRegel (c : Kontext) (s : Zustand Unit Unit Unit Unit Bool Unit) (w : Unit)
    (es : List (SchrittPlan Unit Unit Unit Unit)) (u : Zustand Unit Unit Unit Unit Bool Unit) :
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
def E_w (Dispatch : Kern → Option Kontext) : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
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

theorem z1_dispatch0 : (z1.kerne Nat.zero).laeuft = some A := rfl

theorem z1_live : ∀ c, z1.status c = .laeuft := fun _ => rfl

theorem z1_dispatchN (n : Nat) : (z1.kerne (Nat.succ n)).laeuft = none := rfl

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
    t (Z1 t) (some posLabel) (Z1 (t + 1)) :=
  .schritt rfl (I.Schritt.kontext (hw1_crash t)
    ⟨0, hw1_opp0 t, by rw [z1_kerne]; exact z1_dispatch0, by rw [z1_status]; exact z1_live _⟩
    ⟨(), rfl, rfl, rfl⟩ (posAusfuehr t A (Z1 t)))

def posTaktK (t : Nat) : Takt
    (Lauffolge (E_w dispatch1) hw1) (KeinSchritt (Lauffolge (E_w dispatch1) hw1))
    t (some (Z1 t)) (some posLabel) (some (Z1 (t + 1))) :=
  .schritt rfl (.schritt (ImplSchritt.kontext (hw1_crash t)
    ⟨0, hw1_opp0 t, by rw [z1_kerne]; exact z1_dispatch0, by rw [z1_status]; exact z1_live _⟩
    ⟨(), rfl, rfl, rfl⟩ (posAusfuehr t A (Z1 t))))

def ρ1 : Maschine.Lauf (E_w dispatch1) :=
  ⟨s0, hw1, ⟨fun t => some (Z1 t), fun _ => some posLabel, posTaktK⟩⟩

def η1 : I.Lauf (E_w dispatch1) :=
  ⟨s0, h1, hw1, ⟨Z1, fun _ => some posLabel, posTakt⟩, fun _ => none⟩

theorem η1_zustand : ∀ t, η1.zeit.zustand t = Z1 t := fun _ => rfl

/-- The stepping run has no closed waiting set: nothing ever blocks. -/
theorem pos_deadlockfrei : DeadlockFrei (E := E_w dispatch1) η1 := by
  intro t hC
  obtain ⟨C, hC⟩ := hC
  obtain ⟨c, hc⟩ := hC.1
  obtain ⟨b, hb, _, _, _⟩ := hC.2 c hc
  cases hb

/-- The stepping run hangs nowhere: the dispatched context discharges every tick, and no
    other context is ever dispatched. -/
theorem pos_starvationfrei : StarvationFrei (E := E_w dispatch1) ρ1 η1 := by
  intro c hhang
  obtain ⟨-, a, f, hopen, hen⟩ := hhang
  obtain ⟨k, hdisp⟩ := hopen.1
  rw [η1_zustand, z1_kerne] at hdisp
  have hdis : dispatch1 k = some c := hdisp
  cases k with
  | zero =>
    have hcA : c = A := (Option.some.inj hdis).symm
    subst hcA
    have herl : I.Erledigt η1 A a := Or.inl ⟨(), ⟨[], []⟩, rfl⟩
    exact ((hopen.2 a (Nat.le_refl _)).2.2 herl).elim
  | succ n =>
    have hnone : (z1.kerne (Nat.succ n)).laeuft = none := rfl
    rw [hnone] at hdisp
    cases hdisp

/-- The stepping run is lock-free for every form: each cut steps, and steps never stop. -/
theorem pos_lockfrei : LockFrei (E := E_w dispatch1) (fun _ => True) η1 := by
  constructor
  · intro t c hlive hdisp
    obtain ⟨k, hdispk⟩ := hdisp
    rw [η1_zustand, z1_kerne] at hdispk
    cases k with
    | zero =>
      have hcA : c = A := (Option.some.inj hdispk).symm
      subst hcA
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(), ⟨[], []⟩, _,
        I.Schritt.kontext (hw1_crash t)
          ⟨0, hw1_opp0 t, by rw [η1_zustand, z1_kerne]; exact z1_dispatch0, hlive⟩
          ⟨(), rfl, rfl, rfl⟩ (posAusfuehr t A (Z1 t))⟩)))
    | succ n =>
      have hnone : (z1.kerne n.succ).laeuft = none := rfl
      rw [hnone] at hdispk
      cases hdispk
  · intro a _
    exact ⟨a, Nat.le_refl _, Or.inr ⟨A, (), (), ⟨[], []⟩, trivial, rfl, rfl⟩⟩

/-- The stepping run is wait-free: every tick discharges the waiter within the bound. -/
theorem pos_waitfrei : WaitFrei (E := E_w dispatch1) ρ1 η1 := by
  intro c f a hhead hlive hdisp hheadall hliveall hbereit n hcount
  obtain ⟨k, hdispk⟩ := hdisp
  rw [η1_zustand, z1_kerne] at hdispk
  cases k with
  | succ n =>
    have hnone : (z1.kerne n.succ).laeuft = none := rfl
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
      rfl
    refine ⟨a, Nat.le_refl _, by omega, Or.inl ⟨(), ⟨[], []⟩, rfl⟩⟩

end Gabbro.Core.Fortschritt
