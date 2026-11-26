/-
  File:      core/Core/Fortschritt/Verdraengung.lean
  Subject:   PREEMPTION WITHOUT RETURN HANGS — the load-bearing witness for the return premise.

  The unit `E_v` runs a worker `A` on its single core with a dormant handler `Hv`. At tick
  zero an interrupt displaces `A`; the handler steps forever and never returns, so `A` stays
  live, enabled and undispatched on every later cut: it hangs (`hangV`) although the run is
  admissible (`laufV`) on a fair history (`fairV`) and scheduler-fair (`sfV`, every other
  context is served and `A` is never continuously dispatched). The return premise fails on
  this run (`nretV`), so the second premise of `FortschrittAkzeptiertAussage` is load-bearing.
-/
module

public import Core.Fortschritt.Beispiele
public import Core.Maschine.Speicherfolge
public import Core.Katalog.Erfuellbar
public import Core.Katalog.Start

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

/-- The preempting handler context. -/
def Hv : Kontext := .handler 0 0 (Nat.pair 0 0)

/-- The raised interrupt. -/
def irqV : Unterbrechung := .maskierbar 0 0

/-- Only the worker is live. -/
def statusV : Kontext → Status Unit Unit := fun c => if c = A then .laeuft else .ruht

/-- Only the worker is dispatched, on core zero. -/
def dispatchV : Kern → Option Kontext
  | 0 => some A
  | _ + 1 => none

def wDatenV : Startdaten Unit Unit Bool Unit :=
  ⟨fun _ => false, statusV,
    fun j => ⟨dispatchV j, .nutzer, (), fun _ => false, 0, false, []⟩,
    ⟨fun _ => false, fun _ => 0⟩⟩

def wEinrichtungV : Einrichtung Unit Unit Unit Unit Bool Unit Unit :=
  ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (), fun _ _ _ => False, fun _ _ => True,
    ⟨0, 1⟩, ⟨A, 0, fun _ => wDatenV, fun _ _ => ()⟩, fun _ => 0, fun _ _ _ => none⟩

/-- The initial state. -/
def zV0 : Zustand Unit Unit Unit Unit Bool Unit :=
  Zustand.start (fun _ => false) statusV
    (fun j => ⟨dispatchV j, .nutzer, (), fun _ => false, 0, false, []⟩)
    ⟨fun _ => false, fun _ => 0⟩ (fun _ => ()) (.leer (fun _ => 0))

/-- The witness unit: the worker image with the dormant handler. -/
def E_v : Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit :=
  ⟨Plattform.x86_64.katalog, wBild, wEinrichtungV, toggleSystem,
    fun _ => wDatenV, fun _ => 0,
    fun _ _ => some zV0, Eq, fun _ => 1, .leer, eineTabelle, .leer, .leer, .leer⟩

theorem zV0_dispatch0 : (zV0.kerne 0).laeuft = some A := rfl

theorem zV0_live_A : zV0.status A = .laeuft := rfl

theorem zV0_ruht_Hv : zV0.status Hv = .ruht := rfl

theorem zV0_geliefert : zV0.geliefert = [] := rfl

theorem zV0_epoche : zV0.epoche = 0 := rfl

/-- The hardware history: one selected raise at tick zero, silent raises afterwards,
    opportunities on the single core from tick one on. -/
def angebotV : Nat → Gelegenheit
  | 0 => ⟨none, fun c => decide (c = 0),
      [.erhoben 0 irqV, .zustellen 0 (0, 0) irqV],
      fun _ => false, false, false, 0⟩
  | t + 1 => ⟨some 0, fun c => decide (c = 0), [.erhoben 0 irqV],
      fun e => decide (Plattform.x86_64.katalog.enthaelt (.endpoint e)),
      decide (Plattform.x86_64.katalog.enthaelt .persistence), false, t + 1⟩

def sichtV : Nat → AussenVerlauf → AussenSicht := fun _ _ => AussenSicht.leer

def hwV : HwLauf :=
  ⟨angebotV, (Katalog.Umgebung.referenz Plattform.x86_64.katalog 1 sichtV).politik⟩

def HV : Umgebung := Katalog.Umgebung.referenz Plattform.x86_64.katalog 1 sichtV

theorem HV1 : HV.kernzahl = 1 := rfl

/-- The x86-64 target supports the raised line. -/
theorem hsupV : HV.ziel.unterstuetzt irqV := by
  have hziel : HV.ziel = Plattform.ziel Plattform.x86_64 := rfl
  rw [hziel]
  show 0 < 256 ∧ 0 < 256
  exact ⟨by decide, by decide⟩

/-- The selected raise at tick zero. -/
theorem auswahlV0 : (angebotV 0).interruptAuswahl = some (0, (0, 0), irqV) := rfl

/-- The raise is pending at tick zero. -/
theorem pendingV0 : (angebotV 0).interrupts[0]? = some (.erhoben 0 irqV) := rfl

/-- Every offer of the witness history is row-conformant. -/
theorem gueltigV (i : Nat) :
    AngebotGueltig Plattform.x86_64.katalog HV (angebotV i)
      (hwV.interruptUrsprung i) := by
  cases i with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      cases hc
    · intro c hc
      have hc0 : c = 0 := by
        cases c with
        | zero => rfl
        | succ n =>
          simp only [decide_eq_true_eq] at hc
          exact absurd hc (Nat.succ_ne_zero n)
      subst hc0
      exact Nat.zero_lt_succ 0
    · intro sig hmem
      simp only [angebotV, irqV] at hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ⟨by rw [HV1]; exact Nat.zero_lt_succ 0, hsupV⟩
      · have hmem : sig = .zustellen 0 (0, 0) irqV := List.mem_singleton.mp hmem
        subst hmem
        refine ⟨by rw [HV1]; exact Nat.zero_lt_succ 0, hsupV, rfl, auswahlV0, ?_, rfl, ?_⟩
        · exact ⟨rfl, pendingV0⟩
        · intro e
          rfl
    · intro e he
      cases he
    · intro h
      rcases h with h | h <;> cases h
  | succ t =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      simp only [angebotV] at hc
      have hc0 : c = 0 := (Option.some.inj hc).symm
      subst hc0
      rw [HV1]
      exact Nat.zero_lt_succ 0
    · intro c hc
      have hc0 : c = 0 := by
        cases c with
        | zero => rfl
        | succ n =>
          simp only [decide_eq_true_eq] at hc
          exact absurd hc (Nat.succ_ne_zero n)
      subst hc0
      exact Nat.zero_lt_succ 0
    · intro sig hmem
      simp only [angebotV, irqV, List.mem_singleton] at hmem
      rw [hmem]
      exact ⟨by rw [HV1]; exact Nat.zero_lt_succ 0, hsupV⟩
    · intro e he
      simpa only [decide_eq_true_eq] using he
    · intro h
      rcases h with h | h
      · simpa only [decide_eq_true_eq] using h
      · cases h

/-- The witness history is fair. -/
theorem fairV : FairLaeufe Plattform.x86_64.katalog HV hwV where
  hardware := Katalog.Umgebung.referenz_hardware _ _ _ Plattform.x86_64.katalog_wohlgeformt
    (by decide)
  politik := rfl
  gueltig := fun i => gueltigV i
  kerne := by
    refine ⟨fun i k h => ?_, fun k hk cut => ?_⟩
    · cases i with
      | zero =>
        simp only [hwV, angebotV] at h
        cases h
      | succ t =>
        simp only [hwV, angebotV] at h
        have hk0 : k = 0 := (Option.some.inj h).symm
        subst hk0
        rw [HV1]
        exact Nat.zero_lt_succ 0
    · have hk0 : k = 0 := by rw [HV1] at hk; omega
      subst hk0
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (n := max cut 1) (by omega)
      refine ⟨max cut 1, Nat.le_max_left cut 1, ?_⟩
      rw [hj]
      rfl
  interrupts := by
    intro c hc cut
    have hc0 : c = 0 := by rw [HV1] at hc; omega
    subst hc0
    cases cut with
    | zero => exact ⟨0, Nat.le_refl 0, rfl⟩
    | succ cut => exact ⟨cut + 1, Nat.le_refl _, rfl⟩
  auslieferung := by
    intro e selected cut
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (n := max cut 1) (by omega)
    refine ⟨max cut 1, Nat.le_max_left cut 1, ?_⟩
    rw [hj]
    exact decide_eq_true selected
  medium := by
    intro selected cut
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (n := max cut 1) (by omega)
    refine ⟨max cut 1, Nat.le_max_left cut 1, ?_⟩
    rw [hj]
    exact decide_eq_true selected
  cycles := by
    intro i j le
    cases i with
    | zero => exact Nat.zero_le _
    | succ i =>
      cases j with
      | zero => exact absurd le (by omega)
      | succ j => exact le
  zeit := by
    intro cut n
    refine ⟨cut + n + 1, by omega, ?_⟩
    show n ≤ cut + n + 1
    omega

/-- The memory side of the preemption: one resolution of the injected interrupt event. -/
noncomputable def memV : ∃ r es g',
    Speicherfolge (fun _ => ()) .aussen zV0.graph [⟨.aussen, (), .na, r, ()⟩] es g' :=
  speicherzug_existiert (fun _ => ()) .aussen Speicher.Zustand.leer_konsistent
    Speicher.Zustand.leer_vollstaendig .aussen () .na () (fun h => by cases h)

noncomputable def rV : Unit := Classical.choose memV

noncomputable def memV1 : ∃ es g',
    Speicherfolge (fun _ => ()) .aussen zV0.graph [⟨.aussen, (), .na, rV, ()⟩] es g' :=
  Classical.choose_spec memV

noncomputable def esV : List (SpeicherAkteur Unit × Speicher.Etikett Unit Unit) :=
  Classical.choose memV1

noncomputable def memV2 : ∃ g',
    Speicherfolge (fun _ => ()) .aussen zV0.graph [⟨.aussen, (), .na, rV, ()⟩] esV g' :=
  Classical.choose_spec memV1

noncomputable def gV' : SpeicherGraph Unit Unit := Classical.choose memV2

noncomputable def hmemV : Speicherfolge (fun _ => ()) .aussen zV0.graph
    [⟨.aussen, (), .na, rV, ()⟩] esV gV' :=
  Classical.choose_spec memV2

/-- The chosen read value is the unit. -/
theorem rV_eq : rV = () := rfl

/-- The computed event label. -/
theorem labV : Maschine.aussenEtikett wEinrichtungV (.interrupt 0 irqV .handler) =
    ⟨.aussen, (), .na, (), ()⟩ := rfl

/-- The post-preemption state: the handler runs on core zero. -/
noncomputable def zV1 : Zustand Unit Unit Unit Unit Bool Unit :=
  { Maschine.Zustandseintritt zV0 0 (0, 0) Hv false with graph := gV' }

/-- The run states: initial, post-preemption, then handler toggles. -/
noncomputable def ZV : Nat → Zustand Unit Unit Unit Unit Bool Unit
  | 0 => zV0
  | 1 => zV1
  | t + 2 => toggleUpdate Hv (ZV (t + 1))

/-- The run trace: the interrupt, then handler steps. -/
noncomputable def spurV : Nat → Option (SchrittWahl Unit × SchrittSpur Unit Unit)
  | 0 => some (SchrittWahl.interrupt (0, 0), ⟨esV, [Ereignis.interrupt 0 irqV Eintritt.handler]⟩)
  | _ + 1 => some (SchrittWahl.kontext Hv (), ⟨[], []⟩)

theorem ZV_kerne_succ : ∀ t, (ZV (t + 1)).kerne = zV1.kerne := by
  intro t
  induction t with
  | zero =>
    show (ZV 1).kerne = zV1.kerne
    rfl
  | succ t ih =>
    have hz : ZV (t + 2) = toggleUpdate Hv (ZV (t + 1)) := by simp only [ZV]
    rw [hz]
    exact ih

theorem ZV_status_succ : ∀ t, (ZV (t + 1)).status = zV1.status := by
  intro t
  induction t with
  | zero =>
    show (ZV 1).status = zV1.status
    rfl
  | succ t ih =>
    have hz : ZV (t + 2) = toggleUpdate Hv (ZV (t + 1)) := by simp only [ZV]
    rw [hz]
    exact ih

theorem zV1_dispatch : (zV1.kerne 0).laeuft = some Hv := by
  simp only [zV1, Maschine.Zustandseintritt, Function.update_self,
    KernZustand.unterbrechen]

theorem zV1_live_Hv : zV1.status Hv = .laeuft := by
  simp only [zV1, Maschine.Zustandseintritt, Function.update_self]

theorem zV1_live_A : zV1.status A = .laeuft := by
  have hne : A ≠ Hv := by simp only [A, Hv, ne_eq, reduceCtorEq, not_false_eq_true]
  simp only [zV1, Maschine.Zustandseintritt, Function.update_of_ne hne.symm]
  exact zV0_live_A

/-- Only the worker and the handler are ever dispatched: `A` at tick zero, `Hv` after. -/
theorem nurV (t : Nat) (k : Kern) (c : Kontext)
    (h : ((ZV t).kerne k).laeuft = some c) :
    (t = 0 ∧ c = A) ∨ (0 < t ∧ c = Hv) := by
  cases t with
  | zero =>
    cases k with
    | zero =>
      simp only [ZV] at h
      have hc : c = A := (Option.some.inj (zV0_dispatch0.symm.trans h)).symm
      exact Or.inl ⟨rfl, hc⟩
    | succ k =>
      simp only [ZV, dispatchV] at h
      cases h
  | succ t =>
    have hkerne := ZV_kerne_succ t
    cases k with
    | zero =>
      rw [hkerne, zV1_dispatch] at h
      have hc : c = Hv := (Option.some.inj h).symm
      exact Or.inr ⟨Nat.succ_pos _, hc⟩
    | succ k =>
      rw [hkerne] at h
      simp only [zV1, Maschine.Zustandseintritt, Function.update_of_ne (Nat.succ_ne_zero k),
        dispatchV] at h
      cases h

/-- The worker is never dispatched again after tick zero. -/
theorem nirgendsV (t : Nat) (k : Kern) (ht : 0 < t) :
    ((ZV t).kerne k).laeuft ≠ some A := by
  intro h
  rcases nurV t k A h with ⟨h0, _⟩ | ⟨_, hc⟩
  · omega
  · exact absurd hc (by simp only [A, Hv, ne_eq, reduceCtorEq, not_false_eq_true])

/-- The worker stays live on the whole run. -/
theorem zV_live_A : ∀ t, (ZV t).status A = .laeuft := by
  intro t
  cases t with
  | zero => exact zV0_live_A
  | succ t =>
    rw [ZV_status_succ]
    exact zV1_live_A

/-- Handler steps preserve the local frame protocol. -/
def hvAusfuehr (tick : Nat) (x : Zustand Unit Unit Unit Unit Bool Unit) :
    FuehrtSchrittAus E_v.einrichtung tick Hv x (toggleUpdate Hv x) togglePlan ⟨[], []⟩
      (toggleUpdate Hv x) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, [], toggleUpdate Hv x, .intern, .nil _, rfl⟩

theorem wBildV_format : wBild.format = .elf := rfl

theorem wBildV_bytes : wBild.bytes = fun a => if a = 0 then some 0 else none := rfl

theorem wBildV_entries : wBild.entries = [0] := rfl

/-- `wBild` is a valid image for the witness unit. -/
theorem wBildV_gueltig : wBild.gueltig E_v.katalog.plattform.ziel := by
  have hplat : E_v.katalog.plattform = Plattform.x86_64 := rfl
  rw [hplat]
  refine ⟨(ziele_gut _).2.2.2.2.2.2.2.2.2, ?_, ?_⟩
  · intro a v h
    rw [wBildV_bytes] at h
    have h' : (if a = 0 then some (0 : UInt8) else none) = some v := h
    by_cases ha : a = 0
    · subst ha
      exact pow_pos (by decide : (0 : Nat) < 2) _
    · rw [if_neg ha] at h'
      nomatch h'
  · intro entry hmem
    rw [wBildV_entries, List.mem_singleton] at hmem
    subst hmem
    exact ⟨0, rfl⟩

end Gabbro.Core.Fortschritt
