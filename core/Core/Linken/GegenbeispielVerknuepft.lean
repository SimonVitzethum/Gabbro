module

public import Core.Linken.Gegenbeispiel
public import Core.Annahme.Annahme
public import Core.Ast.LowLevel.Proofs.EnvironmentSatisfiability
public import Core.Ast.Semantik.Runtime.Mehrkontext.Kopf

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

/-- The linked unit of the witness plan. -/
def E_linked : Ast.Semantik.Einheit :=
  (verknuepfteFragmente planAB).einheit .x86_64

/-- The hardware offer for the witness run: core `k` always runs, nothing else happens. -/
def hwAngebot (k : Nat) : Gelegenheit :=
  ⟨some k, fun _ => false, [], fun _ => false, false, false, 0⟩

/-- The hardware history for the witness run. -/
def hwLinked (h : Umgebung) (k : Nat) : HwLauf :=
  ⟨fun _ => hwAngebot k, h.politik⟩

/-- A status away from the entry context stays at rest. -/
theorem nach_status (b : Befehl) (c : Kontext) (s : Zustand) :
    (b.nach c s).status = s.status :=
  rfl

/-- The boot status at the entry context. -/
theorem boot_status_entry (s : AussenStart) :
    ((I.start E_linked s).2).status eintritt = .laeuft :=
  rfl

/-- The boot status away from the entry context. -/
theorem boot_status_other (s : AussenStart) (c : Kontext) (hne : c ≠ eintritt) :
    ((I.start E_linked s).2).status c = .ruht := by
  show (if c = eintritt then Status.laeuft else Status.ruht) = .ruht
  rw [if_neg hne]

/-- The boot dispatch runs the entry context on its assigned core. -/
theorem boot_dispatch (s : AussenStart) (k : Nat) (assigned : s.assignment 0 = some k) :
    (((I.start E_linked s).2).kerne k).laeuft = some eintritt := by
  show (if some k = s.assignment 0 then some eintritt else none) = some eintritt
  rw [assigned]
  exact if_pos rfl

/-- A head at rest is absent. -/
theorem kopf_ruht {s : Zustand} {c : Kontext}
    (h : s.status c = .ruht) : kopf (verknuepfteFragmente planAB).code s c = none := by
  simp only [kopf, h]

/-- The system head is the code head. -/
theorem system_kopf (s : Zustand) (c : Kontext) :
    E_linked.system.kopf s c = kopf (verknuepfteFragmente planAB).code s c := by
  rfl

/-- Liveness ignores the recorded graph. -/
theorem regionLive_graph_irrelevant (s : Zustand) (g : _) :
    Zustand.regionLive { s with graph := g } = Zustand.regionLive s := by
  rfl

/-- No context steps at a resting head. -/
theorem keinSchritt_ruht {c : Kontext} {s : Zustand} {w : PUnit.{1}} {plans : List Plan}
    {u : Zustand} (h : s.status c = .ruht) (step : E_linked.system.ISchritt c s w plans u) :
    False := by
  obtain ⟨b, head, _⟩ := step
  rw [system_kopf, kopf_ruht h] at head
  cases head

/-- The witness hardware is conformant. -/
theorem konformHw (h : Umgebung) (s : AussenStart) (zul : E_linked.ZulStart h s)
    (k : Nat) (assigned : s.assignment 0 = some k) :
    (hwLinked h k).konform E_linked.katalog h := by
  unfold HwLauf.konform
  refine ⟨rfl, fun i => ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro core hc
    cases hc
    exact (zul.2.2.2.1 0 k assigned).2
  · intro core hc
    cases hc
  · intro signal mem
    exact (List.not_mem_nil mem).elim
  · intro e hd
    cases hd
  · intro hmed
    rcases hmed with hmed | hcrash
    · cases hmed
    · cases hcrash

/-- The six prefix states of the witness run. -/
def sLinked (s : AussenStart) : Zustand :=
  (I.start E_linked s).2

def sLinked1 (s : AussenStart) : Zustand :=
  (Befehl.literal 0 10).nach eintritt (sLinked s)

def sLinked2 (s : AussenStart) : Zustand :=
  (Befehl.literal 1 2).nach eintritt (sLinked1 s)

def sLinked3 (s : AussenStart) : Zustand :=
  (Befehl.teilen 0).nach eintritt (sLinked2 s)

def sLinked4 (s : AussenStart) : Zustand :=
  (Befehl.literal 0 5).nach eintritt (sLinked3 s)

def sLinked5 (s : AussenStart) : Zustand :=
  (Befehl.literal 1 0).nach eintritt (sLinked4 s)

def sLinked6 (s : AussenStart) : Zustand :=
  (Befehl.zurueckSprung 3).nach eintritt (sLinked5 s)

/-- Forcing one ideal step: from local, status and core agreement with a concrete
    pre-state, the run takes the forced step and agrees with the concrete post-state. -/
theorem forceStep (ρ : I.Lauf E_linked) (hρ : I.Laeufe E_linked ρ)
    (t : Nat) (k : Nat) (b : Befehl) (sPre : Zustand)
    (hNoCrash : (ρ.hw.angebot t).crash = false)
    (hCore : (ρ.hw.angebot t).core = some k)
    (hNoInt : (ρ.hw.angebot t).interrupt = fun _ => false)
    (hNoInts : ∀ i, (ρ.hw.angebot i).interrupts = [])
    (hNoDel : (ρ.hw.angebot t).delivery = fun _ => false)
    (hFrei : ρ.belegt t = none)
    (hEqL : (ρ.zeit.zustand t).lokal = sPre.lokal)
    (hEqS : (ρ.zeit.zustand t).status = sPre.status)
    (hEqK : (ρ.zeit.zustand t).kerne = sPre.kerne)
    (hEqF : (ρ.zeit.zustand t).fragen = sPre.fragen)
    (hEqR : Zustand.regionLive (ρ.zeit.zustand t) = Zustand.regionLive sPre)
    (hHead : kopf (verknuepfteFragmente planAB).code sPre eintritt = some b)
    (hPriv : b.klasse = .lokal ∨ b.klasse = .ruf)
    (hReady : KannSchreiten ρ.hw t eintritt sPre)
    (hStPre : ∀ c, c ≠ eintritt → sPre.status c = .ruht)
    (hFrPre : sPre.fragen = []) :
    (∃ ev, ρ.zeit.spur t = some ev) ∧
      (ρ.zeit.zustand (t + 1)).lokal = (b.nach eintritt sPre).lokal ∧
      (ρ.zeit.zustand (t + 1)).status = (b.nach eintritt sPre).status ∧
      (ρ.zeit.zustand (t + 1)).kerne = (b.nach eintritt sPre).kerne ∧
      (ρ.zeit.zustand (t + 1)).fragen = [] ∧
      Zustand.regionLive (ρ.zeit.zustand (t + 1)) = Zustand.regionLive (b.nach eintritt sPre) := by
  have hReadyT : KannSchreiten ρ.hw t eintritt (ρ.zeit.zustand t) := by
    obtain ⟨kk, hg, hd, hs⟩ := hReady
    refine ⟨kk, hg, ?_, ?_⟩
    · rw [hEqK]
      exact hd
    · rw [hEqS]
      exact hs
  have headT : kopf (verknuepfteFragmente planAB).code (ρ.zeit.zustand t) eintritt = some b := by
    simp only [kopf, hEqS, hEqL]
    exact hHead
  have stepT : I.Schritt E_linked.einrichtung E_linked.system E_linked.katalog ρ.hw t
      (ρ.zeit.zustand t) (.kontext eintritt (), ⟨[], []⟩)
      (b.maschinennach eintritt (ρ.zeit.zustand t) (b.nach eintritt (ρ.zeit.zustand t))) :=
    .kontext hNoCrash hReadyT
      ⟨b, headT, (b.ideal_privat (hPriv.elim Or.inl (Or.inr ∘ Or.inl)) eintritt (ρ.zeit.zustand t) () [_] _).2 ⟨rfl, rfl⟩⟩
      (b.vollzug E_linked.einrichtung _ _ _ (hPriv.elim Or.inl (Or.inr ∘ Or.inl)))
  have hsome : ∃ ev, ρ.zeit.spur t = some ev := by
    cases hsp : ρ.zeit.spur t with
    | none =>
      exfalso
      obtain ⟨maxA, _⟩ := (hρ.2.2.2.2).1
      exact (maxA t hsp hFrei _ _ stepT).elim
    | some ev => exact ⟨ev, rfl⟩
  obtain ⟨ev, hev⟩ := hsome
  have htakt := ρ.zeit.takt t
  rw [hev] at htakt
  cases htakt with
  | schritt label step =>
    cases step with
    | kontext _ bereit regel aus =>
      rename_i u0 plan0 spur0 c0 w0 kab0
      by_cases heq : c0 = eintritt
      · subst heq
        obtain ⟨b', head', ideal'⟩ := regel
        have hb' : b' = b := by
          rw [system_kopf, headT] at head'
          cases head'
          rfl
        subst b'
        obtain ⟨same, after⟩ :=
          (b.ideal_privat (hPriv.elim Or.inl (Or.inr ∘ Or.inl)) eintritt (ρ.zeit.zustand t) w0 [plan0] u0).1 ideal'
        cases same
        cases after
        obtain ⟨rahmen, _, sperren, v, fuehrt, _, hstate⟩ := aus
        rcases b.plan_privat_aktion (hPriv.elim Or.inl (Or.inr ∘ Or.inl)) ((ρ.zeit.zustand t).lokal eintritt) with hL|⟨v1,a1,hL⟩|⟨g1,hL⟩|⟨v2,k2,hL⟩|⟨l3,k3,p3,hL⟩
        · have hR : (b.plan ((ρ.zeit.zustand t).lokal eintritt) 0).aktion = .intern := hL
          rw [hR] at fuehrt
          generalize hau : spur0.2 = au at fuehrt
          cases fuehrt with
          | intern =>
          refine ⟨⟨ev, hev⟩, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hstate]
            simp only [Befehl.nach, hEqL, hEqR]
          · rw [hstate]
            simp only [Befehl.nach, hEqS]
          · rw [hstate]
            simp only [Befehl.nach, hEqK]
          · rw [hstate]
            simp only [Befehl.nach, hEqF, hFrPre]
          · rw [hstate, regionLive_graph_irrelevant, Befehl.nach_regionLive, hEqR,
              ← Befehl.nach_regionLive]
        · have hR : (b.plan ((ρ.zeit.zustand t).lokal eintritt) 0).aktion = .maskiere v1 a1 := hL
          rw [hR] at fuehrt
          generalize hau : spur0.2 = au at fuehrt
          cases fuehrt with
          | maskiere _ _ =>
          have hI : (b.plan ((ρ.zeit.zustand t).lokal eintritt) 0).aktion = .intern := by
            rcases hPriv with h|h <;> simp only [Befehl.plan, Schrittform.plan, Befehl.form, Wirkungsklasse.plan, h, Semantik.plan]
          rw [hI] at hL
          cases hL
        · have hR : (b.plan ((ρ.zeit.zustand t).lokal eintritt) 0).aktion = .prioritaet g1 := hL
          rw [hR] at fuehrt
          generalize hau : spur0.2 = au at fuehrt
          cases fuehrt with
          | prioritaet _ =>
          have hI : (b.plan ((ρ.zeit.zustand t).lokal eintritt) 0).aktion = .intern := by
            rcases hPriv with h|h <;> simp only [Befehl.plan, Schrittform.plan, Befehl.form, Wirkungsklasse.plan, h, Semantik.plan]
          rw [hI] at hL
          cases hL
        · have hR : (b.plan ((ρ.zeit.zustand t).lokal eintritt) 0).aktion = .sende v2 k2 := hL
          rw [hR] at fuehrt
          generalize hau : spur0.2 = au at fuehrt
          cases fuehrt with
          | sende _ _ =>
          have hI : (b.plan ((ρ.zeit.zustand t).lokal eintritt) 0).aktion = .intern := by
            rcases hPriv with h|h <;> simp only [Befehl.plan, Schrittform.plan, Befehl.form, Wirkungsklasse.plan, h, Semantik.plan]
          rw [hI] at hL
          cases hL
        · have hR : (b.plan ((ρ.zeit.zustand t).lokal eintritt) 0).aktion = .leite l3 k3 p3 := hL
          rw [hR] at fuehrt
          generalize hau : spur0.2 = au at fuehrt
          cases fuehrt with
          | leite _ _ _ =>
          have hI : (b.plan ((ρ.zeit.zustand t).lokal eintritt) 0).aktion = .intern := by
            rcases hPriv with h|h <;> simp only [Befehl.plan, Schrittform.plan, Befehl.form, Wirkungsklasse.plan, h, Semantik.plan]
          rw [hI] at hL
          cases hL
      · exfalso
        obtain ⟨b', head', _⟩ := regel
        have hruht : (ρ.zeit.zustand t).status c0 = .ruht := by
          rw [hEqS]
          exact hStPre c0 heq
        rw [system_kopf, kopf_ruht hruht] at head'
        cases head'
    | antwort _ reply =>
      exfalso
      obtain ⟨offered, _, _, _⟩ := reply
      obtain ⟨q, hmem, _, _⟩ := offered.2.2.2.1
      rw [hEqF, hFrPre] at hmem
      exact (List.not_mem_nil hmem).elim
    | interrupt _ enters =>
      exfalso
      obtain ⟨kk, irq, cc, nmi, _, haus, _, _, _, _, _⟩ := enters
      obtain ⟨_, _, hoffer, _, _⟩ := haus
      rw [hNoInts _] at hoffer
      cases hoffer
    | absturz crash =>
      exfalso
      have hcon := crash.1.2
      rw [hNoCrash] at hcon
      exact Bool.false_ne_true hcon
  | wartet label _ _ =>
    cases label

/-- The divisor slot at the violation cut holds zero. -/
theorem sLinked6_temp0 (s : AussenStart) :
    ((sLinked6 s).lokal eintritt).temp 0 =
      some ⟨.int ((5 : Nat) : Int) ((5 : Nat) : Int), Zahl.literal ((5 : Nat) : Int)⟩ := by
  rfl

theorem sLinked6_temp1 (s : AussenStart) :
    ((sLinked6 s).lokal eintritt).temp 1 =
      some ⟨.int ((0 : Nat) : Int) ((0 : Nat) : Int), Zahl.literal ((0 : Nat) : Int)⟩ := by
  rfl

/-- On the unsealed witness run the whole performs a division by zero: a guard use that no
    accepted part covers. The run, its cut and the failing operands are exhibited together so
    the guard transfer can be refuted independently of the other acceptance conjuncts. -/
theorem unsealed_guard_use :
    ∃ (ρ : I.Lauf E_linked) (hρ : I.Laeufe E_linked ρ) (t : I.Schnitt E_linked ρ),
      (kanonischeVerwendung E_linked).bedarf ρ t .division (5, 0) ∧
        ¬ waechterBedarf .division (5, 0) := by
  obtain ⟨h, hwF, hardwareH, fairH⟩ :=
    katalog_nichtLeer E_linked.katalog (Plattform.katalog_wohlgeformt .x86_64)
  have imageH : E_linked.bild.gueltig E_linked.katalog.plattform.ziel :=
    Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨s, zul⟩ := zulStart_erfuellbar hardwareH imageH
  obtain ⟨k, assigned⟩ := zul.2.2.1 0 (Nat.zero_lt_succ _)
  obtain ⟨zeit, init⟩ := Zeitlauf.existiert
    (I.Schritt E_linked.einrichtung E_linked.system E_linked.katalog (hwLinked h k))
    (I.start E_linked s).2
  have pauseOk : ∀ t z,
      KeinSchritt (I.Schritt E_linked.einrichtung E_linked.system E_linked.katalog (hwLinked h k)) t z →
        ¬ AbsturzAngeboten E_linked.katalog (hwLinked h k) t :=
    fun t z _ offer => Bool.false_ne_true offer.2
  let ρ : I.Lauf E_linked :=
    ⟨s, h, hwLinked h k, zeit.erlaubePausen pauseOk, fun _ => none⟩
  have hρ : I.Laeufe E_linked ρ :=
    ⟨hardwareH, konformHw h s zul k assigned, zul, init,
      zeit.erlaubePausen_maximal pauseOk _ (fun _ => rfl), fun _ _ h => nomatch h⟩
  have baseL : (ρ.zeit.zustand 0).lokal = (sLinked s).lokal := by
    have e : ρ.zeit.zustand 0 = (I.start E_linked s).2 := init
    rw [e]
    rfl
  have baseS : (ρ.zeit.zustand 0).status = (sLinked s).status := by
    have e : ρ.zeit.zustand 0 = (I.start E_linked s).2 := init
    rw [e]
    rfl
  have baseK : (ρ.zeit.zustand 0).kerne = (sLinked s).kerne := by
    have e : ρ.zeit.zustand 0 = (I.start E_linked s).2 := init
    rw [e]
    rfl
  have baseF : (ρ.zeit.zustand 0).fragen = (sLinked s).fragen := by
    have e : ρ.zeit.zustand 0 = (I.start E_linked s).2 := init
    rw [e]
    rfl
  have baseR : Zustand.regionLive (ρ.zeit.zustand 0) = Zustand.regionLive (sLinked s) := by
    have e : ρ.zeit.zustand 0 = (I.start E_linked s).2 := init
    rw [e]
    rfl
  have hwCrash : ∀ t, (ρ.hw.angebot t).crash = false := fun t => rfl
  have hwCore : ∀ t, (ρ.hw.angebot t).core = some k := fun t => rfl
  have hwInt : ∀ t, (ρ.hw.angebot t).interrupt = fun _ => false := fun t => rfl
  have hwInts : ∀ i, (ρ.hw.angebot i).interrupts = [] := fun i => rfl
  have hwDel : ∀ t, (ρ.hw.angebot t).delivery = fun _ => false := fun t => rfl
  have hwFrei : ∀ t, ρ.belegt t = none := fun t => rfl
  have hStPre : ∀ (sPre : Zustand) (c : Kontext), c ≠ eintritt →
      sPre.status = ((I.start E_linked s).2).status → sPre.status c = .ruht := by
    intro sPre c hne heq
    rw [heq]
    exact boot_status_other s c hne
  have readyAt : ∀ (sPre : Zustand) (t : Nat),
      sPre.kerne = ((I.start E_linked s).2).kerne →
      sPre.status = ((I.start E_linked s).2).status →
      KannSchreiten ρ.hw t eintritt sPre := by
    intro sPre t hK hS
    refine ⟨k, hwCore t, ?_, ?_⟩
    · rw [hK]
      exact boot_dispatch s k assigned
    · rw [hS]
      exact boot_status_entry s
  have st0 := forceStep ρ hρ 0 k (.literal 0 10) (sLinked s)
    (hwCrash 0) (hwCore 0) (hwInt 0) hwInts (hwDel 0) (hwFrei 0)
    baseL baseS baseK baseF baseR
    (by rfl) (by first | exact Or.inl rfl | exact Or.inr rfl) (readyAt _ _ rfl rfl)
    (fun c hne => hStPre _ c hne rfl) (by rfl)
  have st1 := forceStep ρ hρ 1 k (.literal 1 2) (sLinked1 s)
    (hwCrash 1) (hwCore 1) (hwInt 1) hwInts (hwDel 1) (hwFrei 1)
    st0.2.1 st0.2.2.1 st0.2.2.2.1 st0.2.2.2.2.1 st0.2.2.2.2.2
    (by rfl) (by first | exact Or.inl rfl | exact Or.inr rfl) (readyAt _ _ rfl rfl)
    (fun c hne => hStPre _ c hne rfl) (by rfl)
  have st2 := forceStep ρ hρ 2 k (.teilen 0) (sLinked2 s)
    (hwCrash 2) (hwCore 2) (hwInt 2) hwInts (hwDel 2) (hwFrei 2)
    st1.2.1 st1.2.2.1 st1.2.2.2.1 st1.2.2.2.2.1 st1.2.2.2.2.2
    (by rfl) (by first | exact Or.inl rfl | exact Or.inr rfl) (readyAt _ _ rfl rfl)
    (fun c hne => hStPre _ c hne rfl) (by rfl)
  have st3 := forceStep ρ hρ 3 k (.literal 0 5) (sLinked3 s)
    (hwCrash 3) (hwCore 3) (hwInt 3) hwInts (hwDel 3) (hwFrei 3)
    st2.2.1 st2.2.2.1 st2.2.2.2.1 st2.2.2.2.2.1 st2.2.2.2.2.2
    (by rfl) (by first | exact Or.inl rfl | exact Or.inr rfl) (readyAt _ _ rfl rfl)
    (fun c hne => hStPre _ c hne rfl) (by rfl)
  have st4 := forceStep ρ hρ 4 k (.literal 1 0) (sLinked4 s)
    (hwCrash 4) (hwCore 4) (hwInt 4) hwInts (hwDel 4) (hwFrei 4)
    st3.2.1 st3.2.2.1 st3.2.2.2.1 st3.2.2.2.2.1 st3.2.2.2.2.2
    (by rfl) (by first | exact Or.inl rfl | exact Or.inr rfl) (readyAt _ _ rfl rfl)
    (fun c hne => hStPre _ c hne rfl) (by rfl)
  have st5 := forceStep ρ hρ 5 k (.zurueckSprung 3) (sLinked5 s)
    (hwCrash 5) (hwCore 5) (hwInt 5) hwInts (hwDel 5) (hwFrei 5)
    st4.2.1 st4.2.2.1 st4.2.2.2.1 st4.2.2.2.2.1 st4.2.2.2.2.2
    (by rfl) (by first | exact Or.inl rfl | exact Or.inr rfl) (readyAt _ _ rfl rfl)
    (fun c hne => hStPre _ c hne rfl) (by rfl)
  have hspur5 : ∃ ev, ρ.zeit.spur 5 = some ev := st5.1
  obtain ⟨ev5, hspur5⟩ := hspur5
  have hEqL6 : (ρ.zeit.zustand 6).lokal = (sLinked6 s).lokal := st5.2.1
  have hEqS6 : (ρ.zeit.zustand 6).status = (sLinked6 s).status := st5.2.2.1
  have hEqK6 : (ρ.zeit.zustand 6).kerne = (sLinked6 s).kerne := st5.2.2.2.1
  have hEqF6 : (ρ.zeit.zustand 6).fragen = (sLinked6 s).fragen := st5.2.2.2.2.1
  have hEqR6 : Zustand.regionLive (ρ.zeit.zustand 6) =
      Zustand.regionLive (sLinked6 s) := st5.2.2.2.2.2
  have hHead6 : kopf (verknuepfteFragmente planAB).code (sLinked6 s) eintritt =
      some (Befehl.teilen 0) := by
    rfl
  have head6 : kopf (verknuepfteFragmente planAB).code (ρ.zeit.zustand 6) eintritt =
      some (Befehl.teilen 0) := by
    simp only [kopf, hEqS6, hEqL6]
    exact hHead6
  have guard6 : (Befehl.teilen 0).guard ((ρ.zeit.zustand 6).lokal eintritt) =
      some ⟨.division, (5, 0)⟩ := by
    simp only [Befehl.guard, Rahmen.zahl, hEqL6, sLinked6_temp0, sLinked6_temp1,
      alsGanzzahl, Option.bind_some, Option.pure_def]
    rfl
  have need6 : (kanonischeVerwendung E_linked).bedarf ρ ⟨6, Or.inr ⟨5, ev5, rfl, hspur5⟩⟩
      .division (5, 0) :=
    ⟨eintritt, .teilen 0, head6, guard6⟩
  refine ⟨ρ, hρ, ⟨6, Or.inr ⟨5, ev5, rfl, hspur5⟩⟩, need6, ?_⟩
  intro hbad
  simp only [waechterBedarf] at hbad
  exact hbad rfl

/-- The linked unit is not accepted: the witness run divides by zero. -/
theorem linked_nicht_akzeptiert : ¬ Akzeptiert E_linked := by
  obtain ⟨ρ, hρ, t, need, hbad⟩ := unsealed_guard_use
  intro ha
  exact hbad (ha.2.2.1 ρ hρ t .division (5, 0) need)

/-- The guard-conjunct transfer fails without the seal: both parts of the witness are accepted,
    yet the whole has a guard use at `(5, 0)` that no covering part run can discharge — any such
    cover would force the pinned division guard through the accepting part. The control-flow
    seal is therefore a necessary premise of the transfer. -/
theorem unsealed_guard_transfer_refuted :
    ¬ (∀ (ρ : I.Lauf E_linked) (hρ : I.Laeufe E_linked ρ) (t : I.Schnitt E_linked ρ)
        (op : PartielleOperation) (args : Operanden op),
        (kanonischeVerwendung E_linked).bedarf ρ t op args →
        ∃ m, m ∈ planAB.module ∧
        ∃ (ρm : I.Lauf (m.fragment.einheit planAB.plattform))
          (hm : I.Laeufe (m.fragment.einheit planAB.plattform) ρm) (tm : I.Schnitt _ ρm),
          (kanonischeVerwendung (m.fragment.einheit planAB.plattform)).bedarf ρm tm op args) := by
  intro hcover
  obtain ⟨ρ, hρ, t, need, hbad⟩ := unsealed_guard_use
  obtain ⟨m, hm, ρm, hρm, tm, needm⟩ := hcover ρ hρ t .division (5, 0) need
  have hmacc : Akzeptiert (m.fragment.einheit planAB.plattform) := by
    simp only [planAB, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact fragA_akzeptiert
    · exact fragB_akzeptiert
  exact hbad (hmacc.2.2.1 ρm hρm tm .division (5, 0) needm)

/-- The sealed linker refuses the witness plan although both parts are accepted:
    unsealed linking is unsound (the linked fragment divides by zero), sealed
    linking refuses. -/
theorem sealedLinkerRefusesWitness : linke planAB = none ∧
    (∀ m ∈ planAB.module, Akzeptiert (m.fragment.einheit planAB.plattform)) := by
  refine ⟨planAB_linke_none, ?_⟩
  intro m hm
  simp only [planAB, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact fragA_akzeptiert
  · exact fragB_akzeptiert

end Gabbro.Core.Linken
