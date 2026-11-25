module

public import Core.Linken.Modul
public import Core.Annahme.Annahme
public import Core.Ast.LowLevel.Proofs.EnvironmentSatisfiability

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

/-- A fragment from a plain instruction list: no clauses, empty scope, no entries, no memory. -/
def codeFrag (code : List Befehl) : Fragment :=
  ⟨code, .leer, [], fun _ => none, .leer⟩

theorem codeFrag_code (code : List Befehl) : (codeFrag code).code = code :=
  rfl

theorem codeFrag_klauseln (code : List Befehl) : (codeFrag code).klauseln = .leer :=
  rfl

/-- Part A: straight-line code dividing 10 by 2. -/
def fragA : Fragment :=
  codeFrag [.literal 0 10, .literal 1 2, .teilen 0]

/-- Part B: straight-line code with a back jump to its own start. -/
def fragB : Fragment :=
  codeFrag [.literal 0 5, .literal 1 0, .zurueckSprung 3]

theorem fragA_code : fragA.code = [.literal 0 10, .literal 1 2, .teilen 0] :=
  rfl

theorem fragB_code : fragB.code = [.literal 0 5, .literal 1 0, .zurueckSprung 3] :=
  rfl

/-- The two modules carry no interface: the point is control flow, not calls. -/
def modulA : Modul :=
  { name := "a", fragment := fragA, exporte := [], importe := [] }

def modulB : Modul :=
  { name := "b", fragment := fragB, exporte := [], importe := [] }

/-- The witness plan: A linked before B, entry at A. -/
def planAB : Bauplan :=
  { module := [modulA, modulB], abhaengigkeiten := [], plattform := .x86_64, einstieg := "a" }

/-- The current link check accepts the witness plan. -/
theorem planAB_ok : bauplanOk planAB = true := by
  decide

/-- The linked code is the concatenation: the divider runs with B's divisor. -/
theorem planAB_code : (verknuepfteFragmente planAB).code =
    [.literal 0 10, .literal 1 2, .teilen 0, .literal 0 5, .literal 1 0, .zurueckSprung 3] := by
  rfl

/-- Linking the witness plan succeeds under the current check. -/
theorem planAB_linke : linke planAB = some (verknuepfteFragmente planAB) := by
  unfold linke
  rw [if_pos planAB_ok]

/-- Every instruction of B is guard-free. -/
theorem fragB_guard (b : Befehl) (present : b ∈ fragB.code) (frame : Rahmen) :
    b.guard frame = none := by
  rw [fragB_code] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl <;> rfl

/-- Part B alone is accepted: guard-free with empty clauses. -/
theorem fragB_akzeptiert : Akzeptiert (fragB.einheit .x86_64) :=
  Fragment.akzeptiert_ohne_bedarf fragB _ (codeFrag_klauseln _) (fun b present frame => fragB_guard b present frame)

/-- The exact value `literal 1 2` writes to its slot. -/
def zweiWert : Dynamisch :=
  ⟨.int ((2 : Nat) : Int) ((2 : Nat) : Int), Zahl.literal ((2 : Nat) : Int)⟩

/-- Slot 1 only ever holds nothing or the literal 2. -/
def temp1Sauber (frame : Rahmen) : Prop :=
  frame.temp 1 = none ∨ frame.temp 1 = some zweiWert

/-- A `teilen` guard use determines its dividend, its divisor and the operands. -/
theorem teilen_guard_form {l : Nat} {frame : Rahmen} {p : (op : PartielleOperation) × Operanden op}
    (h : (Befehl.teilen l).guard frame = some p) :
    ∃ a b, frame.zahl l = some a ∧ frame.zahl (l + 1) = some b ∧
      p = ⟨.division, (a.zahl.wert.natAbs, b.zahl.wert.natAbs)⟩ := by
  simp only [Befehl.guard] at h
  cases hz : frame.zahl l with
  | none =>
    simp only [hz, Option.bind_eq_bind, Option.bind_none] at h
    cases h
  | some a =>
    simp only [hz, Option.bind_eq_bind, Option.bind_some] at h
    cases hz2 : frame.zahl (l + 1) with
    | none =>
      simp only [hz2, Option.bind_eq_bind, Option.bind_none] at h
      cases h
    | some b =>
      simp only [hz2, Option.bind_eq_bind, Option.bind_some] at h
      simp only [Option.pure_def, Option.some.injEq] at h
      exact ⟨a, b, rfl, rfl, h.symm⟩

/-- Every instruction of A preserves a clean slot 1 at the acting context. -/
theorem nach_temp1 {b : Befehl} {c : Kontext} {s : Zustand}
    (hb : b ∈ fragA.code) (h : temp1Sauber (s.lokal c)) :
    temp1Sauber ((b.nach c s).lokal c) := by
  rw [fragA_code] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · simp only [Befehl.nach, Befehl.auswerten, Rahmen.schreibe, Function.update_self,
      temp1Sauber]
    rw [Function.update_of_ne (by decide : (1 : Nat) ≠ 0)]
    exact h
  · simp only [Befehl.nach, Befehl.auswerten, Rahmen.schreibe, Function.update_self,
      temp1Sauber]
    exact Or.inr rfl
  · simp only [Befehl.nach, Befehl.auswerten, Rahmen.schreibe, Function.update_self,
      temp1Sauber]
    rw [Function.update_of_ne (by decide : (1 : Nat) ≠ 0)]
    exact h

/-- A step of A preserves a clean slot 1 in every context. -/
theorem schritt_temp1 {c : Kontext} {s u : Zustand} {w : PUnit.{1}}
    {plans : List Plan} (h : ∀ d, temp1Sauber (s.lokal d))
    (step : (fragA.einheit .x86_64).system.ISchritt c s w plans u) :
    ∀ d, temp1Sauber (u.lokal d) := by
  obtain ⟨b, head, ideal⟩ := step
  obtain ⟨same, after⟩ := (b.ideal_privat c s w plans u).1 ideal
  subst after
  have hpc : fragA.code[(s.lokal c).pc]? = some b := kopf_code head
  have hlen : (s.lokal c).pc < 3 := by
    by_contra hle
    push_neg at hle
    have h3 : fragA.code.length = 3 := rfl
    have hnone : fragA.code[(s.lokal c).pc]? = none :=
      List.getElem?_eq_none (by omega)
    rw [hnone] at hpc
    cases hpc
  revert hpc hlen
  generalize (s.lokal c).pc = pc
  intro hpc hlen
  match hmpc : pc with
  | 0 =>
    have h0 : fragA.code[0]? = some (Befehl.literal 0 10) := rfl
    rw [hpc] at h0
    cases h0
    intro d
    by_cases heq : d = c
    · subst heq
      exact nach_temp1 (by simp [fragA_code]) (h _)
    · have hkeep : ((Befehl.literal 0 10).nach c s).lokal d = s.lokal d :=
        Function.update_of_ne heq _ _
      rw [hkeep]
      exact h d
  | 1 =>
    have h1 : fragA.code[1]? = some (Befehl.literal 1 2) := rfl
    rw [hpc] at h1
    cases h1
    intro d
    by_cases heq : d = c
    · subst heq
      exact nach_temp1 (by simp [fragA_code]) (h _)
    · have hkeep : ((Befehl.literal 1 2).nach c s).lokal d = s.lokal d :=
        Function.update_of_ne heq _ _
      rw [hkeep]
      exact h d
  | 2 =>
    have h2 : fragA.code[2]? = some (Befehl.teilen 0) := rfl
    rw [hpc] at h2
    cases h2
    intro d
    by_cases heq : d = c
    · subst heq
      exact nach_temp1 (by simp [fragA_code]) (h _)
    · have hkeep : ((Befehl.teilen 0).nach c s).lokal d = s.lokal d :=
        Function.update_of_ne heq _ _
      rw [hkeep]
      exact h d
  | n + 3 => omega
/-- Slot 1 is clean in every start frame of A. -/
theorem start_temp1 (s : AussenStart) (c : Kontext) :
    temp1Sauber ((((fragA.einheit .x86_64).startdaten s).lokal c)) := by
  exact Or.inl rfl

/-- Slot 1 stays clean along any ideal run of A: only `literal 1 2` writes it,
    interrupts and answers leave frames untouched, and a crash restarts from fresh frames. -/
theorem lauf_temp1 (ρ : I.Lauf (fragA.einheit .x86_64))
    (hρ : I.Laeufe _ ρ) (t : Nat) : ∀ c, temp1Sauber ((ρ.zeit.zustand t).lokal c) := by
  induction t with
  | zero =>
    intro c
    have h0 : ρ.zeit.zustand 0 = (I.start _ ρ.start).2 := hρ.2.2.2.1
    rw [h0]
    exact start_temp1 _ c
  | succ t ih =>
    intro c
    cases htakt : ρ.zeit.takt t with
    | schritt label step =>
      cases step with
      | kontext _ bereit regel aus =>
        rename_i u0 plan0 spur0 c0 w0 kab0
        have hall := schritt_temp1 (fun d => ih d) regel
        obtain ⟨b, head, ideal⟩ := regel
        obtain ⟨same, after⟩ :=
          (b.ideal_privat c0 (ρ.zeit.zustand t) w0 [plan0] u0).1 ideal
        cases same
        cases after
        have hakt : Semantik.plan.aktion = .intern := rfl
        obtain ⟨rahmen, _, sperren, v, fuehrt, _, hstate⟩ := aus
        rw [hakt] at fuehrt
        generalize hau : spur0.2 = au at fuehrt
        cases fuehrt with
        | intern =>
          rw [hstate]
          exact hall c
      | antwort _ reply =>
        obtain ⟨_, _, _, hstate⟩ := reply
        rw [hstate]
        exact ih c
      | interrupt _ enters =>
        obtain ⟨_, _, _, _, _, _, _, _, _, _, hstate⟩ := enters
        rw [hstate]
        exact ih c
      | absturz crash =>
        obtain ⟨_, _, p, _, hstate⟩ := crash
        rw [hstate]
        exact Or.inl rfl
    | wartet label eq hp =>
      rw [eq]
      exact ih c

/-- Every guard use on any run of A holds: at `teilen` the divisor slot is the literal 2. -/
theorem fragA_guard_hält (ρ : I.Lauf (fragA.einheit .x86_64))
    (hρ : I.Laeufe _ ρ) (t : I.Schnitt _ ρ) (op : PartielleOperation) (args : Operanden op)
    (need : (kanonischeVerwendung _).bedarf ρ t op args) : waechterBedarf op args := by
  obtain ⟨c, b, head, gdef⟩ := need
  have hpc : fragA.code[((ρ.zeit.zustand t.val).lokal c).pc]? = some b := kopf_code head
  have hmem : b ∈ fragA.code := List.mem_of_getElem? hpc
  rw [fragA_code] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · simp only [Befehl.guard] at gdef
    cases gdef
  · simp only [Befehl.guard] at gdef
    cases gdef
  · obtain ⟨a, g₂, ha, hb, hsig⟩ := teilen_guard_form gdef
    cases hsig
    have hclean := lauf_temp1 ρ hρ t.val c
    have htemp : ((ρ.zeit.zustand t.val).lokal c).temp 1 = some zweiWert := by
      have hbind : ((((ρ.zeit.zustand t.val).lokal c).temp 1).bind alsGanzzahl) = some g₂ := hb
      rcases hclean with hnone | hsome
      · rw [hnone] at hbind
        cases hbind
      · exact hsome
    have hzahl : Rahmen.zahl ((ρ.zeit.zustand t.val).lokal c) 1 =
        some ⟨((2 : Nat) : Int), ((2 : Nat) : Int), Zahl.literal ((2 : Nat) : Int)⟩ := by
      have e : ((((ρ.zeit.zustand t.val).lokal c).temp 1).bind alsGanzzahl) =
          some ⟨((2 : Nat) : Int), ((2 : Nat) : Int), Zahl.literal ((2 : Nat) : Int)⟩ := by
        rw [htemp]
        rfl
      exact e
    rw [hb] at hzahl
    cases hzahl
    show (2 : Nat) ≠ 0
    decide

/-- Part A alone is accepted: straight-line code with divisor 2. -/
theorem fragA_akzeptiert : Akzeptiert (fragA.einheit .x86_64) := by
  let E := fragA.einheit .x86_64
  have hklauseln : fragA.klauseln = .leer := codeFrag_klauseln _
  refine ⟨⟨Plattform.katalog_wohlgeformt .x86_64, fun b => b.lokal E rfl,
    ⟨Aussen.zulassung_m2 _, ?_⟩, Beobachtung.fragment_fluss_lokal fragA .x86_64, ?_⟩, ?_, ?_⟩
  · apply aussen_gueltig_aus_kontext
    intro run t s c w spur next step
    cases step with
    | kontext _ _ rule execute =>
      obtain ⟨b, _, transfer⟩ := rule
      obtain ⟨rfl, rfl⟩ := b.vollzug_genau (w := w) transfer execute
      exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
        (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩
  · exact schrankenLokal_leer rfl rfl rfl
  · intro run conforms
    change (∀ pred ∈ fragA.klauseln.voraus, _) ∧
      (∀ _ : I.Schnitt E run, ∀ pred ∈ fragA.klauseln.invariant, _) ∧
      ∀ _ : I.Schnitt E run, _ → ∀ pred ∈ fragA.klauseln.sicher, _
    rw [hklauseln]
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
      fun _ _ _ h => (List.not_mem_nil h).elim⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro run conforms t op args need
      exact fragA_guard_hält run conforms t op args need
    · intro run conforms t waiting
      obtain ⟨contexts, ⟨c, member⟩, blocked⟩ := waiting
      obtain ⟨_, impossible, _⟩ := blocked c member
      exact impossible
    · intro run conforms t l h _ hne
      exact (hne rfl).elim

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
    E_linked.system.kopf s c = kopf (verknuepfteFragmente planAB).code s c :=
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
    (hHead : kopf (verknuepfteFragmente planAB).code sPre eintritt = some b)
    (hReady : KannSchreiten ρ.hw t eintritt sPre)
    (hStPre : ∀ c, c ≠ eintritt → sPre.status c = .ruht)
    (hFrPre : sPre.fragen = []) :
    (∃ ev, ρ.zeit.spur t = some ev) ∧
      (ρ.zeit.zustand (t + 1)).lokal = (b.nach eintritt sPre).lokal ∧
      (ρ.zeit.zustand (t + 1)).status = (b.nach eintritt sPre).status ∧
      (ρ.zeit.zustand (t + 1)).kerne = (b.nach eintritt sPre).kerne ∧
      (ρ.zeit.zustand (t + 1)).fragen = [] := by
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
      (ρ.zeit.zustand t) (.kontext eintritt (), ⟨[], []⟩) (b.nach eintritt (ρ.zeit.zustand t)) :=
    .kontext hNoCrash hReadyT
      ⟨b, headT, (b.ideal_privat eintritt (ρ.zeit.zustand t) () [Semantik.plan] _).2 ⟨rfl, rfl⟩⟩
      (b.vollzug _ _ _ _)
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
          (b.ideal_privat eintritt (ρ.zeit.zustand t) w0 [plan0] u0).1 ideal'
        cases same
        cases after
        have hakt : Semantik.plan.aktion = .intern := rfl
        obtain ⟨rahmen, _, sperren, v, fuehrt, _, hstate⟩ := aus
        rw [hakt] at fuehrt
        generalize hau : spur0.2 = au at fuehrt
        cases fuehrt with
        | intern =>
          refine ⟨⟨ev, hev⟩, ?_, ?_, ?_, ?_⟩
          · rw [hstate]
            simp only [Befehl.nach, hEqL]
          · rw [hstate]
            simp only [Befehl.nach, hEqS]
          · rw [hstate]
            simp only [Befehl.nach, hEqK]
          · rw [hstate]
            simp only [Befehl.nach, hEqF, hFrPre]
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

/-- The linked unit is not accepted: the witness run divides by zero. -/
theorem linked_nicht_akzeptiert : ¬ Akzeptiert E_linked := by
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
    baseL baseS baseK baseF
    (by rfl) (readyAt _ _ rfl rfl)
    (fun c hne => hStPre _ c hne rfl) (by rfl)
  have st1 := forceStep ρ hρ 1 k (.literal 1 2) (sLinked1 s)
    (hwCrash 1) (hwCore 1) (hwInt 1) hwInts (hwDel 1) (hwFrei 1)
    st0.2.1 st0.2.2.1 st0.2.2.2.1 st0.2.2.2.2
    (by rfl) (readyAt _ _ rfl rfl)
    (fun c hne => hStPre _ c hne rfl) (by rfl)
  have st2 := forceStep ρ hρ 2 k (.teilen 0) (sLinked2 s)
    (hwCrash 2) (hwCore 2) (hwInt 2) hwInts (hwDel 2) (hwFrei 2)
    st1.2.1 st1.2.2.1 st1.2.2.2.1 st1.2.2.2.2
    (by rfl) (readyAt _ _ rfl rfl)
    (fun c hne => hStPre _ c hne rfl) (by rfl)
  have st3 := forceStep ρ hρ 3 k (.literal 0 5) (sLinked3 s)
    (hwCrash 3) (hwCore 3) (hwInt 3) hwInts (hwDel 3) (hwFrei 3)
    st2.2.1 st2.2.2.1 st2.2.2.2.1 st2.2.2.2.2
    (by rfl) (readyAt _ _ rfl rfl)
    (fun c hne => hStPre _ c hne rfl) (by rfl)
  have st4 := forceStep ρ hρ 4 k (.literal 1 0) (sLinked4 s)
    (hwCrash 4) (hwCore 4) (hwInt 4) hwInts (hwDel 4) (hwFrei 4)
    st3.2.1 st3.2.2.1 st3.2.2.2.1 st3.2.2.2.2
    (by rfl) (readyAt _ _ rfl rfl)
    (fun c hne => hStPre _ c hne rfl) (by rfl)
  have st5 := forceStep ρ hρ 5 k (.zurueckSprung 3) (sLinked5 s)
    (hwCrash 5) (hwCore 5) (hwInt 5) hwInts (hwDel 5) (hwFrei 5)
    st4.2.1 st4.2.2.1 st4.2.2.2.1 st4.2.2.2.2
    (by rfl) (readyAt _ _ rfl rfl)
    (fun c hne => hStPre _ c hne rfl) (by rfl)
  obtain ⟨ev5, hspur5, hEqL6, hEqS6, hEqK6, hEqF6⟩ := st5
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
  have t6 : I.Schnitt E_linked ρ := ⟨6, Or.inr ⟨5, ev5, rfl, hspur5⟩⟩
  have need6 : (kanonischeVerwendung E_linked).bedarf ρ t6 .division (5, 0) :=
    ⟨eintritt, .teilen 0, head6, guard6⟩
  intro ha
  have hbad := ha.2.2.1 ρ hρ t6 .division (5, 0) need6
  simp only [waechterBedarf] at hbad
  exact hbad rfl

/-- The current linker statement is false: both parts are accepted, the plan links,
    but the linked unit divides by zero. -/
theorem linkerAkzeptiert_ohne_abschottung_falsch :
    ¬ Gabbro.Core.Ziel.Korrektheit.LinkerAkzeptiertAussage := by
  intro hlink
  have hparts : ∀ m ∈ planAB.module, Akzeptiert (m.fragment.einheit planAB.plattform) := by
    intro m hm
    simp only [planAB, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact fragA_akzeptiert
    · exact fragB_akzeptiert
  have hlinked : Akzeptiert ((verknuepfteFragmente planAB).einheit planAB.plattform) :=
    hlink _ _ planAB_linke hparts
  exact linked_nicht_akzeptiert hlinked

end Gabbro.Core.Linken
