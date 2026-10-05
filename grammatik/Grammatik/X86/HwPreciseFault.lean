/-
  File:      Grammatik/X86/HwPreciseFault.lean
  Subject:   Precise exceptions at the store buffer: faults and interrupt
             delivery against buffered stores on the coherent machine.

  Lane 1225: follow-up of lanes 1123 (`HwFaults`), 1125/1181
  (`HwInterrupts`, `HwNestedInterrupts`) and 1185
  (`HwForwardingGeneric`). Nothing is redefined here: the fault choice
  (`hwFehlerWahl`), the fault step (`HwFehlerSchritt`), the delivery
  step (`asyncSchritt`) and the byte equations (`issueByte`,
  `loadByte`, `flushKern`) are lifted unchanged. Proved: a fault step
  has no architectural effect (older stores stay buffered, memory and
  every core view are still); delivery never drains any buffer (S3);
  the owner keeps forwarding buffered stores to the handler while a
  foreign core sees them only after drain.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.HwFaults
import Grammatik.X86.HwInterrupts

namespace Gabbro.Grammatik.X86

/-! ## 1. Family event type and the adapter plug.

   A fault admits no successor state (the accepted
   `adapterFehler1123` discipline); delivery reuses the accepted
   `asyncSchritt` with the event's own control snapshot. -/

/-- Precise-exception family events: an ordered fault, or an async
    delivery attempt. -/
inductive PrzEreignis where
  | fehler : PrioritaetsFehler → PrzEreignis
  | liefere : AsyncEreignis → PrzEreignis
  deriving DecidableEq, Repr

/-- The family adapter: faults refuse (no successor BY
    CONSTRUCTION), delivery is exactly the accepted step. -/
def adapterPraezise : HwAdapter PrzEreignis :=
  ⟨fun m c ev => match ev with
    | .fehler _ => none
    | .liefere a => (asyncSchritt m c a a.steuer).map (fun r => r.1)⟩

/-- A fault admits no successor through this plug. -/
theorem adapterPraezise_fehler_verweigert (m : HwMaschine) (c : Nat)
    (f : PrioritaetsFehler) :
    adapterPraezise.schritt m c (.fehler f) = none := rfl

/-! ## 2. Precise fault: the faulting instruction has no effect.

   A fault step is a self-loop (the accepted
   `hwFehlerSchritt_fehler_still`): shared memory, every buffer and
   hence every core view are still. An older store is therefore
   either still buffered or drained by somebody else -- never by the
   fault itself. -/

/-- A fault step leaves shared memory alone. -/
theorem przFehler_speicher_still (m m' : HwMaschine) (c : Nat)
    (f : PrioritaetsFehler)
    (h : HwFehlerSchritt m m' (.fehler c f)) :
    m'.mem = m.mem := by
  have hs := hwFehlerSchritt_fehler_still m m' c f h
  rw [hs]

/-- A fault step drops no buffered store on any core. -/
theorem przFehler_puffer_still (m m' : HwMaschine) (c : Nat)
    (f : PrioritaetsFehler)
    (h : HwFehlerSchritt m m' (.fehler c f)) (d : Nat) :
    m'.puffer d = m.puffer d := by
  have hs := hwFehlerSchritt_fehler_still m m' c f h
  rw [hs]

/-- Every older buffered store survives the fault. -/
theorem przFehler_eintrag_bleibt (m m' : HwMaschine) (c : Nat)
    (f : PrioritaetsFehler)
    (h : HwFehlerSchritt m m' (.fehler c f)) (d : Nat)
    (e : TSOEintrag) (hm : e ∈ m.puffer d) :
    e ∈ m'.puffer d := by
  have hp := przFehler_puffer_still m m' c f h d
  rw [hp]
  exact hm

/-- No core view moves under a fault: every observation is still. -/
theorem przFehler_beobachtung_still (m m' : HwMaschine) (c : Nat)
    (f : PrioritaetsFehler)
    (h : HwFehlerSchritt m m' (.fehler c f)) (d : Nat)
    (a : Adresse) :
    loadByte (tsoAnsicht m') d a = loadByte (tsoAnsicht m) d a := by
  have hs := hwFehlerSchritt_fehler_still m m' c f h
  rw [hs]

/-! ## 3. Delivery is not a drain.

   The accepted S3 (lane 1125: only stated serialising forms drain;
   delivery alone leaves pending stores buffered) lifted from the
   push stage to the whole delivery step: every successful delivery
   keeps well-formedness (profiles untouched) and every buffer on
   every core. The named silicon assumption is S3 itself
   (`HwInterrupts.lean` §1: SDM Vol. 3 interrupt delivery and the
   memory-ordering chapter, provenance per MUSE-REPORT-660/1125). -/

/-- Push-stage preservation: the frame changes memory only; the
    successor keeps profiles and all buffers. -/
theorem przFertig_erhaelt (m : HwMaschine) (c : Nat)
    (st : Steuerstand) (g : IdtTor) (q : LieferAnfrage) (rsp : Wort)
    (gew : Bool) (m' : HwMaschine) (ifNeu gew' : Bool)
    (h : asyncFertig m c st g q rsp gew = some (m', ifNeu, gew'))
    (hwf : HwWf m) :
    HwWf m' ∧ ∀ d : Nat, m'.puffer d = m.puffer d := by
  unfold asyncFertig at h
  cases hk : istKanonisch rsp with
  | false =>
    rw [hk] at h
    simp at h
  | true =>
    rw [hk] at h
    simp at h
    cases hs : schiebeRahmen m.mem rsp (rahmenWorte q) with
    | none =>
      rw [hs] at h
      simp at h
    | some m2 =>
      rw [hs] at h
      simp at h
      obtain ⟨h1, _, _⟩ := h
      rw [← h1]
      exact ⟨asyncMasch_wf m c g q rsp m2 hwf, fun _ => rfl⟩

/-- Delivery preservation: checks first, effects only through the
    push stage, so profiles and every buffer survive. -/
theorem przLieferung_erhaelt (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand) (m' : HwMaschine)
    (ifNeu gew : Bool)
    (h : asyncSchritt m c ev st = some (m', ifNeu, gew))
    (hwf : HwWf m) :
    HwWf m' ∧ ∀ d : Nat, m'.puffer d = m.puffer d := by
  unfold asyncSchritt at h
  cases hvo : asyncVektorOk ev with
  | false =>
    rw [hvo] at h
    simp at h
  | true =>
    rw [hvo] at h
    simp at h
    cases hb : asyncBereit ev with
    | false =>
      rw [hb] at h
      simp at h
    | true =>
      rw [hb] at h
      simp at h
      cases hl : torImLimit st.idtLimit ev.vektor with
      | false =>
        rw [hl] at h
        simp at h
      | true =>
        rw [hl] at h
        simp at h
        cases hr : liesTorBytes m.mem
            (torAdresse st.idtBasis ev.vektor) with
        | none =>
          rw [hr] at h
          simp at h
        | some t =>
          rw [hr] at h
          simp at h
          cases hp : pruefeTor ev.vektor st.idtLimit t .extern
              st.cpl ev.codeOk with
          | fehler _ =>
            rw [hp] at h
            simp at h
          | bereit g =>
            rw [hp] at h
            simp at h
            cases hs : waehleStapel m.mem st g.ist ev.neuDpl
                ev.wechsel ((m.kerne c).register Register.rsp) with
            | stapelFehler _ =>
              rw [hs] at h
              simp at h
            | behalten rsp =>
              rw [hs] at h
              simp at h
              exact przFertig_erhaelt m c st g _ rsp _ m' ifNeu gew h hwf
            | wechseln rsp =>
              rw [hs] at h
              simp at h
              exact przFertig_erhaelt m c st g _ rsp _ m' ifNeu gew h hwf

/-- Delivery preserves well-formedness. -/
theorem przLieferung_wf (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand) (m' : HwMaschine)
    (ifNeu gew : Bool)
    (h : asyncSchritt m c ev st = some (m', ifNeu, gew))
    (hwf : HwWf m) : HwWf m' :=
  (przLieferung_erhaelt m c ev st m' ifNeu gew h hwf).1

/-- Delivery drains no buffer on any core. -/
theorem przLieferung_puffer_still (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand) (m' : HwMaschine)
    (ifNeu gew : Bool)
    (h : asyncSchritt m c ev st = some (m', ifNeu, gew))
    (hwf : HwWf m) (d : Nat) :
    m'.puffer d = m.puffer d :=
  (przLieferung_erhaelt m c ev st m' ifNeu gew h hwf).2 d

/-! ## 4. Agreement, refusals and handler forwarding.

   The plug IS the accepted step on delivery (no new semantics);
   masked and misranged events refuse through the accepted refusal
   lemmas. A buffered older store keeps forwarding to its owner
   across delivery (buffers are still by §3); nothing is claimed
   about foreign cores beyond the buffer equations -- their
   visibility arrives only with the drain (§5 witness). -/

/-- Delivery through the plug is the accepted step. -/
theorem adapterPraezise_liefere_treue (m : HwMaschine) (c : Nat)
    (a : AsyncEreignis) :
    adapterPraezise.schritt m c (.liefere a) =
      (asyncSchritt m c a a.steuer).map (fun r => r.1) := rfl

/-- Every admitted plug step preserves well-formedness. -/
theorem adapterPraezise_wf (m m' : HwMaschine) (c : Nat)
    (ev : PrzEreignis)
    (h : adapterPraezise.schritt m c ev = some m')
    (hwf : HwWf m) : HwWf m' := by
  cases ev with
  | fehler f =>
    simp [adapterPraezise] at h
  | liefere a =>
    have h' : (asyncSchritt m c a a.steuer).map
        (fun r => r.1) = some m' := h
    cases hs : asyncSchritt m c a a.steuer with
    | none =>
      simp [hs] at h'
    | some r =>
      rw [hs] at h'
      simp at h'
      have hs' : asyncSchritt m c a a.steuer =
          some (r.1, r.2.1, r.2.2) := hs
      rw [← h']
      exact przLieferung_wf m c a a.steuer r.1 r.2.1 r.2.2 hs' hwf

/-- A masked maskable event refuses through the plug. -/
theorem adapterPraezise_maskiert_verweigert (m : HwMaschine)
    (c : Nat) (ev : AsyncEreignis)
    (hv : asyncVektorOk ev = true)
    (hb : asyncBereit ev = false) :
    adapterPraezise.schritt m c (.liefere ev) = none := by
  have h := asyncSchritt_verweigert_maskiert m c ev ev.steuer hv hb
  have h' : (asyncSchritt m c ev ev.steuer).map
      (fun r => r.1) = none := by
    rw [h]
    rfl
  exact h'

/-- A misranged vector refuses through the plug. -/
theorem adapterPraezise_vektor_verweigert (m : HwMaschine)
    (c : Nat) (ev : AsyncEreignis)
    (hv : asyncVektorOk ev = false) :
    adapterPraezise.schritt m c (.liefere ev) = none := by
  have h := asyncSchritt_verweigert_vektor m c ev ev.steuer hv
  have h' : (asyncSchritt m c ev ev.steuer).map
      (fun r => r.1) = none := by
    rw [h]
    rfl
  exact h'

/-- Handler forwarding: a store buffered on the acting core keeps
    reaching it after delivery -- the buffer is still (§3) and the
    frame push is elsewhere (readability at `a` is the premise). -/
theorem przHandler_weiterleitung (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand) (m' : HwMaschine)
    (ifNeu gew : Bool)
    (h : asyncSchritt m c ev st = some (m', ifNeu, gew))
    (hwf : HwWf m) (a : Adresse) (w : Byte)
    (hbuf : neuestens (m.puffer c) a = some w)
    (hles : m'.mem.lesbar a = true) :
    loadByte (tsoAnsicht m') c a = some w := by
  have hp := przLieferung_puffer_still m c ev st m' ifNeu gew h hwf c
  have hbuf' : neuestens (m'.puffer c) a = some w := by
    rw [hp]
    exact hbuf
  have e1 : (tsoAnsicht m').mem = m'.mem := rfl
  have e2 : (tsoAnsicht m').puffer c = m'.puffer c := rfl
  unfold loadByte
  rw [e1, e2, hles, hbuf']
  simp

/-! ## 5. Joint witness: two cores, a buffered store, then #PF.

   Core 0 issues byte 42 at the witness data cell on the accepted
   two-core start machine; core 1 carries the fetch #PF (the accepted
   choice on the same projection: the issue touches no projection).
   At fault time the store is still buffered, visible to the owner
   by forwarding and to core 1 only after the drain. -/

/-- Core 0 issues byte 42 at the witness data cell. -/
def przWitTso : Option TSOZustand :=
  issueByte (tsoAnsicht hwWitStart) 0 hwWitAdr (BitVec.ofNat 8 42)

/-- The witness machine: the buffered store sits on core 0. -/
def przWitM : HwMaschine :=
  match przWitTso with
  | some s => setTso hwWitStart s
  | none => hwWitStart

/-- The issue touches no core projection: same fault candidate. -/
theorem przWit_proj : projFp przWitM 1 = projFp hwWitStart 1 := rfl

/-- Core 1 carries the fetch #PF candidate. -/
theorem przWit_abruf :
    abrufKandidat (projFp przWitM 1) = some ⟨.abruf, .pf⟩ := by
  rw [przWit_proj]
  exact hwFehler_wit_abruf

/-- The ordered machine choice on core 1 is the fetch #PF. -/
theorem przWit_wahl :
    hwFehlerWahl przWitM 1 hwFehlerZLeer hwFehlerPgDunkel ⟨false⟩
      ⟨fun _ => false⟩ false = some ⟨.abruf, .pf⟩ :=
  hwFehler_abruf_schlaegt_alles przWitM 1 hwFehlerZLeer
    hwFehlerPgDunkel ⟨false⟩ ⟨fun _ => false⟩ false
    ⟨.abruf, .pf⟩ przWit_abruf

/-- The reached fault step: core 1 faults, the state never moves. -/
theorem przWit_schritt :
    HwFehlerSchritt przWitM przWitM (.fehler 1 ⟨.abruf, .pf⟩) :=
  .fehler 1 hwFehlerZLeer hwFehlerPgDunkel ⟨false⟩
    ⟨fun _ => false⟩ false ⟨.abruf, .pf⟩ przWit_wahl

/-- The witness machine is well-formed. -/
theorem przWit_wf : HwWf przWitM := by
  cases h : przWitTso with
  | none =>
    have e : przWitM = hwWitStart := by simp [przWitM, h]
    rw [e]
    exact hwWitStart_wf
  | some s =>
    have e : przWitM = setTso hwWitStart s := by simp [przWitM, h]
    rw [e]
    exact setTso_wf _ s hwWitStart_wf

/-- At fault time the store is still buffered on core 0. -/
theorem przWit_gepuffert : (przWitM.puffer 0).length = 1 := by
  decide

/-- The owner forwards the still-buffered store. -/
theorem przWit_eigen :
    loadByte (tsoAnsicht przWitM) 0 hwWitAdr =
      some (BitVec.ofNat 8 42) := by
  decide

/-- The foreign core still reads the old byte. -/
theorem przWit_fremd :
    loadByte (tsoAnsicht przWitM) 1 hwWitAdr =
      some (BitVec.ofNat 8 0) := by
  decide

/-- Core 0 drains its oldest entry. -/
def przWitTso2 : Option TSOZustand :=
  match przWitTso with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def przWitNachFlush : Option (Option Byte) :=
  match przWitTso2 with
  | some s => some (some (s.mem.bytes hwWitAdr))
  | none => none

/-- Core 1 reads the drained byte from shared memory. -/
def przWitFremdNachFlush : Option (Option Byte) :=
  match przWitTso2 with
  | some s => some (loadByte s 1 hwWitAdr)
  | none => none

/-- The drain installs the byte into shared memory. -/
theorem przWit_spuelung :
    przWitNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem przWit_fremd_neu :
    przWitFremdNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- Masked delivery refuses on the witness machine as well. -/
theorem przWit_maskiert_verweigert :
    asyncSchritt przWitM 0 witMaskiert witSteuerNmi = none :=
  asyncSchritt_verweigert_maskiert przWitM 0 witMaskiert
    witSteuerNmi (by decide) (by decide)

/-- JOINT WITNESS: a reached two-core run -- well-formedness, the
    fetch #PF on core 1 with the store still buffered on core 0,
    owner-only forwarding, the memory-changing drain observed from
    both cores, the masked-delivery refusal and the plug's fault
    refusal. Non-degenerate: the drain changes ACTUAL shared memory
    while the fault fires on the second core. -/
theorem prz_zeuge :
    HwWf przWitM ∧
      HwFehlerSchritt przWitM przWitM (.fehler 1 ⟨.abruf, .pf⟩) ∧
      (przWitM.puffer 0).length = 1 ∧
      loadByte (tsoAnsicht przWitM) 0 hwWitAdr =
        some (BitVec.ofNat 8 42) ∧
      loadByte (tsoAnsicht przWitM) 1 hwWitAdr =
        some (BitVec.ofNat 8 0) ∧
      przWitNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      przWitFremdNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      asyncSchritt przWitM 0 witMaskiert witSteuerNmi = none ∧
      adapterPraezise.schritt przWitM 0
        (.fehler ⟨.abruf, .pf⟩) = none := by
  refine ⟨przWit_wf, przWit_schritt, przWit_gepuffert, przWit_eigen,
    przWit_fremd, przWit_spuelung, przWit_fremd_neu,
    przWit_maskiert_verweigert, rfl⟩

/- CUTS:
   Proved here, over the REUSED coherent machine and the REUSED
   accepted fault/delivery vocabulary (no new machine, no new
   decoder row, no silicon re-verification):
   - family event type `PrzEreignis` with the `HwAdapter` plug
     `adapterPraezise` (faults refuse, delivery IS the accepted
     step), agreement and wf preservation (§1, §4);
   - precise fault: a fault step leaves memory, every buffer,
     every buffered entry and every core view still (§2);
   - delivery preservation: profiles and every buffer on every
     core survive delivery -- S3, the named silicon assumption
     (`HwInterrupts.lean` §1; SDM Vol. 3 provenance per
     MUSE-REPORT-660/1125) (§3);
   - handler forwarding across delivery (§4) with the masked and
     misranged refusals beside it;
   - joint witness: two cores, a buffered store, then #PF, with
     owner-only forwarding, the memory-changing drain and the
     refusals (§5).
   NOT proved here, and not claimed:
   - No hardware verification: classes, vectors and the S3 order
     NAME the accepted manual entries; delivery timing versus a
     racing drain is not modelled (drains are separate steps).
   - No fault DELIVERY (IDT path stays with lanes 672/1125/1181),
     no per-access target-to-W/GX simulation, no whole-word
     atomicity beyond the accepted `WortGruppe` guard, no word-
     level forwarding interaction beyond the shared byte
     equations with lane 1185.
-/

#print axioms adapterPraezise
#print axioms adapterPraezise_fehler_verweigert
#print axioms adapterPraezise_liefere_treue
#print axioms adapterPraezise_wf
#print axioms adapterPraezise_maskiert_verweigert
#print axioms adapterPraezise_vektor_verweigert
#print axioms przFehler_speicher_still
#print axioms przFehler_puffer_still
#print axioms przFehler_eintrag_bleibt
#print axioms przFehler_beobachtung_still
#print axioms przFertig_erhaelt
#print axioms przLieferung_erhaelt
#print axioms przLieferung_wf
#print axioms przLieferung_puffer_still
#print axioms przHandler_weiterleitung
#print axioms przWit_proj
#print axioms przWit_abruf
#print axioms przWit_wahl
#print axioms przWit_schritt
#print axioms przWit_wf
#print axioms przWit_gepuffert
#print axioms przWit_eigen
#print axioms przWit_fremd
#print axioms przWit_spuelung
#print axioms przWit_fremd_neu
#print axioms przWit_maskiert_verweigert
#print axioms prz_zeuge

end Gabbro.Grammatik.X86
