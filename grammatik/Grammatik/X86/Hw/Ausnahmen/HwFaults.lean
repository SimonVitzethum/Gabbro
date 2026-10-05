/-
  File:      Grammatik/X86/HwFaults.lean
  Subject:   Architectural faults (#DE/#UD/#GP/#PF) as outcomes of the
             coherent multicore machine.

  Lane 1123: connect ONE family to the coherent machine of
  `HardwareExecution.lean`, reusing the accepted fault vocabulary and
  priority order of `HardwareFaults.lean` / `ExceptionPriorityHardware.lean`
  unchanged (never copied, only lifted). Faults are OUTCOMES
  (`HwFehlerAusgang`, `HwFehlerSchritt`), never an `Option`-plugged
  successor state. Priority follows the accepted ordered candidate row
  (fetch < decode < address < access < divide < control); a faulting
  store never enters the TSO buffer and a faulting load changes nothing.
-/
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Grundlage.ExceptionPriorityHardware
namespace Gabbro.Grammatik.X86

/-- Machine-level fault choice: the accepted ordered row, run on the
    core projection. The head IS the minimum-rank pending fault. -/
def hwFehlerWahl (m : HwMaschine) (c : Nat) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) (st : SteuerInfo) (ill : IllegalInfo)
    (teiltFalle : Bool) : Option PrioritaetsFehler :=
  ersteWahl (kandidatenReihe (projFp m c) z pg st ill teiltFalle)

/-! ## 1. Agreement: the machine choice is the accepted row head. -/

/-- The machine choice unfolds to the accepted row head. -/
theorem hwFehlerWahl_reihenkopf (m : HwMaschine) (c : Nat)
    (z : ZugriffsBeschreibung) (pg : SeitenInfo) (st : SteuerInfo)
    (ill : IllegalInfo) (teiltFalle : Bool) :
    hwFehlerWahl m c z pg st ill teiltFalle =
      (kandidatenReihe (projFp m c) z pg st ill teiltFalle).head? := rfl

/-! ## 2. Priority on the machine: the SDM order, lifted.

  The accepted dominance theorems run on the core projection; each
  machine theorem below uses every premise (no silent stage). -/

/-- Fetch beats everything on the machine. -/
theorem hwFehler_abruf_schlaegt_alles (m : HwMaschine) (c : Nat)
    (z : ZugriffsBeschreibung) (pg : SeitenInfo) (st : SteuerInfo)
    (ill : IllegalInfo) (teiltFalle : Bool) (f : PrioritaetsFehler)
    (h : abrufKandidat (projFp m c) = some f) :
    hwFehlerWahl m c z pg st ill teiltFalle = some f :=
  abruf_schlaegt_alles (projFp m c) z pg st ill teiltFalle f h

/-- Address beats access, divide and control on the machine. -/
theorem hwFehler_adresse_schlaegt_spaete (m : HwMaschine) (c : Nat)
    (z : ZugriffsBeschreibung) (pg : SeitenInfo) (st : SteuerInfo)
    (ill : IllegalInfo) (teiltFalle : Bool) (f : PrioritaetsFehler)
    (hfrueh : abrufKandidat (projFp m c) = none)
    (hdec : dekodiereKandidat (projFp m c) ill = none)
    (hadr : adressKandidat z = some f) :
    hwFehlerWahl m c z pg st ill teiltFalle = some f :=
  adresse_schlaegt_spaete (projFp m c) z pg st ill teiltFalle f
    hfrueh hdec hadr

/-- Access beats divide and control on the machine. -/
theorem hwFehler_zugriff_schlaegt_spaete (m : HwMaschine) (c : Nat)
    (z : ZugriffsBeschreibung) (pg : SeitenInfo) (st : SteuerInfo)
    (ill : IllegalInfo) (teiltFalle : Bool) (f : PrioritaetsFehler)
    (hfrueh : abrufKandidat (projFp m c) = none)
    (hdec : dekodiereKandidat (projFp m c) ill = none)
    (hadr : adressKandidat z = none)
    (hzug : zugriffKandidat (projFp m c) z pg = some f) :
    hwFehlerWahl m c z pg st ill teiltFalle = some f :=
  zugriff_schlaegt_teilung_steuerung (projFp m c) z pg st ill teiltFalle f
    hfrueh hdec hadr hzug

/-- The divide trap beats control on the machine. -/
theorem hwFehler_teilung_schlaegt_steuerung (m : HwMaschine) (c : Nat)
    (z : ZugriffsBeschreibung) (pg : SeitenInfo) (st : SteuerInfo)
    (ill : IllegalInfo)
    (hfrueh : abrufKandidat (projFp m c) = none)
    (hdec : dekodiereKandidat (projFp m c) ill = none)
    (hadr : adressKandidat z = none)
    (hzug : zugriffKandidat (projFp m c) z pg = none)
    (hfalle : teiltFalle = true) :
    hwFehlerWahl m c z pg st ill teiltFalle = some ⟨.teilung, .de⟩ := by
  have h := teilung_schlaegt_steuerung (projFp m c) z pg st ill
    hfrueh hdec hadr hzug hfalle
  simp only [hwFehlerWahl]
  exact h

/-! ## 3. Faults as outcomes: the extended outcome type.

  A fault carries the PRE-state machine plus its ordered stage and
  class -- never an `Option`-plugged successor. The register path
  embeds exactly; no embedded outcome is a fault. -/

/-- Machine-level register-or-fault outcome: the successor machine,
    the divide trap, explicit refusal, or the ordered fault observed
    against the pre-state machine. -/
inductive HwFehlerAusgang where
  | weiter : HwMaschine → HwFehlerAusgang
  | halt : HwFehlerAusgang
  | verweigert : HwFehlerAusgang
  | fehler : HwMaschine → PrioritaetsFehler → HwFehlerAusgang

/-- The register path embeds constructor by constructor. -/
def einbettenReg : HwRegAusgang → HwFehlerAusgang
  | .weiter m => .weiter m
  | .halt => .halt
  | .verweigert => .verweigert

/-- The embedding never invents a fault. -/
theorem einbettenReg_kein_fehler (o : HwRegAusgang) (m : HwMaschine)
    (f : PrioritaetsFehler) :
    einbettenReg o ≠ .fehler m f := by
  cases o with
  | weiter m' =>
    simp [einbettenReg]
  | halt =>
    simp [einbettenReg]
  | verweigert =>
    simp [einbettenReg]

/-- The embedding keeps the successor machine. -/
theorem einbettenReg_weiter (m : HwMaschine) :
    einbettenReg (.weiter m) = .weiter m := rfl

/-- The embedding keeps the divide trap. -/
theorem einbettenReg_halt : einbettenReg .halt = .halt := rfl

/-- The embedding keeps refusal. -/
theorem einbettenReg_verweigert :
    einbettenReg .verweigert = .verweigert := rfl

/-- The fault outcome IS the pre-state: no successor is hidden in it. -/
theorem fehler_ist_vorzstand (m : HwMaschine) (f : PrioritaetsFehler) :
    ∃ vor : HwMaschine, HwFehlerAusgang.fehler vor f = .fehler m f ∧
      vor.mem = m.mem ∧ ∀ d : Nat, vor.puffer d = m.puffer d :=
  ⟨m, rfl, rfl, fun _ => rfl⟩

/-! ## 4. The family adapter: faults admit no state step.

  A fault has no successor BY CONSTRUCTION, so the `HwAdapter` state
  step over the fault vocabulary refuses everything; fault behaviour
  lives in the outcome type (§3) and the extended step relation (§5).
  This keeps the §11 contract: defaults refuse, never trust. -/

/-- Fault adapter: no fault admits a successor state. -/
def adapterFehler1123 : HwAdapter PrioritaetsFehler :=
  verweigertAdapter _

/-- The fault adapter admits nothing. -/
theorem adapterFehler1123_verweigert (m : HwMaschine) (c : Nat)
    (f : PrioritaetsFehler) :
    adapterFehler1123.schritt m c f = none := rfl

/-! ## 5. The extended step relation: old steps plus fault outcomes.

  Every `HwSchritt` rides along unchanged under `.alt`; a pending
  ordered fault steps to ITSELF with the fault event -- the state
  never moves under a fault. -/

/-- Extended machine events: the old events plus the ordered fault. -/
inductive HwFehlerEreignis where
  | alt : HwEreignis → HwFehlerEreignis
  | fehler : Nat → PrioritaetsFehler → HwFehlerEreignis
  deriving DecidableEq, Repr

/-- One extended machine step: the embedded old step, or the ordered
    fault chosen on the acting core's projection. -/
inductive HwFehlerSchritt : HwMaschine → HwMaschine → HwFehlerEreignis → Prop where
  | einbettet {m m' : HwMaschine} (e : HwEreignis)
      (h : HwSchritt m m' e) :
      HwFehlerSchritt m m' (.alt e)
  | fehler {m : HwMaschine} (c : Nat) (z : ZugriffsBeschreibung)
      (pg : SeitenInfo) (st : SteuerInfo) (ill : IllegalInfo)
      (teiltFalle : Bool) (f : PrioritaetsFehler)
      (h : hwFehlerWahl m c z pg st ill teiltFalle = some f) :
      HwFehlerSchritt m m (.fehler c f)

/-- FORWARD embedding: every old step is an extended step. -/
theorem hwFehlerSchritt_einbettung_vor (m m' : HwMaschine)
    (e : HwEreignis) (h : HwSchritt m m' e) :
    HwFehlerSchritt m m' (.alt e) :=
  .einbettet e h

/-- BACKWARD embedding, exact: an `.alt` step comes only from the old
    step with the same event -- no new behaviour hides behind it. -/
theorem hwFehlerSchritt_einbettung_zurueck (m m' : HwMaschine)
    (e : HwEreignis) (h : HwFehlerSchritt m m' (.alt e)) :
    HwSchritt m m' e := by
  cases h with
  | einbettet _ hstep => exact hstep

/-- A fault step never moves the state. -/
theorem hwFehlerSchritt_fehler_still (m m' : HwMaschine) (c : Nat)
    (f : PrioritaetsFehler)
    (h : HwFehlerSchritt m m' (.fehler c f)) : m' = m := by
  cases h
  rfl

/-- Every extended step preserves well-formedness: old steps by the
    accepted preservation, fault steps because the state never moves. -/
theorem hwFehlerSchritt_wf (m m' : HwMaschine)
    (e : HwFehlerEreignis) (h : HwFehlerSchritt m m' e)
    (hwf : HwWf m) : HwWf m' := by
  cases h with
  | einbettet e' hstep => exact hwSchritt_wf m m' e' hstep hwf
  | fehler c z pg st ill teiltFalle f hwahl => exact hwf

/-! ## 6. Agreement with the accepted evaluator: lifted, never redefined.

  Success keeps its successor, the divide trap IS #DE, and refusal is
  never a fault -- the accepted binder equations, used by name. -/

/-- Success is never invented: the accepted binder equation. -/
theorem hwFehler_erfolg_treue (t' : FpZustand)
    (wahl : Option PrioritaetsFehler) :
    bindeUrteil (.weiter t') wahl = .erfolg t' :=
  urteil_erfolg_treue t' wahl

/-- The divide trap binds #DE, whatever the choice says. -/
theorem hwFehler_halt_ist_teilung (wahl : Option PrioritaetsFehler) :
    bindeUrteil .halt wahl = .fehler ⟨.teilung, .de⟩ :=
  urteil_halt_ist_teilung wahl

/-- Admission refusal is never a fault. -/
theorem hwFehler_verweigerung_kein_fehler (f : PrioritaetsFehler) :
    FehlerUrteil.zugelassenVerweigert ≠ .fehler f :=
  verweigerung_kein_fehler f

/-- Refusal with a pending choice binds that exact choice. -/
theorem hwFehler_verweigert_bindet_wahl (f : PrioritaetsFehler) :
    bindeUrteil .verweigert (some f) = .fehler f :=
  urteil_verweigert_wahl f

/-- The divide trap delivers on vector 0 (Table 6-1). -/
theorem hwFehler_de_vektor_null : fehlerVektor .de = 0 :=
  vektor_de_null

/-- The page fault delivers on vector 14 (Table 6-1). -/
theorem hwFehler_pf_vektor_vierzehn : fehlerVektor .pf = 14 :=
  vektor_pf_vierzehn

/-! ## 7. Buffer discipline: a faulting store never enters the buffer,
  a faulting load changes nothing.

  `issueByte` refuses exactly where the cell is not writable and
  `loadByte` refuses exactly where the cell is not readable (the
  accepted TSO equations); the machine `lade` step is a self-loop by
  construction, so observation never moves state. -/

/-- A store at a non-writable cell issues nothing. -/
theorem hwFehler_issue_verweigert (m : HwMaschine) (c : Nat)
    (b : Adresse) (v : Byte)
    (h : (tsoAnsicht m).mem.schreibbar b = false) :
    issueByte (tsoAnsicht m) c b v = none := by
  simp [issueByte, h]

/-- A faulting store never enters any buffer: no machine store step
    exists at a non-writable cell. -/
theorem hwFehler_schreibfehler_kein_puffer (m : HwMaschine) (c : Nat)
    (b : Adresse) (v : Byte)
    (h : (tsoAnsicht m).mem.schreibbar b = false) (m' : HwMaschine) :
    ¬ HwSchritt m m' (.schreibAusgabe c b v) := by
  intro hstep
  have hissue : ∃ s' : TSOZustand,
      issueByte (tsoAnsicht m) c b v = some s' := by
    cases hstep with
    | gibAus _ _ _ s' h => exact ⟨s', h⟩
  obtain ⟨s', hs'⟩ := hissue
  rw [hwFehler_issue_verweigert m c b v h] at hs'
  cases hs'

/-- A load at a non-readable cell observes nothing. -/
theorem hwFehler_lade_verweigert (m : HwMaschine) (c : Nat)
    (a : Adresse) (h : (tsoAnsicht m).mem.lesbar a = false) :
    loadByte (tsoAnsicht m) c a = none := by
  simp [loadByte, h]

/-- A faulting load changes nothing: every load step is a self-loop. -/
theorem hwFehler_lade_aendert_nichts (m m' : HwMaschine) (c : Nat)
    (a : Adresse) (v : Byte)
    (h : HwSchritt m m' (.leseBeob c a v)) : m' = m := by
  cases h with
  | lade _ _ _ _ => rfl

/-- Oracle-stated illegality on the machine projection IS the #UD
    candidate: refusal alone never claims it (accepted equation). -/
theorem hwFehler_orakel_ud (m : HwMaschine) (c : Nat)
    (ill : IllegalInfo)
    (href : decodeExt (geholt (projFp m c).kern) = none)
    (hill : ill.istIllegal (geholt (projFp m c).kern) = true) :
    dekodiereKandidat (projFp m c) ill = some ⟨.dekodiere, .ud⟩ :=
  dekodiere_orakel_ud (projFp m c) ill href hill

/-! ## 8. Planted refusals: the family admits nothing silently.

  Every shape below refuses through the ACCEPTED equations, reused by
  name: the illegal byte is refusal (never a silent #UD), LOCK stays
  refused, code memory answers no load and takes no store, and the
  zero-divisor divide on real execution IS #DE. -/

/-- No silent #UD: the illegal byte refuses and refusal is no fault. -/
theorem hwFehler_fehlbyte_kein_stiller_ud :
    decodeExt [natByte 255] = none ∧
      klassifiziereExt .verweigert = none :=
  fehlbyte_kein_stiller_ud

/-- LOCK stays refused on the coherent machine. -/
theorem hwFehler_lock_verweigert (m : HwMaschine) (c : Nat)
    (b : SperrBefehl) :
    hwLockAnfrage m c b = none :=
  hwLock_verweigert m c b

/-- Code memory answers no load on the witness machine. -/
theorem hwFehler_code_laden_verweigert :
    loadByte (tsoAnsicht hwWitStart) 0 hwWitCodeAdr = none :=
  hwWit_laden_code_verweigert

/-- Code memory takes no store on the witness machine. -/
theorem hwFehler_code_ausgabe_verweigert :
    issueByte (tsoAnsicht hwWitStart) 0 hwWitCodeAdr
      (BitVec.ofNat 8 42) = none :=
  hwWit_ausgabe_code_verweigert

/-- Zero-divisor divide on real execution IS #DE. -/
theorem hwFehler_de_durch_null :
    klassifiziereMulDiv
      (mulDivSchritt ⟨.divRax .rcx, 3⟩ mdZustandNull) =
      some .de := by
  have h := fehler_div_null_haelt_zeuge.1
  rw [h]
  rfl

/-! ## 9. Joint witness: two cores, fault plus memory-changing run.

  Core 1 idles on non-executable memory: its fetch window is empty,
  so the ordered choice is the fetch #PF -- ahead of every later
  stage. Core 0 runs the accepted two-core byte/TSO witness beside
  it: owner-only forwarding, then a drain that changes ACTUAL shared
  memory (0 becomes 42, observed from both cores). -/

/-- Witness descriptor: no data access, no divide, disarmed control --
    only fetch and decode may fire. -/
def hwFehlerZLeer : ZugriffsBeschreibung :=
  ⟨none, none, false, 8, false⟩

/-- Witness page state: every page non-present (access class would be
    #PF -- but no access fires on the empty descriptor). -/
def hwFehlerPgDunkel : SeitenInfo := ⟨fun _ => false⟩

/-- Core 1 (non-executable RIP) carries the fetch #PF candidate. -/
theorem hwFehler_wit_abruf :
    abrufKandidat (projFp hwWitStart 1) = some ⟨.abruf, .pf⟩ := by
  decide

/-- The ordered machine choice on core 1 is the fetch #PF. -/
theorem hwFehler_wit_wahl :
    hwFehlerWahl hwWitStart 1 hwFehlerZLeer hwFehlerPgDunkel ⟨false⟩
      ⟨fun _ => false⟩ false = some ⟨.abruf, .pf⟩ := by
  have hab := hwFehler_wit_abruf
  simp [hwFehlerWahl, kandidatenReihe, ersteWahl, hab]

/-- The reached fault step: core 1 faults, the state never moves. -/
theorem hwFehler_wit_schritt :
    HwFehlerSchritt hwWitStart hwWitStart (.fehler 1 ⟨.abruf, .pf⟩) :=
  .fehler 1 hwFehlerZLeer hwFehlerPgDunkel ⟨false⟩
    ⟨fun _ => false⟩ false ⟨.abruf, .pf⟩ hwFehler_wit_wahl

/-- JOINT WITNESS: a reached two-core run that ties the fault to the
    memory-changing TSO run. Well-formedness and the fault step join
    the premises of `hwFehlerSchritt_wf`; beside them the buffered
    store is visible via forwarding to the owner only, the drain
    changes ACTUAL shared memory (0 becomes 42, observed from both
    cores), the code cell refuses load and store, and the
    zero-divisor divide on real execution IS #DE. Non-degenerate:
    the drain changes real memory and the fault fires on a second
    core. -/
theorem hwFehler_zeuge :
    HwWf hwWitStart ∧
      HwFehlerSchritt hwWitStart hwWitStart
        (.fehler 1 ⟨.abruf, .pf⟩) ∧
      hwWitMem.bytes hwWitAdr = BitVec.ofNat 8 0 ∧
      hwWitLoadEigen = some (some (BitVec.ofNat 8 42)) ∧
      hwWitLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
      hwWitNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      hwWitFremdNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      loadByte (tsoAnsicht hwWitStart) 0 hwWitCodeAdr = none ∧
      issueByte (tsoAnsicht hwWitStart) 0 hwWitCodeAdr
        (BitVec.ofNat 8 42) = none ∧
      klassifiziereMulDiv
        (mulDivSchritt ⟨.divRax .rcx, 3⟩ mdZustandNull) =
        some .de := by
  refine ⟨hwWitStart_wf, hwFehler_wit_schritt, hwWit_anfang_null,
    hwWit_weiterleitung, hwWit_fremd_alt,
    hwWit_spülung_aendert_speicher, hwWit_fremd_neu,
    hwWit_laden_code_verweigert, hwWit_ausgabe_code_verweigert,
    hwFehler_de_durch_null⟩

/- CUTS:
    Proved here (all over the REUSED coherent machine and the REUSED
    accepted fault vocabulary -- no new machine, no new decoder row,
    no new instruction, no silicon re-verification):
    - machine fault choice `hwFehlerWahl` (the accepted ordered row
      on the core projection) with the SDM priority lifts: fetch
      beats all, address beats access/divide/control, access beats
      divide/control, divide beats control (§1, §2);
    - faults as outcomes (`HwFehlerAusgang` + `einbettenReg`: the
      register path embeds exactly and never invents a fault; the
      fault outcome IS the pre-state) and the refusing family
      adapter `adapterFehler1123` (§3, §4);
    - the extended step relation `HwFehlerSchritt` with the EXACT
      two-way embedding of `HwSchritt`, fault steps that never move
      state, wf preservation, and the accepted binder equations
      (success keeps its successor, halt IS the divide #DE, refusal
      is never a fault; vectors 0 and 14) (§5, §6);
    - buffer discipline on the accepted TSO equations: a faulting
      store never enters any buffer (no store step at a
      non-writable cell), a faulting load observes nothing and every
      load step is a self-loop; oracle-stated illegality IS the #UD
      candidate (§7);
    - planted refusals through the accepted equations: illegal byte
      (no silent #UD), LOCK, code-cell load/store, zero-divisor #DE
      on real execution (§8);
    - joint witness: reached two-core run (fetch #PF on core 1 with
      owner-only forwarding and a memory-changing drain on core 0)
      beside the load/store/divide refusals (§9).
    NOT proved here, and not claimed:
    - No hardware verification: classes, vectors and the order NAME
      the accepted manual entries (Table 6-1, Table 7-2, canonical
      addressing §3.3.7.1 per the MUSE-REPORT-660/670 provenance);
      the quotient rule and flag relations are inherited from the
      accepted `MulDiv`/`Ganzzahl` semantics, not verified here.
    - No #UD membership from refusal alone (`decodeExt = none` may
      be illegal OR unmodelled); no unmasked #XM/#AC/#NM claim
      (masked FP computes, disarmed control never faults).
    - No fault DELIVERY (IDT/stack/handler/error code stays with
      lane 672), no per-access target-to-W/GX simulation, no
      whole-word atomicity beyond the accepted `WortGruppe` guard,
      no source stop-class or time transfer.
-/

#print axioms hwFehlerWahl
#print axioms hwFehlerWahl_reihenkopf
#print axioms hwFehler_abruf_schlaegt_alles
#print axioms hwFehler_adresse_schlaegt_spaete
#print axioms hwFehler_zugriff_schlaegt_spaete
#print axioms hwFehler_teilung_schlaegt_steuerung
#print axioms einbettenReg
#print axioms einbettenReg_kein_fehler
#print axioms fehler_ist_vorzstand
#print axioms adapterFehler1123
#print axioms adapterFehler1123_verweigert
#print axioms hwFehlerSchritt_einbettung_vor
#print axioms hwFehlerSchritt_einbettung_zurueck
#print axioms hwFehlerSchritt_fehler_still
#print axioms hwFehlerSchritt_wf
#print axioms hwFehler_erfolg_treue
#print axioms hwFehler_halt_ist_teilung
#print axioms hwFehler_verweigerung_kein_fehler
#print axioms hwFehler_verweigert_bindet_wahl
#print axioms hwFehler_de_vektor_null
#print axioms hwFehler_pf_vektor_vierzehn
#print axioms hwFehler_issue_verweigert
#print axioms hwFehler_schreibfehler_kein_puffer
#print axioms hwFehler_lade_verweigert
#print axioms hwFehler_lade_aendert_nichts
#print axioms hwFehler_orakel_ud
#print axioms hwFehler_fehlbyte_kein_stiller_ud
#print axioms hwFehler_lock_verweigert
#print axioms hwFehler_code_laden_verweigert
#print axioms hwFehler_code_ausgabe_verweigert
#print axioms hwFehler_de_durch_null
#print axioms hwFehler_wit_abruf
#print axioms hwFehler_wit_wahl
#print axioms hwFehler_wit_schritt
#print axioms hwFehler_zeuge

end Gabbro.Grammatik.X86
