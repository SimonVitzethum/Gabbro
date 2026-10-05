/-
  File:      Grammatik/X86/HwFeatureGates.lean
  Subject:   CPUID/feature enabled-state gating inside the coherent
             machine `HwMaschine`/`HwSchritt`.

  Lane 1135: connect ONE family strand (CPUID/XCR0 observation from
  `CpuFeatureHardwareForms`, finite admission from `FeatureProfile`,
  per-image closing from `ComposeFeatureGate`) to the coherent
  machine from `HardwareExecution`, reusing every accepted definition
  unchanged (never a copied model; only lifted equations). The
  architectural fault vocabulary is `ArchFehler` (`HardwareFaults`).
-/
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Grundlage.HardwareFaults
import Grammatik.X86.Compose.Buchungen.ComposeFeatureGate

namespace Gabbro.Grammatik.X86

/-- Feature row behind one unified instruction: scalar FP needs the
    scalar-double row, packed integer the packed tier; every other
    dispatcher family needs no feature bit (always admitted). -/
def hwTorMerkmal : ExtInstr → Option PerfMerkmal
  | .fp _ => some .sseDoppel
  | .vec _ => some .paketInt128
  | _ => none

/-! ## 1. Gate predicates: profile, state and observation.

  Three independent legs, all reused (never redefined):
  - `hwTorBereit`: the finite profile admission (`merkmalZugelassen`)
    on the machine's own silicon/readiness (`m.hw`, `m.bereit c`);
  - `hwTorZustand`: the step-enforced state admission (`fpEintritt`
    on the core's FP context, `vecEintritt` on readiness);
  - `hwTorBeobachtet`: the observed CPUID/XCR0 bit gate
    (`beobachtungsTor`) over the reached chain's named answers.
  Either closed leg closes the whole gate; the fault classifier
  `hwTorFehler` names the architectural #UD outcome. -/

/-- Profile leg: finite admission on the machine's own profiles. -/
def hwTorBereit (m : HwMaschine) (c : Nat) (i : ExtInstr) : Bool :=
  match hwTorMerkmal i with
  | none => true
  | some f => merkmalZugelassen m.hw (m.bereit c) f

/-- State leg: the admission the accepted steps enforce themselves. -/
def hwTorZustand (m : HwMaschine) (c : Nat) : ExtInstr → Bool
  | .fp _ => fpEintritt (projFp m c).fp
  | .vec _ => vecEintritt (m.bereit c)
  | _ => true

/-- Observation leg: the reached CPUID/XCR0 answers admit the row. -/
def hwTorBeobachtet (leaf1 : CpuOut) (xcrLo : BitVec 32) :
    ExtInstr → Bool
  | .fp _ => beobachtungsTor leaf1 xcrLo .sseDoppel
  | .vec _ => beobachtungsTor leaf1 xcrLo .paketInt128
  | _ => true

/-- The whole gate: all three legs must be open. -/
def hwTorOffen (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (i : ExtInstr) : Bool :=
  hwTorBereit m c i && hwTorZustand m c i
    && hwTorBeobachtet leaf1 xcrLo i

/-- Gate fault classifier: a closed gate is the architectural #UD
    outcome; an open gate is no fault. This classifies the GATE, not
    the step: `klassifiziereExt` still maps every step refusal to
    `none` (reused `stepExt_verweigert_kein_de`). -/
def hwTorFehler (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (i : ExtInstr) : Option ArchFehler :=
  if hwTorOffen m c leaf1 xcrLo i then none else some .ud

/-- The mapping needs no feature for pilot steps. -/
theorem hwTorMerkmal_pilot (d : Decodiert) :
    hwTorMerkmal (.pilot d) = none := rfl

/-- An open gate classifies no fault. -/
theorem hwTorFehler_offen (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (i : ExtInstr)
    (h : hwTorOffen m c leaf1 xcrLo i = true) :
    hwTorFehler m c leaf1 xcrLo i = none := by
  simp [hwTorFehler, h]

/-- A closed gate classifies #UD. -/
theorem hwTorFehler_ud (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (i : ExtInstr)
    (h : hwTorOffen m c leaf1 xcrLo i = false) :
    hwTorFehler m c leaf1 xcrLo i = some .ud := by
  simp [hwTorFehler, h]

/-! ## 2. Generic refusal: a closed state leg never executes.

  Proved generically over the dispatcher's families (`ExtInstr`),
  not per example: wherever the state leg (`hwTorZustand`) is closed,
  the unified step is `verweigert` -- the accepted evaluators are
  lifted, never redefined. The profile leg closes the vector arm the
  same way once silicon is present (`vecEintritt_merkmal`); the
  scalar-FP profile leg and the observation leg are enforced by the
  §3 wrapper (the accepted FP step does not read `BereitProfil` and
  no accepted step reads CPUID answers -- see CUTS). -/

/-- Closed OS vector state refuses EVERY packed-integer step. -/
theorem hwTor_vec_verweigert (v : VectorDec) (t : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk v.laenge = true) (h : vecEintritt b = false) :
    stepExt (.vec v) t b = .verweigert :=
  stepExt_vec_verweigert v t b
    (stepVector_profil_verweigert v t b hok h)

/-- Closed FP control state refuses EVERY scalar-FP step. -/
theorem hwTor_fp_verweigert (f : FpDecodiert) (t : FpZustand)
    (b : BereitProfil)
    (hok : laengeOk f.laenge = true) (h : fpEintritt t.fp = false) :
    stepExt (.fp f) t b = .verweigert :=
  stepExt_fp_verweigert f t b
    (fpSchritt_profil_verweigert f t hok h)

/-- Closed finite profile refuses the vector arm where silicon is
    present: `m.bereit c` gating for an admitted family step. -/
theorem hwTor_vec_bereit_verweigert (hw : HwProfil)
    (b : BereitProfil) (v : VectorDec) (t : FpZustand)
    (hsilizium : hat hw .paketInt128 = true)
    (htor : merkmalZugelassen hw b .paketInt128 = false)
    (hok : laengeOk v.laenge = true) :
    stepExt (.vec v) t b = .verweigert := by
  have heintritt : vecEintritt b = false := by
    rw [vecEintritt_merkmal hw b hsilizium, htor]
  exact stepExt_vec_verweigert v t b
    (stepVector_profil_verweigert v t b hok heintritt)

/-- Closed FP control state refuses the scalar-FP step on the
    coherent machine projection (length and profile legs jointly). -/
theorem hwTor_fp_zustand_verweigert (m : HwMaschine) (c : Nat)
    (f : FpDecodiert)
    (h : fpEintritt (projFp m c).fp = false) :
    stepExt (.fp f) (projFp m c) (m.bereit c) = .verweigert := by
  cases e : laengeOk f.laenge
  case true => exact hwTor_fp_verweigert f _ _ e h
  case false =>
    exact stepExt_fp_verweigert f _ _
      (fpSchritt_laenge_verweigert f _ e)

/-- Closed OS vector state refuses the packed-integer step on the
    coherent machine projection (length and profile legs jointly). -/
theorem hwTor_vec_zustand_verweigert (m : HwMaschine) (c : Nat)
    (v : VectorDec)
    (h : vecEintritt (m.bereit c) = false) :
    stepExt (.vec v) (projFp m c) (m.bereit c) = .verweigert := by
  cases e : laengeOk v.laenge
  case true => exact hwTor_vec_verweigert v _ _ e h
  case false =>
    exact stepExt_vec_verweigert v _ _
      (stepVector_laenge_verweigert v _ _ e)

/-- Generic over all dispatcher families: a closed state leg refuses
    the unified step on the coherent machine projection. -/
theorem hwTor_verweigert_bei_zustand (m : HwMaschine) (c : Nat)
    (i : ExtInstr)
    (h : hwTorZustand m c i = false) :
    stepExt i (projFp m c) (m.bereit c) = .verweigert := by
  cases i with
  | pilot d =>
    simp [hwTorZustand] at h
  | narrow n =>
    simp [hwTorZustand] at h
  | muldiv q =>
    simp [hwTorZustand] at h
  | shift d =>
    simp [hwTorZustand] at h
  | setcc cnd dst l =>
    simp [hwTorZustand] at h
  | cmov cnd dst src l =>
    simp [hwTorZustand] at h
  | fp f =>
    simp only [hwTorZustand] at h
    exact hwTor_fp_zustand_verweigert m c f h
  | vec v =>
    simp only [hwTorZustand] at h
    exact hwTor_vec_zustand_verweigert m c v h

/-- An open gate needs an open state leg. -/
theorem hwTor_offen_braucht_zustand (m : HwMaschine) (c : Nat)
    (leaf1 : CpuOut) (xcrLo : BitVec 32) (i : ExtInstr)
    (h : hwTorOffen m c leaf1 xcrLo i = true) :
    hwTorZustand m c i = true := by
  unfold hwTorOffen at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

/-- An open gate needs an open profile leg. -/
theorem hwTor_offen_braucht_bereit (m : HwMaschine) (c : Nat)
    (leaf1 : CpuOut) (xcrLo : BitVec 32) (i : ExtInstr)
    (h : hwTorOffen m c leaf1 xcrLo i = true) :
    hwTorBereit m c i = true := by
  unfold hwTorOffen at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-! ## 3. Gated execution on the coherent machine.

  The family's event type plus a `HwAdapter` plug (register-path
  default, exactly the `adapterInteger666` discipline: memory forms
  must use the §3/§6 issue events of `HardwareExecution`, never this
  plug), and a gated step relation that embeds `HwSchritt` with an
  exact embedding theorem. A closed gate is the architectural #UD
  outcome (`ud` leg, self-loop, never a successor); an open gate
  with a memory-unchanged unified step is exactly `HwSchritt.reg`. -/

/-- Gated machine event: an admitted family step, or the #UD refusal
    of a form whose feature is absent. -/
inductive HwTorEreignis where
  | ausf : Nat → ExtInstr → HwTorEreignis
  | udTor : Nat → ExtInstr → ArchFehler → HwTorEreignis
  deriving DecidableEq, Repr

/-- The feature-gate plug: the accepted unified step where the whole
    gate is open, refusal otherwise. Register-path default only. -/
def adapterFeatureTor (leaf1 : CpuOut) (xcrLo : BitVec 32) :
    HwAdapter ExtInstr :=
  ⟨fun m c i =>
    match stepExt i (projFp m c) (m.bereit c) with
    | .weiter t' =>
      if hwTorOffen m c leaf1 xcrLo i then some (setKernVonFp m c t')
      else none
    | _ => none⟩

/-- A closed gate admits nothing through the plug. -/
theorem adapterFeatureTor_verweigert (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (m : HwMaschine) (c : Nat) (i : ExtInstr)
    (h : hwTorOffen m c leaf1 xcrLo i = false) :
    (adapterFeatureTor leaf1 xcrLo).schritt m c i = none := by
  unfold adapterFeatureTor
  cases hstep : stepExt i (projFp m c) (m.bereit c)
  case weiter t' =>
    simp [hstep, h]
  case halt =>
    simp [hstep]
  case verweigert =>
    simp [hstep]

/-- An open gate with a successful unified step is exactly the
    re-embedded successor: the old evaluator lifted, never redefined. -/
theorem adapterFeatureTor_weiter (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (m : HwMaschine) (c : Nat) (i : ExtInstr) (t' : FpZustand)
    (hstep : stepExt i (projFp m c) (m.bereit c) = .weiter t')
    (hoff : hwTorOffen m c leaf1 xcrLo i = true) :
    (adapterFeatureTor leaf1 xcrLo).schritt m c i
      = some (setKernVonFp m c t') := by
  unfold adapterFeatureTor
  simp only [hstep, hoff, if_true]

/-- Gated step relation: open gates execute through `HwSchritt`,
    closed gates refuse with #UD and change nothing. -/
inductive HwTorSchritt (leaf1 : CpuOut) (xcrLo : BitVec 32) :
    HwMaschine → HwMaschine → HwTorEreignis → Prop where
  | ok {m : HwMaschine} (c : Nat) (i : ExtInstr) (t' : FpZustand)
      (hoff : hwTorOffen m c leaf1 xcrLo i = true)
      (hstep : stepExt i (projFp m c) (m.bereit c) = .weiter t')
      (hmem : t'.kern.speicher = m.mem) :
      HwTorSchritt leaf1 xcrLo m (setKernVonFp m c t') (.ausf c i)
  | ud {m : HwMaschine} (c : Nat) (i : ExtInstr)
      (hzu : hwTorOffen m c leaf1 xcrLo i = false) :
      HwTorSchritt leaf1 xcrLo m m (.udTor c i .ud)

/-- Exact embedding: the admitted leg IS the coherent `reg` step. -/
theorem hwTorSchritt_ok_reg (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (m m' : HwMaschine) (c : Nat) (i : ExtInstr)
    (h : HwTorSchritt leaf1 xcrLo m m' (.ausf c i)) :
    HwSchritt m m' (.regAusf c i) := by
  cases h with
  | ok c i t' hoff hstep hmem => exact .reg c i t' hstep hmem

/-- Every gated step preserves well-formedness. -/
theorem hwTorSchritt_wf (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (m m' : HwMaschine) (e : HwTorEreignis)
    (h : HwTorSchritt leaf1 xcrLo m m' e) (hwf : HwWf m) :
    HwWf m' := by
  cases h with
  | ok c i t' hoff hstep hmem => exact setKernDaten_wf _ c _ hwf
  | ud c i hzu => exact hwf

/-- The admitted leg classifies no gate fault. -/
theorem hwTorSchritt_ok_kein_fehler (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (m m' : HwMaschine) (c : Nat)
    (i : ExtInstr)
    (h : HwTorSchritt leaf1 xcrLo m m' (.ausf c i)) :
    hwTorFehler m c leaf1 xcrLo i = none := by
  cases h with
  | ok c i t' hoff hstep hmem =>
    exact hwTorFehler_offen _ _ _ _ _ hoff

/-- The refused leg classifies #UD and changes no state. -/
theorem hwTorSchritt_ud_klasse (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (m m' : HwMaschine) (c : Nat) (i : ExtInstr)
    (h : HwTorSchritt leaf1 xcrLo m m' (.udTor c i .ud)) :
    hwTorFehler m c leaf1 xcrLo i = some .ud := by
  cases h with
  | ud c i hzu => exact hwTorFehler_ud _ _ _ _ _ hzu

/-! ## 4. Witness forms, refusal machines and gate equations.

  Concrete instances only: the canonical PXOR vector form and the
  register MOVSD scalar-FP form, the two-core witness start
  (`hwWitStart`: full silicon, OS vector state on), one refusal
  machine per closed leg (OS state off, FTZ control word, absent
  observed bit), and the TSO issue/drain states. Every equation is a
  closed Bool computation. -/

/-- Witness vector form: canonical PXOR, length 5. -/
def hwTorWitV : VectorDec := ⟨.pxorRR .xmm0 .xmm1, 5⟩

/-- Witness FP form: register MOVSD, length 4. -/
def hwTorWitF : FpDecodiert := ⟨.movsdRR .xmm0 .xmm1, 4⟩

/-- Witness vector successor: RIP + 5, destination lane-xored. -/
def hwTorWitT' : FpZustand :=
  { projFp hwWitStart 0 with
    kern := { (projFp hwWitStart 0).kern with
      rip := ripNach (projFp hwWitStart 0).kern.rip hwTorWitV.laenge }
    xmm := xmmSet (projFp hwWitStart 0).xmm .xmm0
      (vecXor .b64 ((projFp hwWitStart 0).xmm .xmm0)
        ((projFp hwWitStart 0).xmm .xmm1)) }

/-- Witness FP successor: RIP + 4, low double-word moved. -/
def hwTorWitU' : FpZustand :=
  { projFp hwWitStart 0 with
    kern := { (projFp hwWitStart 0).kern with
      rip := ripNach (projFp hwWitStart 0).kern.rip hwTorWitF.laenge }
    xmm := xmmSchreibeTief (projFp hwWitStart 0).xmm .xmm0
      (xmmTief (projFp hwWitStart 0).xmm .xmm1) }

/-- Refusal machine: OS vector state off, all else as the start. -/
def hwTorUnbereit : HwMaschine :=
  { hwWitStart with bereit := fun _ => ⟨0x1F80, false⟩ }

/-- Refusal machine: FTZ control word in core 0, all else as start. -/
def hwTorFtz : HwMaschine :=
  { hwWitStart with kerne := fun d =>
    if d = 0 then { hwWitKern 0 with fp := ⟨0x9F80⟩ } else hwWitKern d }

/-- Witness TSO issue state: core 0 holds byte 42 at the data cell. -/
def hwTorS1 : TSOZustand :=
  ⟨hwWitMem, fun d =>
    if d = 0 then [⟨hwWitAdr, BitVec.ofNat 8 42⟩] else []⟩

/-- Witness TSO drain state: the byte installed in shared memory. -/
def hwTorS2 : TSOZustand :=
  ⟨{ hwWitMem with bytes := fun x =>
      if x = hwWitAdr then BitVec.ofNat 8 42 else hwWitMem.bytes x },
   pufferSetze hwTorS1.puffer 0 []⟩

/-- The baseline admits the vector form under observed SSE2 + XMM. -/
theorem hwTor_basis_vec_offen :
    hwTorOffen hwWitStart 0 zeugeOut1 (BitVec.ofNat 32 0x6)
      (.vec hwTorWitV) = true := by
  decide

/-- The baseline admits the scalar-FP form under observed SSE2 + XMM. -/
theorem hwTor_basis_fp_offen :
    hwTorOffen hwWitStart 0 zeugeOut1 (BitVec.ofNat 32 0x6)
      (.fp hwTorWitF) = true := by
  decide

/-- Without OS vector state the vector gate is closed. -/
theorem hwTor_unbereit_vec_zu :
    hwTorOffen hwTorUnbereit 0 zeugeOut1 (BitVec.ofNat 32 0x6)
      (.vec hwTorWitV) = false := by
  decide

/-- Under the FTZ control word the scalar-FP gate is closed. -/
theorem hwTor_ftz_fp_zu :
    hwTorOffen hwTorFtz 0 zeugeOut1 (BitVec.ofNat 32 0x6)
      (.fp hwTorWitF) = false := by
  decide

/-- With no observed silicon bit the vector gate is closed. -/
theorem hwTor_ohne_bit_vec_zu :
    hwTorOffen hwWitStart 0 ⟨0, 0, 0, 0⟩ (BitVec.ofNat 32 0)
      (.vec hwTorWitV) = false := by
  decide

/-! ## 5. Executed steps, TSO facts and planted refusals.

  The admitted vector and scalar-FP steps run through the accepted
  evaluators (lifted, never redefined) with memory unchanged, so both
  embed as `HwSchritt.reg`. The TSO issue/drain states are exactly
  the accepted byte equations. Each refusal machine refuses its step
  and takes the #UD leg, changing nothing. -/

/-- The admitted vector step runs: destination lane-xored, RIP + 5. -/
theorem hwTorWit_vec_schritt :
    stepVector hwTorWitV (projFp hwWitStart 0) (hwWitStart.bereit 0)
      = some hwTorWitT' :=
  stepVector_pxor hwTorWitV _ _ .xmm0 .xmm1 (by decide) rfl rfl

/-- The admitted vector step is a unified success. -/
theorem hwTorWit_ext_vec :
    stepExt (.vec hwTorWitV) (projFp hwWitStart 0)
        (hwWitStart.bereit 0) = .weiter hwTorWitT' :=
  stepExt_vec hwTorWitV _ _ _ hwTorWit_vec_schritt

/-- The vector step leaves shared memory alone. -/
theorem hwTorWit_vec_mem :
    hwTorWitT'.kern.speicher = hwWitStart.mem := rfl

/-- The admitted FP step runs: low double-word moved, RIP + 4. -/
theorem hwTorWit_fp_schritt :
    fpSchritt hwTorWitF (projFp hwWitStart 0) = some hwTorWitU' :=
  fpSchritt_movsdRR hwTorWitF _ .xmm0 .xmm1 (by decide) rfl rfl

/-- The admitted FP step is a unified success. -/
theorem hwTorWit_ext_fp :
    stepExt (.fp hwTorWitF) (projFp hwWitStart 0)
        (hwWitStart.bereit 0) = .weiter hwTorWitU' :=
  stepExt_fp hwTorWitF _ _ _ hwTorWit_fp_schritt

/-- The FP step leaves shared memory alone. -/
theorem hwTorWit_fp_mem :
    hwTorWitU'.kern.speicher = hwWitStart.mem := rfl

/-- Core 0 issues byte 42 at the data cell. -/
theorem hwTor_issue :
    issueByte (tsoAnsicht hwWitStart) 0 hwWitAdr
        (BitVec.ofNat 8 42) = some hwTorS1 := rfl

/-- The data cell is readable on the witness start view. -/
theorem hwTor_hrd :
    (tsoAnsicht hwWitStart).mem.lesbar hwWitAdr = true := by
  decide

/-- Core 0 drains its oldest entry into shared memory. -/
theorem hwTor_flush : flushKern hwTorS1 0 = some hwTorS2 := rfl

/-- The issue buffer holds exactly the one entry. -/
theorem hwTor_buf :
    hwTorS1.puffer 0
      = ⟨hwWitAdr, BitVec.ofNat 8 42⟩ :: [] := rfl

/-- No foreign forwarding: core 1 still reads the old byte. -/
theorem hwTor_fremd_alt :
    loadByte hwTorS1 1 hwWitAdr = some (BitVec.ofNat 8 0) := by
  decide

/-- PLANTED REFUSAL: without OS vector state the vector step refuses. -/
theorem hwTor_unbereit_schritt :
    stepExt (.vec hwTorWitV) (projFp hwTorUnbereit 0)
        (hwTorUnbereit.bereit 0) = .verweigert :=
  hwTor_vec_zustand_verweigert _ _ _ rfl

/-- PLANTED REFUSAL: without OS vector state the gate takes #UD. -/
theorem hwTor_unbereit_ud :
    HwTorSchritt zeugeOut1 (BitVec.ofNat 32 0x6)
      hwTorUnbereit hwTorUnbereit
      (.udTor 0 (.vec hwTorWitV) .ud) :=
  .ud 0 _ hwTor_unbereit_vec_zu

/-- PLANTED REFUSAL: under FTZ the scalar-FP step refuses. -/
theorem hwTor_ftz_schritt :
    stepExt (.fp hwTorWitF) (projFp hwTorFtz 0)
        (hwTorFtz.bereit 0) = .verweigert :=
  hwTor_fp_zustand_verweigert _ _ _ rfl

/-- PLANTED REFUSAL: under FTZ the gate takes #UD. -/
theorem hwTor_ftz_ud :
    HwTorSchritt zeugeOut1 (BitVec.ofNat 32 0x6)
      hwTorFtz hwTorFtz
      (.udTor 0 (.fp hwTorWitF) .ud) :=
  .ud 0 _ hwTor_ftz_fp_zu

/-- PLANTED REFUSAL: with no observed bit the gate takes #UD. -/
theorem hwTor_ohne_bit_ud :
    HwTorSchritt ⟨0, 0, 0, 0⟩ (BitVec.ofNat 32 0)
      hwWitStart hwWitStart
      (.udTor 0 (.vec hwTorWitV) .ud) :=
  .ud 0 _ hwTor_ohne_bit_vec_zu

/-! ## 6. Two-core gating and the closing connection.

  One machine, two cores, one family: core 0 keeps OS vector state
  (gate open, the step executes), core 1 loses it (gate closed, the
  same form refuses with #UD). The closing theorem ties the admitted
  vector step, its exact `HwSchritt` embedding, well-formedness, the
  gate classification, the step-level fault silence and a full TSO
  issue/forward/drain leg into one conjunction. Every premise is used
  by the proof. -/

/-- Half-gated machine: core 1 without OS vector state, all else as
    the witness start. -/
def hwTorHalb : HwMaschine :=
  { hwWitStart with bereit := fun d =>
    if d = 1 then ⟨0x1F80, false⟩ else basisBereit }

/-- Core 0 of the half-gated machine admits the vector form. -/
theorem hwTor_halb_vec_0_offen :
    hwTorOffen hwTorHalb 0 zeugeOut1 (BitVec.ofNat 32 0x6)
      (.vec hwTorWitV) = true := by
  decide

/-- Core 1 of the half-gated machine refuses the vector form. -/
theorem hwTor_halb_vec_1_zu :
    hwTorOffen hwTorHalb 1 zeugeOut1 (BitVec.ofNat 32 0x6)
      (.vec hwTorWitV) = false := by
  decide

/-- Core 1 of the half-gated machine takes the #UD leg. -/
theorem hwTor_halb_ud_1 :
    HwTorSchritt zeugeOut1 (BitVec.ofNat 32 0x6)
      hwTorHalb hwTorHalb
      (.udTor 1 (.vec hwTorWitV) .ud) :=
  .ud 1 _ hwTor_halb_vec_1_zu

/-- Core 0 of the half-gated machine runs the admitted vector step:
    same core data and readiness as the witness start. -/
theorem hwTor_halb_vec_0_schritt :
    stepExt (.vec hwTorWitV) (projFp hwTorHalb 0)
        (hwTorHalb.bereit 0) = .weiter hwTorWitT' :=
  hwTorWit_ext_vec

/-- CLOSING: an admitted vector step on the coherent machine executes
    exactly as the coherent `reg` step, preserves well-formedness,
    classifies no gate fault and no step fault, and its TSO leg
    forwards to the owner and drains into shared memory. -/
theorem hwTor_verbindung
    (m : HwMaschine) (c : Nat) (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (v : VectorDec) (t' : FpZustand)
    (hoff : hwTorOffen m c leaf1 xcrLo (.vec v) = true)
    (hstep : stepExt (.vec v) (projFp m c) (m.bereit c)
      = .weiter t')
    (hmem : t'.kern.speicher = m.mem)
    (hwf : HwWf m)
    (s1 s2 : TSOZustand) (a : Adresse) (val : Byte)
    (hrd : (tsoAnsicht m).mem.lesbar a = true)
    (hissue : issueByte (tsoAnsicht m) c a val = some s1)
    (e : TSOEintrag) (hrest : List TSOEintrag)
    (hbuf : s1.puffer c = e :: hrest)
    (hflush : flushKern s1 c = some s2) :
    HwTorSchritt leaf1 xcrLo m (setKernVonFp m c t')
        (.ausf c (.vec v))
      ∧ HwSchritt m (setKernVonFp m c t') (.regAusf c (.vec v))
      ∧ loadByte s1 c a = some val
      ∧ s2.mem.bytes e.addr = e.wert
      ∧ HwWf (setKernVonFp m c t')
      ∧ hwTorFehler m c leaf1 xcrLo (.vec v) = none
      ∧ klassifiziereExt (stepExt (.vec v) (projFp m c)
        (m.bereit c)) = none := by
  have hok : HwTorSchritt leaf1 xcrLo m (setKernVonFp m c t')
      (.ausf c (.vec v)) := .ok c _ t' hoff hstep hmem
  refine ⟨hok, hwTorSchritt_ok_reg _ _ _ _ _ _ hok, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact load_nach_issue (tsoAnsicht m) s1 c a val hissue hrd
  · exact flush_schreibt_kopf s1 s2 c hflush e hrest hbuf
  · exact hwTorSchritt_wf _ _ _ _ _ hok hwf
  · exact hwTorSchritt_ok_kein_fehler _ _ _ _ _ _ hok
  · rw [hstep]
    rfl

/-! ## 7. Joint witness: admitted steps, two-core gating,
  memory-changing run, planted refusals.

  Every premise of `hwTor_verbindung` is instantiated jointly on the
  concrete reached run, plus the memory-change evidence, the
  owner-only foreign observation, the half-gated two-core fact (core 0
  executes the same form core 1 refuses with #UD), the scalar-FP
  admission and the planted state/observation refusals. Non-degenerate:
  two family steps execute, the TSO leg changes ACTUAL shared memory
  (0 becomes 42) with forwarding visible to the owner only, and three
  closed gates refuse with #UD. -/

/-- JOINT COMPANION WITNESS. -/
theorem hwTor_verbindung_zeuge :
    HwTorSchritt zeugeOut1 (BitVec.ofNat 32 0x6) hwWitStart
        (setKernVonFp hwWitStart 0 hwTorWitT')
        (.ausf 0 (.vec hwTorWitV))
      ∧ HwSchritt hwWitStart (setKernVonFp hwWitStart 0 hwTorWitT')
        (.regAusf 0 (.vec hwTorWitV))
      ∧ loadByte hwTorS1 0 hwWitAdr = some (BitVec.ofNat 8 42)
      ∧ hwTorS2.mem.bytes hwWitAdr = BitVec.ofNat 8 42
      ∧ HwWf (setKernVonFp hwWitStart 0 hwTorWitT')
      ∧ hwTorFehler hwWitStart 0 zeugeOut1 (BitVec.ofNat 32 0x6)
        (.vec hwTorWitV) = none
      ∧ klassifiziereExt (stepExt (.vec hwTorWitV)
        (projFp hwWitStart 0) (hwWitStart.bereit 0)) = none
      ∧ loadByte hwTorS1 1 hwWitAdr = some (BitVec.ofNat 8 0)
      ∧ hwWitMem.bytes hwWitAdr = BitVec.ofNat 8 0
      ∧ stepExt (.vec hwTorWitV) (projFp hwTorHalb 0)
        (hwTorHalb.bereit 0) = .weiter hwTorWitT'
      ∧ HwTorSchritt zeugeOut1 (BitVec.ofNat 32 0x6)
        hwTorHalb hwTorHalb (.udTor 1 (.vec hwTorWitV) .ud)
      ∧ stepExt (.vec hwTorWitV) (projFp hwTorUnbereit 0)
        (hwTorUnbereit.bereit 0) = .verweigert
      ∧ hwTorFehler hwTorUnbereit 0 zeugeOut1 (BitVec.ofNat 32 0x6)
        (.vec hwTorWitV) = some .ud
      ∧ stepExt (.fp hwTorWitF) (projFp hwWitStart 0)
        (hwWitStart.bereit 0) = .weiter hwTorWitU'
      ∧ hwTorOffen hwWitStart 0 zeugeOut1 (BitVec.ofNat 32 0x6)
        (.fp hwTorWitF) = true := by
  have hmain := hwTor_verbindung hwWitStart 0 zeugeOut1
    (BitVec.ofNat 32 0x6) hwTorWitV hwTorWitT' hwTor_basis_vec_offen
    hwTorWit_ext_vec hwTorWit_vec_mem hwWitStart_wf hwTorS1 hwTorS2
    hwWitAdr (BitVec.ofNat 8 42) hwTor_hrd hwTor_issue
    ⟨hwWitAdr, BitVec.ofNat 8 42⟩ [] hwTor_buf hwTor_flush
  obtain ⟨hok, hreg, hfwd, hdrain, hwf', hkein, hklass⟩ := hmain
  refine ⟨hok, hreg, hfwd, hdrain, hwf', hkein, hklass,
    hwTor_fremd_alt, hwWit_anfang_null, hwTor_halb_vec_0_schritt,
    hwTor_halb_ud_1, hwTor_unbereit_schritt, ?_, hwTorWit_ext_fp,
    hwTor_basis_fp_offen⟩
  exact hwTorSchritt_ud_klasse _ _ _ _ _ _ hwTor_unbereit_ud

/- CUTS: what is not proved here.

  Proved here (every accepted definition reused unchanged, never
  copied: `HwMaschine`/`HwSchritt`/`HwWf`/`HwAdapter`/`projFp`/
  `setKernVonFp`, `stepExt`/`ExtInstr`, `stepVector`/`fpSchritt`,
  `merkmalZugelassen`/`beobachtungsTor`, `issueByte`/`loadByte`/
  `flushKern` with `load_nach_issue`/`flush_schreibt_kopf`,
  `ArchFehler` with `klassifiziereExt`, `zeugeOut1`, `hwWitStart`):
  - the feature-row mapping per dispatcher family (§1);
  - generic refusal: a closed state leg refuses EVERY admitted family
    step on the coherent projection, proved by case split over the
    dispatcher (not per example), with the `m.bereit c` profile leg
    for the vector arm under present silicon (§2);
  - the gate fault classifier (closed = architectural #UD, open = no
    fault), the `HwAdapter` plug with refusal/admission equations, the
    gated relation with exact `HwSchritt.reg` embedding and
    well-formedness preservation (§3);
  - gate equations, executed vector + scalar-FP steps with unchanged
    memory, TSO issue/drain facts and planted refusals per closed leg
    (OS state, FTZ word, absent observed bit) (§§4-5);
  - half-gated two-core gating and the closing connection with its
    joint non-degenerate witness (§§6-7).
  Silicon and provenance (checked against the clone-local snapshot
  `.tmp/HARDWARE-REFERENCES/`, REFERENCES.json sha256
  `a4a62e6a7ba11a76c7753a195b825087306812aac39b930973f9168ee599f321`,
  Intel SDM 325462-093US September 2026; no AMD snapshot exists and no
  vendor-difference, timing or physical-silicon claim is made):
  - no NEW hardware definition is introduced, so no new definition
    could be silicon-wrong: every encoding, bit position, length and
    fault class is the accepted producer's, with provenance in its
    CUTS. The gate-closed to `ArchFehler.ud` mapping reuses the
    accepted architectural #UD class for disabled-feature execution;
    step-level refusal stays `klassifiziereExt`-silent (reused
    `stepExt_verweigert_kein_de`), exactly as `HardwareFaults` demands.
  NOT proved here, and not claimed:
  - the scalar-FP `BereitProfil` leg and the CPUID-observation leg are
    wrapper-enforced (`HwTorSchritt`/`adapterFeatureTor` refuse), not
    step-enforced: the accepted FP step does not read `BereitProfil`
    and no accepted step reads CPUID answers;
  - silicon-absent profile refusal (feature bit off in `HwProfil`)
    likewise refuses only through the wrapper, never through `stepExt`;
  - memory-touching family forms (e.g. FP stores) cannot use the
    register plug: they must use the §3/§6 issue events of
    `HardwareExecution` (same discipline as `adapterInteger666`);
  - no source/checker/emitter correspondence, no per-access target to
    W/GX simulation, no whole-word atomicity beyond the reused TSO
    byte equations, no image/loader/entry/budget link.
-/

#print axioms hwTorMerkmal
#print axioms hwTorMerkmal_pilot
#print axioms hwTorFehler_offen
#print axioms hwTorFehler_ud
#print axioms hwTor_vec_verweigert
#print axioms hwTor_fp_verweigert
#print axioms hwTor_vec_bereit_verweigert
#print axioms hwTor_fp_zustand_verweigert
#print axioms hwTor_vec_zustand_verweigert
#print axioms hwTor_verweigert_bei_zustand
#print axioms hwTor_offen_braucht_zustand
#print axioms hwTor_offen_braucht_bereit
#print axioms adapterFeatureTor_verweigert
#print axioms adapterFeatureTor_weiter
#print axioms hwTorSchritt_ok_reg
#print axioms hwTorSchritt_wf
#print axioms hwTorSchritt_ok_kein_fehler
#print axioms hwTorSchritt_ud_klasse
#print axioms hwTor_basis_vec_offen
#print axioms hwTor_basis_fp_offen
#print axioms hwTor_unbereit_vec_zu
#print axioms hwTor_ftz_fp_zu
#print axioms hwTor_ohne_bit_vec_zu
#print axioms hwTorWit_vec_schritt
#print axioms hwTorWit_ext_vec
#print axioms hwTorWit_vec_mem
#print axioms hwTorWit_fp_schritt
#print axioms hwTorWit_ext_fp
#print axioms hwTorWit_fp_mem
#print axioms hwTor_issue
#print axioms hwTor_hrd
#print axioms hwTor_flush
#print axioms hwTor_buf
#print axioms hwTor_fremd_alt
#print axioms hwTor_unbereit_schritt
#print axioms hwTor_unbereit_ud
#print axioms hwTor_ftz_schritt
#print axioms hwTor_ftz_ud
#print axioms hwTor_ohne_bit_ud
#print axioms hwTor_halb_vec_0_offen
#print axioms hwTor_halb_vec_1_zu
#print axioms hwTor_halb_ud_1
#print axioms hwTor_halb_vec_0_schritt
#print axioms hwTor_verbindung
#print axioms hwTor_verbindung_zeuge

end Gabbro.Grammatik.X86
