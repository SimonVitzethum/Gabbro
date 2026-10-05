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
import Grammatik.X86.HardwareExecution
import Grammatik.X86.HardwareFaults
import Grammatik.X86.ComposeFeatureGate

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

/- CUTS:
   Skeleton only: the feature-row mapping. Gate predicates, generic
   refusal over all dispatcher families, the #UD classification, the
   adapter/embedding, planted refusals and the joint witness are OPEN.
-/

#print axioms hwTorMerkmal

end Gabbro.Grammatik.X86
