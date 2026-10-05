/-
  File:      Grammatik/X86/HwFeatureStep.lean
  Subject:   Feature gating enforced per step, not by wrapper.

  Lane 1183 (follow-up of lane 1135 `HwFeatureGates`): the scalar-FP
  `BereitProfil` leg, the CPUID-observation leg and the silicon-absent
  refusal are enforced by a wrapper (`HwTorSchritt`), not by the steps.
  This file adds the step-level statement `stepExtTor`, which reads
  `BereitProfil`/CPUID answers (lifting, never editing, the accepted
  steps), and proves wrapper and step-level versions agree.
-/
import Grammatik.X86.HwFeatureGates

namespace Gabbro.Grammatik.X86

/-! ## 1. Step-level gated evaluator.

  The accepted unified step `stepExt`, gated per step by the whole
  `hwTorOffen` conjunction (profile, state, observation). -/

/-- Step-level gate: the accepted step where the whole gate is open,
    refusal otherwise. The accepted evaluators are lifted, never edited. -/
def stepExtTor (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (i : ExtInstr) : ExtAusgang :=
  if hwTorOffen m c leaf1 xcrLo i then stepExt i (projFp m c) (m.bereit c)
  else .verweigert

/-- An open gate runs the accepted step. -/
theorem stepExtTor_offen (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (i : ExtInstr) (t' : FpZustand)
    (hoff : hwTorOffen m c leaf1 xcrLo i = true)
    (hstep : stepExt i (projFp m c) (m.bereit c) = .weiter t') :
    stepExtTor m c leaf1 xcrLo i = .weiter t' := by
  simp [stepExtTor, hoff, hstep]

/-- A closed gate refuses at step level. -/
theorem stepExtTor_zu (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (i : ExtInstr)
    (hzu : hwTorOffen m c leaf1 xcrLo i = false) :
    stepExtTor m c leaf1 xcrLo i = .verweigert := by
  simp [stepExtTor, hzu]

/-- A step-level success has an open gate. -/
theorem stepTor_weiter_offen (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (i : ExtInstr) (t' : FpZustand)
    (h : stepExtTor m c leaf1 xcrLo i = .weiter t') :
    hwTorOffen m c leaf1 xcrLo i = true := by
  unfold stepExtTor at h
  cases hgate : hwTorOffen m c leaf1 xcrLo i with
  | true => rfl
  | false => simp [hgate] at h

/-- A step-level success IS the accepted step success. -/
theorem stepTor_weiter_schritt (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (i : ExtInstr) (t' : FpZustand)
    (h : stepExtTor m c leaf1 xcrLo i = .weiter t') :
    stepExt i (projFp m c) (m.bereit c) = .weiter t' := by
  unfold stepExtTor at h
  cases hgate : hwTorOffen m c leaf1 xcrLo i with
  | true =>
    simp [hgate] at h
    exact h
  | false => simp [hgate] at h

/-! ## 2. Wrapper agreement: `HwTorSchritt`/`adapterFeatureTor` coincide
  with the step-level gate. -/

/-- Step-level success admits through the wrapper plug. -/
theorem stepTor_adapter_weiter (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (i : ExtInstr) (t' : FpZustand)
    (h : stepExtTor m c leaf1 xcrLo i = .weiter t') :
    (adapterFeatureTor leaf1 xcrLo).schritt m c i
      = some (setKernVonFp m c t') := by
  have hoff := stepTor_weiter_offen m c leaf1 xcrLo i t' h
  have hstep := stepTor_weiter_schritt m c leaf1 xcrLo i t' h
  exact adapterFeatureTor_weiter leaf1 xcrLo m c i t' hstep hoff

/-- Step-level refusal admits nothing through the wrapper plug. -/
theorem stepTor_adapter_verweigert (m : HwMaschine) (c : Nat)
    (leaf1 : CpuOut) (xcrLo : BitVec 32) (i : ExtInstr)
    (h : stepExtTor m c leaf1 xcrLo i = .verweigert) :
    (adapterFeatureTor leaf1 xcrLo).schritt m c i = none := by
  cases hgate : hwTorOffen m c leaf1 xcrLo i with
  | true =>
    have hstep : stepExt i (projFp m c) (m.bereit c) = .verweigert := by
      have heq : stepExtTor m c leaf1 xcrLo i
          = stepExt i (projFp m c) (m.bereit c) := by
        simp [stepExtTor, hgate]
      rw [heq] at h
      exact h
    unfold adapterFeatureTor
    cases h2 : stepExt i (projFp m c) (m.bereit c) with
    | weiter t' =>
      rw [hstep] at h2
      cases h2
    | halt => simp [h2]
    | verweigert => simp [h2]
  | false =>
    exact adapterFeatureTor_verweigert leaf1 xcrLo m c i hgate

/-- Step-level trap admits nothing through the wrapper plug. -/
theorem stepTor_adapter_halt (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (i : ExtInstr)
    (h : stepExtTor m c leaf1 xcrLo i = .halt) :
    (adapterFeatureTor leaf1 xcrLo).schritt m c i = none := by
  cases hgate : hwTorOffen m c leaf1 xcrLo i with
  | true =>
    have hstep : stepExt i (projFp m c) (m.bereit c) = .halt := by
      have heq : stepExtTor m c leaf1 xcrLo i
          = stepExt i (projFp m c) (m.bereit c) := by
        simp [stepExtTor, hgate]
      rw [heq] at h
      exact h
    unfold adapterFeatureTor
    cases h2 : stepExt i (projFp m c) (m.bereit c) with
    | weiter t' =>
      rw [hstep] at h2
      cases h2
    | halt => simp [h2]
    | verweigert => simp [h2]
  | false =>
    exact adapterFeatureTor_verweigert leaf1 xcrLo m c i hgate

/-- The admitted wrapper leg IS the step-level success. -/
theorem hwStepTor_ok_iff (m m' : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (i : ExtInstr) :
    HwTorSchritt leaf1 xcrLo m m' (.ausf c i) ↔
      ∃ t' : FpZustand, m' = setKernVonFp m c t' ∧
        stepExtTor m c leaf1 xcrLo i = .weiter t' ∧
        t'.kern.speicher = m.mem := by
  constructor
  · intro h
    cases h with
    | ok c i t' hoff hstep hmem =>
      exact ⟨t', rfl, stepExtTor_offen m c leaf1 xcrLo i t' hoff hstep,
        hmem⟩
  · intro h
    obtain ⟨t', hm', hstep, hmem⟩ := h
    have hoff := stepTor_weiter_offen m c leaf1 xcrLo i t' hstep
    have hst := stepTor_weiter_schritt m c leaf1 xcrLo i t' hstep
    rw [hm']
    exact .ok c i t' hoff hst hmem

/-- The refused wrapper leg IS the closed step-level gate. -/
theorem hwStepTor_ud_iff (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (i : ExtInstr) :
    HwTorSchritt leaf1 xcrLo m m (.udTor c i .ud) ↔
      hwTorOffen m c leaf1 xcrLo i = false := by
  constructor
  · intro h
    have hklasse := hwTorSchritt_ud_klasse leaf1 xcrLo m m c i h
    unfold hwTorFehler at hklasse
    cases hgate : hwTorOffen m c leaf1 xcrLo i with
    | true => simp [hgate] at hklasse
    | false => rfl
  · intro hzu
    exact .ud c i hzu

/-! ## 3. Exact agreement with the accepted evaluators.

  The old evaluators are lifted, never redefined: an accepted
  `fpSchritt`/`stepVector` success under an open gate IS the step-level
  success, and a step-level FP/vector success IS the accepted success. -/

/-- An accepted scalar-FP success under an open gate is step-level. -/
theorem stepTor_fp_lift (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (f : FpDecodiert) (t' : FpZustand)
    (hoff : hwTorOffen m c leaf1 xcrLo (.fp f) = true)
    (h : fpSchritt f (projFp m c) = some t') :
    stepExtTor m c leaf1 xcrLo (.fp f) = .weiter t' :=
  stepExtTor_offen m c leaf1 xcrLo (.fp f) t' hoff
    (stepExt_fp f _ t' _ h)

/-- An accepted vector success under an open gate is step-level. -/
theorem stepTor_vec_lift (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (v : VectorDec) (t' : FpZustand)
    (hoff : hwTorOffen m c leaf1 xcrLo (.vec v) = true)
    (h : stepVector v (projFp m c) (m.bereit c) = some t') :
    stepExtTor m c leaf1 xcrLo (.vec v) = .weiter t' :=
  stepExtTor_offen m c leaf1 xcrLo (.vec v) t' hoff
    (stepExt_vec v _ t' _ h)

/-- A step-level FP success IS the accepted `fpSchritt` success. -/
theorem stepTor_fp_aus_fpSchritt (m : HwMaschine) (c : Nat)
    (leaf1 : CpuOut) (xcrLo : BitVec 32) (f : FpDecodiert)
    (t' : FpZustand)
    (h : stepExtTor m c leaf1 xcrLo (.fp f) = .weiter t') :
    fpSchritt f (projFp m c) = some t' := by
  have hst : stepExt (.fp f) (projFp m c) (m.bereit c) = .weiter t' :=
    stepTor_weiter_schritt m c leaf1 xcrLo (.fp f) t' h
  cases hfp : fpSchritt f (projFp m c) with
  | some t'' =>
    have e := stepExt_fp f (projFp m c) t'' (m.bereit c) hfp
    rw [e] at hst
    cases hst
    rfl
  | none =>
    have e := stepExt_fp_verweigert f (projFp m c) (m.bereit c) hfp
    rw [e] at hst
    cases hst

/-- A step-level vector success IS the accepted `stepVector` success. -/
theorem stepTor_vec_aus_stepVector (m : HwMaschine) (c : Nat)
    (leaf1 : CpuOut) (xcrLo : BitVec 32) (v : VectorDec)
    (t' : FpZustand)
    (h : stepExtTor m c leaf1 xcrLo (.vec v) = .weiter t') :
    stepVector v (projFp m c) (m.bereit c) = some t' := by
  have hst : stepExt (.vec v) (projFp m c) (m.bereit c) = .weiter t' :=
    stepTor_weiter_schritt m c leaf1 xcrLo (.vec v) t' h
  cases hvec : stepVector v (projFp m c) (m.bereit c) with
  | some t'' =>
    have e := stepExt_vec v (projFp m c) t'' (m.bereit c) hvec
    rw [e] at hst
    cases hst
    rfl
  | none =>
    have e := stepExt_vec_verweigert v (projFp m c) (m.bereit c) hvec
    rw [e] at hst
    cases hst

/-! ## 4. Findings: which accepted steps ignore the profile.

  FINDING (proved below, one theorem per family): six of the eight
  dispatcher families never read `BereitProfil` at all -- the accepted
  `stepExt` arm ignores its `b` argument -- and the scalar-FP arm
  ignores it as well (`fpSchritt` takes no profile). Only the packed-
  integer arm reads it (`vecEintritt`). No accepted arm reads CPUID/XCR0
  answers (`stepExt` takes no `CpuOut`/XCR0 argument); the observation
  leg lives only in the wrapper and in `stepExtTor` above. For the six
  families with `hwTorMerkmal = none` the step-level gate is always
  open, so the wrapper adds nothing for them. -/

/-- FINDING F1a: the pilot gate is always open (no feature bit). -/
theorem hwStepTor_offen_pilot (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (d : Decodiert) :
    hwTorOffen m c leaf1 xcrLo (.pilot d) = true := by
  simp [hwTorOffen, hwTorBereit, hwTorZustand, hwTorBeobachtet,
    hwTorMerkmal_pilot]

/-- FINDING F1b: the narrow gate is always open (no feature bit). -/
theorem hwStepTor_offen_narrow (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (n : NarrowDec) :
    hwTorOffen m c leaf1 xcrLo (.narrow n) = true := by
  simp [hwTorOffen, hwTorBereit, hwTorZustand, hwTorBeobachtet,
    hwTorMerkmal]

/-- FINDING F1c: the multiply/divide gate is always open. -/
theorem hwStepTor_offen_muldiv (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (q : MulDivDecodiert) :
    hwTorOffen m c leaf1 xcrLo (.muldiv q) = true := by
  simp [hwTorOffen, hwTorBereit, hwTorZustand, hwTorBeobachtet,
    hwTorMerkmal]

/-- FINDING F1d: the shift gate is always open (no feature bit). -/
theorem hwStepTor_offen_shift (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (d : ShiftDecodiert) :
    hwTorOffen m c leaf1 xcrLo (.shift d) = true := by
  simp [hwTorOffen, hwTorBereit, hwTorZustand, hwTorBeobachtet,
    hwTorMerkmal]

/-- FINDING F1e: the SETcc gate is always open (no feature bit). -/
theorem hwStepTor_offen_setcc (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (cnd : Bedingung) (dst : Register) (l : Nat) :
    hwTorOffen m c leaf1 xcrLo (.setcc cnd dst l) = true := by
  simp [hwTorOffen, hwTorBereit, hwTorZustand, hwTorBeobachtet,
    hwTorMerkmal]

/-- FINDING F1f: the CMOVcc gate is always open (no feature bit). -/
theorem hwStepTor_offen_cmov (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (cnd : Bedingung) (dst src : Register)
    (l : Nat) :
    hwTorOffen m c leaf1 xcrLo (.cmov cnd dst src l) = true := by
  simp [hwTorOffen, hwTorBereit, hwTorZustand, hwTorBeobachtet,
    hwTorMerkmal]

/-- The pilot step-level gate adds nothing: it IS the accepted step. -/
theorem stepTor_pilot_ohne_beobachtung (m : HwMaschine) (c : Nat)
    (leaf1 : CpuOut) (xcrLo : BitVec 32) (d : Decodiert) :
    stepExtTor m c leaf1 xcrLo (.pilot d)
      = stepExt (.pilot d) (projFp m c) (m.bereit c) := by
  have hoff := hwStepTor_offen_pilot m c leaf1 xcrLo d
  simp [stepExtTor, hoff]

/-- The narrow step-level gate adds nothing. -/
theorem stepTor_narrow_ohne_beobachtung (m : HwMaschine) (c : Nat)
    (leaf1 : CpuOut) (xcrLo : BitVec 32) (n : NarrowDec) :
    stepExtTor m c leaf1 xcrLo (.narrow n)
      = stepExt (.narrow n) (projFp m c) (m.bereit c) := by
  have hoff := hwStepTor_offen_narrow m c leaf1 xcrLo n
  simp [stepExtTor, hoff]

/-- The multiply/divide step-level gate adds nothing. -/
theorem stepTor_muldiv_ohne_beobachtung (m : HwMaschine) (c : Nat)
    (leaf1 : CpuOut) (xcrLo : BitVec 32) (q : MulDivDecodiert) :
    stepExtTor m c leaf1 xcrLo (.muldiv q)
      = stepExt (.muldiv q) (projFp m c) (m.bereit c) := by
  have hoff := hwStepTor_offen_muldiv m c leaf1 xcrLo q
  simp [stepExtTor, hoff]

/-- The shift step-level gate adds nothing. -/
theorem stepTor_shift_ohne_beobachtung (m : HwMaschine) (c : Nat)
    (leaf1 : CpuOut) (xcrLo : BitVec 32) (d : ShiftDecodiert) :
    stepExtTor m c leaf1 xcrLo (.shift d)
      = stepExt (.shift d) (projFp m c) (m.bereit c) := by
  have hoff := hwStepTor_offen_shift m c leaf1 xcrLo d
  simp [stepExtTor, hoff]

/-- The SETcc step-level gate adds nothing. -/
theorem stepTor_setcc_ohne_beobachtung (m : HwMaschine) (c : Nat)
    (leaf1 : CpuOut) (xcrLo : BitVec 32) (cnd : Bedingung)
    (dst : Register) (l : Nat) :
    stepExtTor m c leaf1 xcrLo (.setcc cnd dst l)
      = stepExt (.setcc cnd dst l) (projFp m c) (m.bereit c) := by
  have hoff := hwStepTor_offen_setcc m c leaf1 xcrLo cnd dst l
  simp [stepExtTor, hoff]

/-- The CMOVcc step-level gate adds nothing. -/
theorem stepTor_cmov_ohne_beobachtung (m : HwMaschine) (c : Nat)
    (leaf1 : CpuOut) (xcrLo : BitVec 32) (cnd : Bedingung)
    (dst src : Register) (l : Nat) :
    stepExtTor m c leaf1 xcrLo (.cmov cnd dst src l)
      = stepExt (.cmov cnd dst src l) (projFp m c) (m.bereit c) := by
  have hoff := hwStepTor_offen_cmov m c leaf1 xcrLo cnd dst src l
  simp [stepExtTor, hoff]

/-- FINDING F2a: the accepted pilot step never reads the profile. -/
theorem stepTor_pilot_ignoriert_bereit (d : Decodiert) (t : FpZustand)
    (b1 b2 : BereitProfil) :
    stepExt (.pilot d) t b1 = stepExt (.pilot d) t b2 := by
  cases h1 : laufAlt d t with
  | some t' =>
    rw [stepExt_pilot d t t' b1 h1, stepExt_pilot d t t' b2 h1]
  | none =>
    rw [stepExt_pilot_verweigert d t b1 h1,
      stepExt_pilot_verweigert d t b2 h1]

/-- FINDING F2b: the accepted narrow step never reads the profile. -/
theorem stepTor_narrow_ignoriert_bereit (n : NarrowDec) (t : FpZustand)
    (b1 b2 : BereitProfil) :
    stepExt (.narrow n) t b1 = stepExt (.narrow n) t b2 := by
  cases h1 : stepNarrow n t.kern with
  | some s' =>
    rw [stepExt_narrow n t b1 s' h1, stepExt_narrow n t b2 s' h1]
  | none =>
    rw [stepExt_narrow_verweigert n t b1 h1,
      stepExt_narrow_verweigert n t b2 h1]

/-- FINDING F2c: the accepted multiply/divide step never reads it. -/
theorem stepTor_muldiv_ignoriert_bereit (q : MulDivDecodiert)
    (t : FpZustand) (b1 b2 : BereitProfil) :
    stepExt (.muldiv q) t b1 = stepExt (.muldiv q) t b2 := by
  cases h1 : mulDivSchritt q t.kern with
  | ok s' =>
    rw [stepExt_muldiv_ok q t b1 s' h1, stepExt_muldiv_ok q t b2 s' h1]
  | hardwareHalt =>
    rw [stepExt_muldiv_halt q t b1 h1, stepExt_muldiv_halt q t b2 h1]
  | misslungen =>
    rw [stepExt_muldiv_misslungen q t b1 h1,
      stepExt_muldiv_misslungen q t b2 h1]

/-- FINDING F2d: the accepted shift step never reads the profile. -/
theorem stepTor_shift_ignoriert_bereit (d : ShiftDecodiert)
    (t : FpZustand) (b1 b2 : BereitProfil) :
    stepExt (.shift d) t b1 = stepExt (.shift d) t b2 := by
  cases h1 : shiftSchritt d t.kern with
  | some s' =>
    rw [stepExt_shift d t b1 s' h1, stepExt_shift d t b2 s' h1]
  | none =>
    rw [stepExt_shift_verweigert d t b1 h1,
      stepExt_shift_verweigert d t b2 h1]

/-- FINDING F2e: the accepted SETcc step never reads the profile. -/
theorem stepTor_setcc_ignoriert_bereit (cnd : Bedingung) (dst : Register)
    (l : Nat) (t : FpZustand) (b1 b2 : BereitProfil) :
    stepExt (.setcc cnd dst l) t b1
      = stepExt (.setcc cnd dst l) t b2 := by
  cases h1 : setccSchrittBytes l t.kern dst cnd with
  | some s' =>
    rw [stepExt_setcc cnd dst l t b1 s' h1,
      stepExt_setcc cnd dst l t b2 s' h1]
  | none =>
    rw [stepExt_setcc_verweigert cnd dst l t b1 h1,
      stepExt_setcc_verweigert cnd dst l t b2 h1]

/-- FINDING F2f: the accepted CMOVcc step never reads the profile. -/
theorem stepTor_cmov_ignoriert_bereit (cnd : Bedingung) (dst src : Register)
    (l : Nat) (t : FpZustand) (b1 b2 : BereitProfil) :
    stepExt (.cmov cnd dst src l) t b1
      = stepExt (.cmov cnd dst src l) t b2 := by
  cases h1 : cmovSchrittBytes l t.kern dst src cnd with
  | some s' =>
    rw [stepExt_cmov cnd dst src l t b1 s' h1,
      stepExt_cmov cnd dst src l t b2 s' h1]
  | none =>
    rw [stepExt_cmov_verweigert cnd dst src l t b1 h1,
      stepExt_cmov_verweigert cnd dst src l t b2 h1]

/-- FINDING F2g: the accepted scalar-FP step never reads `BereitProfil`
    (`fpSchritt` takes no profile argument). -/
theorem stepTor_fp_ignoriert_bereit (f : FpDecodiert) (t : FpZustand)
    (b1 b2 : BereitProfil) :
    stepExt (.fp f) t b1 = stepExt (.fp f) t b2 := by
  cases h1 : fpSchritt f t with
  | some t' =>
    rw [stepExt_fp f t t' b1 h1, stepExt_fp f t t' b2 h1]
  | none =>
    rw [stepExt_fp_verweigert f t b1 h1,
      stepExt_fp_verweigert f t b2 h1]

/-- The packed-integer arm is the exception: it DOES read the profile.
    With OS vector state the witness vector step succeeds; without it
    the same form refuses. -/
theorem stepTor_vec_beachtet_bereit :
    stepExt (.vec hwTorWitV) (projFp hwWitStart 0) (hwWitStart.bereit 0)
      ≠ stepExt (.vec hwTorWitV) (projFp hwWitStart 0)
        ⟨0x1F80, false⟩ := by
  have h1 := hwTorWit_ext_vec
  have h2 : stepExt (.vec hwTorWitV) (projFp hwWitStart 0)
      ⟨0x1F80, false⟩ = .verweigert := by
    apply stepExt_vec_verweigert
    apply stepVector_profil_verweigert
    · rfl
    · rfl
  rw [h1, h2]
  intro h
  cases h

/-- FINDING F3: the step-level scalar-FP gate DOES read the observed
    CPUID/XCR0 answers (which no accepted step reads): under observed
    SSE2 + XMM the witness FP step runs, under zero answers the same
    form refuses at step level. -/
theorem stepTor_fp_beobachtet_haengt_ab :
    stepExtTor hwWitStart 0 zeugeOut1 (BitVec.ofNat 32 0x6)
        (.fp hwTorWitF)
      ≠ stepExtTor hwWitStart 0 ⟨0, 0, 0, 0⟩ (BitVec.ofNat 32 0)
        (.fp hwTorWitF) := by
  have h1 : stepExtTor hwWitStart 0 zeugeOut1 (BitVec.ofNat 32 0x6)
      (.fp hwTorWitF) = .weiter hwTorWitU' :=
    stepExtTor_offen _ _ _ _ _ _ hwTor_basis_fp_offen hwTorWit_ext_fp
  have hzu : hwTorOffen hwWitStart 0 ⟨0, 0, 0, 0⟩ (BitVec.ofNat 32 0)
      (.fp hwTorWitF) = false := by
    decide
  have h2 : stepExtTor hwWitStart 0 ⟨0, 0, 0, 0⟩ (BitVec.ofNat 32 0)
      (.fp hwTorWitF) = .verweigert :=
    stepExtTor_zu _ _ _ _ _ hzu
  rw [h1, h2]
  intro h
  cases h

/-! ## 5. Well-formedness through the step level, concrete equations,
  planted refusals and the closing connection. -/

/-- Every step-level success preserves well-formedness (via the
    wrapper agreement: the step evidence builds the wrapper leg). -/
theorem hwStepTor_wf (m : HwMaschine) (c : Nat) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (i : ExtInstr) (t' : FpZustand)
    (hstep : stepExtTor m c leaf1 xcrLo i = .weiter t')
    (hmem : t'.kern.speicher = m.mem) (hwf : HwWf m) :
    HwWf (setKernVonFp m c t') := by
  have hoff := stepTor_weiter_offen m c leaf1 xcrLo i t' hstep
  have hst := stepTor_weiter_schritt m c leaf1 xcrLo i t' hstep
  exact hwTorSchritt_wf leaf1 xcrLo m (setKernVonFp m c t')
    (.ausf c i) (.ok c i t' hoff hst hmem) hwf

/-- The admitted vector step at step level: RIP + 5, lane-xored. -/
theorem hwStepTor_wit_vec :
    stepExtTor hwWitStart 0 zeugeOut1 (BitVec.ofNat 32 0x6)
      (.vec hwTorWitV) = .weiter hwTorWitT' :=
  stepExtTor_offen _ _ _ _ _ _ hwTor_basis_vec_offen hwTorWit_ext_vec

/-- Core 0 of the half-gated machine runs at step level. -/
theorem hwStepTor_halb_0 :
    stepExtTor hwTorHalb 0 zeugeOut1 (BitVec.ofNat 32 0x6)
      (.vec hwTorWitV) = .weiter hwTorWitT' :=
  stepExtTor_offen _ _ _ _ _ _ hwTor_halb_vec_0_offen
    hwTor_halb_vec_0_schritt

/-- Core 1 of the half-gated machine refuses at step level. -/
theorem hwStepTor_halb_1 :
    stepExtTor hwTorHalb 1 zeugeOut1 (BitVec.ofNat 32 0x6)
      (.vec hwTorWitV) = .verweigert :=
  stepExtTor_zu _ _ _ _ _ hwTor_halb_vec_1_zu

/-- PLANTED REFUSAL at step level: without OS vector state. -/
theorem hwStepTor_unbereit :
    stepExtTor hwTorUnbereit 0 zeugeOut1 (BitVec.ofNat 32 0x6)
      (.vec hwTorWitV) = .verweigert :=
  stepExtTor_zu _ _ _ _ _ hwTor_unbereit_vec_zu

/-- PLANTED REFUSAL at step level: under the FTZ control word. -/
theorem hwStepTor_ftz :
    stepExtTor hwTorFtz 0 zeugeOut1 (BitVec.ofNat 32 0x6)
      (.fp hwTorWitF) = .verweigert :=
  stepExtTor_zu _ _ _ _ _ hwTor_ftz_fp_zu

/-- PLANTED REFUSAL at step level: with no observed silicon bit. -/
theorem hwStepTor_ohne_bit :
    stepExtTor hwWitStart 0 ⟨0, 0, 0, 0⟩ (BitVec.ofNat 32 0)
      (.vec hwTorWitV) = .verweigert :=
  stepExtTor_zu _ _ _ _ _ hwTor_ohne_bit_vec_zu

/-- Silicon-absent machine: full readiness, but the packed-integer
    feature bit off in silicon. -/
def hwStepTorOhneSilizium : HwMaschine :=
  { hwWitStart with hw := ⟨true, true, true, false⟩ }

/-- FINDING F4: absent silicon closes the step-level gate even under
    full readiness -- enforced per step here, wrapper-only in 1135. -/
theorem hwStepTor_ohne_silizium_zu :
    hwTorOffen hwStepTorOhneSilizium 0 zeugeOut1 (BitVec.ofNat 32 0x6)
      (.vec hwTorWitV) = false := by
  decide

/-- PLANTED REFUSAL at step level: absent silicon refuses the step. -/
theorem hwStepTor_ohne_silizium :
    stepExtTor hwStepTorOhneSilizium 0 zeugeOut1 (BitVec.ofNat 32 0x6)
      (.vec hwTorWitV) = .verweigert :=
  stepExtTor_zu _ _ _ _ _ hwStepTor_ohne_silizium_zu

/-- CLOSING: a step-level admitted vector step executes exactly as
    the coherent `reg` step, preserves well-formedness, classifies no
    gate fault and no step fault, and its TSO leg forwards to the owner
    and drains into shared memory. Every premise is used: the wrapper
    gate through `hoff`, the accepted step through `hstep`. -/
theorem hwStepTor_verbindung
    (m : HwMaschine) (c : Nat) (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (v : VectorDec) (t' : FpZustand)
    (hoff : hwTorOffen m c leaf1 xcrLo (.vec v) = true)
    (hstep : stepExtTor m c leaf1 xcrLo (.vec v) = .weiter t')
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
  have hst : stepExt (.vec v) (projFp m c) (m.bereit c) = .weiter t' :=
    stepTor_weiter_schritt m c leaf1 xcrLo (.vec v) t' hstep
  exact hwTor_verbindung m c leaf1 xcrLo v t' hoff hst hmem hwf s1 s2
    a val hrd hissue e hrest hbuf hflush

/-- JOINT COMPANION WITNESS: every premise of `hwStepTor_verbindung`
    instantiated jointly on the concrete reached run, plus the
    step-level half-gated two-core fact, the memory-change evidence,
    the owner-only foreign observation, the scalar-FP admission and
    the planted refusals. Non-degenerate: two family steps execute,
    the TSO leg changes ACTUAL shared memory (0 becomes 42) with
    forwarding visible to the owner only, and closed gates refuse. -/
theorem hwStepTor_verbindung_zeuge :
    (stepExtTor hwWitStart 0 zeugeOut1 (BitVec.ofNat 32 0x6)
        (.vec hwTorWitV) = .weiter hwTorWitT')
      ∧ HwTorSchritt zeugeOut1 (BitVec.ofNat 32 0x6) hwWitStart
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
        (.fp hwTorWitF) = true
      ∧ stepExtTor hwTorHalb 0 zeugeOut1 (BitVec.ofNat 32 0x6)
        (.vec hwTorWitV) = .weiter hwTorWitT'
      ∧ stepExtTor hwTorHalb 1 zeugeOut1 (BitVec.ofNat 32 0x6)
        (.vec hwTorWitV) = .verweigert := by
  have hmain := hwStepTor_verbindung hwWitStart 0 zeugeOut1
    (BitVec.ofNat 32 0x6) hwTorWitV hwTorWitT' hwTor_basis_vec_offen
    hwStepTor_wit_vec hwTorWit_vec_mem hwWitStart_wf hwTorS1 hwTorS2
    hwWitAdr (BitVec.ofNat 8 42) hwTor_hrd hwTor_issue
    ⟨hwWitAdr, BitVec.ofNat 8 42⟩ [] hwTor_buf hwTor_flush
  obtain ⟨hok, hreg, hfwd, hdrain, hwf', hkein, hklass⟩ := hmain
  refine ⟨hwStepTor_wit_vec, hok, hreg, hfwd, hdrain, hwf', hkein,
    hklass, hwTor_fremd_alt, hwWit_anfang_null,
    hwTor_halb_vec_0_schritt, hwTor_halb_ud_1, hwTor_unbereit_schritt,
    ?_, hwTorWit_ext_fp, hwTor_basis_fp_offen, hwStepTor_halb_0,
    hwStepTor_halb_1⟩
  exact hwTorSchritt_ud_klasse _ _ _ _ _ _ hwTor_unbereit_ud

/- CUTS: what is not proved here.

  Proved here (every accepted definition reused unchanged, never
  copied: `HwMaschine`/`HwSchritt`/`HwWf`/`HwAdapter`/`projFp`/
  `setKernVonFp`, `stepExt`/`ExtInstr`, `fpSchritt`/`stepVector`,
  `merkmalZugelassen`/`beobachtungsTor`/`hwTorOffen`, `issueByte`/
  `loadByte`/`flushKern`, `ArchFehler` with `klassifiziereExt`,
  `zeugeOut1`, `hwWitStart` and all of lane 1135's gates, plugs,
  refusals and witnesses):
  - the step-level gated evaluator `stepExtTor` (§1): the accepted
    step where the whole gate is open, refusal otherwise;
  - exact wrapper agreement (§2): step-level success admits through
    `adapterFeatureTor`, refusal/trap admits nothing, and the
    `HwTorSchritt` admitted/refused legs coincide with the step-level
    success/closed gate (`hwStepTor_ok_iff`, `hwStepTor_ud_iff`);
  - exact agreement with the accepted evaluators (§3): accepted
    FP/vector success under an open gate IS step-level (`stepTor_fp_*
    /stepTor_vec_lift`), and step-level FP/vector success IS the
    accepted success (inversions);
  - the profile-ignorance findings (§4), one theorem per family:
    F1 (six families carry no feature bit, so wrapper and step-level
    gates are always open for them and add nothing), F2 (seven of
    eight accepted `stepExt` arms never read `BereitProfil`; only the
    packed-integer arm does, with a proved counterexample), F3 (the
    step-level FP gate reads the observed CPUID/XCR0 answers, which no
    accepted step reads), F4 (absent silicon closes the step-level
    gate under full readiness);
  - well-formedness through the step level, concrete step-level
    equations, planted step-level refusals per closed leg (OS state,
    FTZ word, absent observed bit, absent silicon) (§5);
  - the closing connection with its joint non-degenerate witness:
    step-level admission, exact `HwSchritt.reg` embedding,
    well-formedness, gate/step fault silence, TSO owner-only
    forwarding and drain (0 becomes 42), two-core half-gating at both
    wrapper and step level, scalar-FP admission beside it.
  Silicon and provenance: no NEW hardware definition is introduced,
  so no new definition could be silicon-wrong: every encoding, bit
  position, length and fault class is the accepted producer's, with
  provenance in its CUTS (clone-local Intel SDM snapshot as in
  MUSE-REPORT-660/1135; no AMD snapshot, no vendor-difference,
  timing or physical-silicon claim).
  NOT proved here, and not claimed:
  - memory-touching family forms (e.g. FP stores) cannot use the
    register plug: they must use the §3/§6 issue events of
    `HardwareExecution` (same discipline as `adapterInteger666`);
  - no source/checker/emitter correspondence, no per-access target to
    W/GX simulation, no whole-word atomicity beyond the reused TSO
    byte equations, no image/loader/entry/budget link.
-/

#print axioms stepExtTor
#print axioms stepExtTor_offen
#print axioms stepExtTor_zu
#print axioms stepTor_weiter_offen
#print axioms stepTor_weiter_schritt
#print axioms stepTor_adapter_weiter
#print axioms stepTor_adapter_verweigert
#print axioms stepTor_adapter_halt
#print axioms hwStepTor_ok_iff
#print axioms hwStepTor_ud_iff
#print axioms stepTor_fp_lift
#print axioms stepTor_vec_lift
#print axioms stepTor_fp_aus_fpSchritt
#print axioms stepTor_vec_aus_stepVector
#print axioms hwStepTor_wf
#print axioms hwStepTor_verbindung
#print axioms hwStepTor_verbindung_zeuge
#print axioms stepTor_pilot_ignoriert_bereit
#print axioms stepTor_narrow_ignoriert_bereit
#print axioms stepTor_muldiv_ignoriert_bereit
#print axioms stepTor_shift_ignoriert_bereit
#print axioms stepTor_setcc_ignoriert_bereit
#print axioms stepTor_cmov_ignoriert_bereit
#print axioms stepTor_fp_ignoriert_bereit
#print axioms stepTor_vec_beachtet_bereit
#print axioms stepTor_fp_beobachtet_haengt_ab
#print axioms hwStepTor_ohne_silizium_zu

end Gabbro.Grammatik.X86
