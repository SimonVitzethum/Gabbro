/-
  File:      Grammatik/X86/HwFpDispatch.lean
  Subject:   FP s32/MXCSR rows in the unified dispatcher, on the coherent machine.

  Lane 1211 (follow-up of lane 1129 `HwFpControl.lean`): `decodeExt`/`fetchExt`
  carry no s32/MXCSR rows; those legs plug in via `FpCtrlSchritt` only. This
  file adds the decoder/dispatcher extension for the accepted s32 and MXCSR
  rows (LDMXCSR/STMXCSR, scalar single): `decodeFpDisp` tries the unified
  `decodeExt` first and the accepted `s32Decode`/`mxcsrDecode` only where every
  earlier decoder refuses, with disjointness pins (§2), fetch/execute
  permission in the `fetchExt_erfolg` discipline (§3), the `fpHwCvttZugelassen`
  gate re-proved at dispatch step level (§4, never cited), and the coherent
  machine step with wf, exact agreement, refusals and a reached two-core
  witness (§§5-8). Accepted evaluators are lifted, never redefined.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.HwFpControl
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.ScalarFloat32HardwareForms
import Grammatik.X86.FpControlHardwareForms
import Grammatik.X86.ScalarFloatHardwareForms

namespace Gabbro.Grammatik.X86

/-- One dispatched instruction: the whole unified chain plus the s32 and
    MXCSR rows. Later arms run only on earlier `none`, so dispatch is
    disjoint by construction. -/
inductive FpDispInstr where
  | ext : ExtInstr → FpDispInstr
  | s32 : S32Decodiert → FpDispInstr
  | mxcsr : MxcsrDec → FpDispInstr
  deriving DecidableEq, Repr

/-- Consumed length of one dispatched instruction (checked data). -/
def fpDispLen : FpDispInstr → Nat
  | .ext i => extLen i
  | .s32 d => d.laenge
  | .mxcsr d => d.laenge

/-- Unified dispatcher with the s32/MXCSR rows: the accepted unified
    decoder first, each accepted family decoder only where every earlier
    decoder refuses. No unified row is shadowed; no new row is re-decided. -/
def decodeFpDisp : List Byte → Option (FpDispInstr × List Byte) :=
  fun bs =>
    match decodeExt bs with
    | some (i, rest) => some (.ext i, rest)
    | none =>
      match s32Decode bs with
      | some (d, rest) => some (.s32 d, rest)
      | none =>
        match mxcsrDecode bs with
        | some (d, rest) => some (.mxcsr d, rest)
        | none => none

/-- The dispatcher agrees with the unified decoder wherever it accepts:
    no existing row is shadowed. -/
theorem decodeFpDisp_ext (bs : List Byte) (i : ExtInstr)
    (rest : List Byte) (h : decodeExt bs = some (i, rest)) :
    decodeFpDisp bs = some (.ext i, rest) := by
  unfold decodeFpDisp
  rw [h]

/-- Where the unified chain refuses, a covered s32 row is taken. -/
theorem decodeFpDisp_s32 (bs : List Byte) (d : S32Decodiert)
    (rest : List Byte) (h1 : decodeExt bs = none)
    (h2 : s32Decode bs = some (d, rest)) :
    decodeFpDisp bs = some (.s32 d, rest) := by
  unfold decodeFpDisp
  rw [h1, h2]

/-- Where the unified chain and s32 refuse, a covered MXCSR row is taken. -/
theorem decodeFpDisp_mxcsr (bs : List Byte) (d : MxcsrDec)
    (rest : List Byte) (h1 : decodeExt bs = none)
    (h2 : s32Decode bs = none)
    (h3 : mxcsrDecode bs = some (d, rest)) :
    decodeFpDisp bs = some (.mxcsr d, rest) := by
  unfold decodeFpDisp
  rw [h1, h2, h3]

/-- Where every decoder refuses, the dispatcher refuses. -/
theorem decodeFpDisp_nichts (bs : List Byte) (h1 : decodeExt bs = none)
    (h2 : s32Decode bs = none) (h3 : mxcsrDecode bs = none) :
    decodeFpDisp bs = none := by
  unfold decodeFpDisp
  rw [h1, h2, h3]

/-! ## 2. Disjointness: the new rows overlap no existing family.

  Each pin evaluates the COMPLETE decoder chain on closed bytes. The s32
  and MXCSR witness rows are refused by the whole unified chain (hence
  taken in their own arms, never in `.ext`), refuse each other, and both
  new decoders refuse the existing scalar-DOUBLE row (hence the old row
  stays in `.ext`). Any overlap would fail here as a FINDING; none does. -/

/-- The unified chain refuses the s32 witness row. -/
theorem pin_disp_vereinheitlicht_weist_s32_zurueck :
    decodeExt (s32EncodeAddssRR .xmm2 .xmm3) = none := by
  decide

/-- The MXCSR decoder refuses the s32 witness row. -/
theorem pin_disp_mxcsr_weist_s32_zurueck :
    mxcsrDecode (s32EncodeAddssRR .xmm2 .xmm3) = none := by
  decide

/-- The unified chain refuses the LDMXCSR witness row. -/
theorem pin_disp_vereinheitlicht_weist_ldmxcsr_zurueck :
    decodeExt (mxcsrEncodeLd .rax (BitVec.ofNat 32 0)) = none := by
  decide

/-- The s32 decoder refuses the LDMXCSR witness row. -/
theorem pin_disp_s32_weist_ldmxcsr_zurueck :
    s32Decode (mxcsrEncodeLd .rax (BitVec.ofNat 32 0)) = none := by
  decide

/-- The unified chain refuses the STMXCSR witness row. -/
theorem pin_disp_vereinheitlicht_weist_stmxcsr_zurueck :
    decodeExt (mxcsrEncodeSt .rax (BitVec.ofNat 32 0)) = none := by
  decide

/-- The s32 decoder refuses the STMXCSR witness row. -/
theorem pin_disp_s32_weist_stmxcsr_zurueck :
    s32Decode (mxcsrEncodeSt .rax (BitVec.ofNat 32 0)) = none := by
  decide

/-- The s32 decoder refuses the existing scalar-DOUBLE row. -/
theorem pin_disp_s32_weist_f64_zurueck :
    s32Decode (fpEncodeMovsdRR .xmm0 .xmm1) = none := by
  decide

/-- The MXCSR decoder refuses the existing scalar-DOUBLE row. -/
theorem pin_disp_mxcsr_weist_f64_zurueck :
    mxcsrDecode (fpEncodeMovsdRR .xmm0 .xmm1) = none := by
  decide

/-- The existing scalar-DOUBLE row stays unified: it decodes as `.fp`. -/
theorem pin_disp_f64_bleibt_vereinheitlicht :
    decodeExt (fpEncodeMovsdRR .xmm0 .xmm1) =
      some (.fp ⟨.movsdRR .xmm0 .xmm1, 4⟩, []) :=
  pin_ext_fp_movsd

/-- The s32 witness row is taken in its own arm. -/
theorem pin_disp_s32_arm :
    decodeFpDisp (s32EncodeAddssRR .xmm2 .xmm3) =
      some (.s32 ⟨.addssRR .xmm2 .xmm3,
        (s32EncodeAddssRR .xmm2 .xmm3).length⟩, []) := by
  have h2 := s32Roundtrip_addssRR .xmm2 .xmm3 []
  simp only [List.append_nil] at h2
  exact decodeFpDisp_s32 _ _ _ pin_disp_vereinheitlicht_weist_s32_zurueck h2

/-- `rax` has a low register code (roundtrip premise, checked data). -/
theorem pin_disp_rax_code : regCode .rax < 8 := by
  decide

/-- The LDMXCSR witness row is taken in its own arm. -/
theorem pin_disp_ldmxcsr_arm :
    decodeFpDisp (mxcsrEncodeLd .rax (BitVec.ofNat 32 0)) =
      some (.mxcsr ⟨.ldmxcsr .rax (BitVec.ofNat 32 0),
        (mxcsrEncodeLd .rax (BitVec.ofNat 32 0)).length, false⟩, []) := by
  have h3 := mxcsrRoundtrip_ld .rax (BitVec.ofNat 32 0) [] pin_disp_rax_code
  simp only [List.append_nil] at h3
  exact decodeFpDisp_mxcsr _ _ _
    pin_disp_vereinheitlicht_weist_ldmxcsr_zurueck
    pin_disp_s32_weist_ldmxcsr_zurueck h3

/-- The STMXCSR witness row is taken in its own arm. -/
theorem pin_disp_stmxcsr_arm :
    decodeFpDisp (mxcsrEncodeSt .rax (BitVec.ofNat 32 0)) =
      some (.mxcsr ⟨.stmxcsr .rax (BitVec.ofNat 32 0),
        (mxcsrEncodeSt .rax (BitVec.ofNat 32 0)).length, false⟩, []) := by
  have h3 := mxcsrRoundtrip_st .rax (BitVec.ofNat 32 0) [] pin_disp_rax_code
  simp only [List.append_nil] at h3
  exact decodeFpDisp_mxcsr _ _ _
    pin_disp_vereinheitlicht_weist_stmxcsr_zurueck
    pin_disp_s32_weist_stmxcsr_zurueck h3

/-! ## 3. Fetch: the dispatcher over actual bytes, permission as in `fetchExt`.

  Admission checks the consumed length against the fetched window, the
  decode-length guard, and execute permission of the consumed prefix --
  exactly the `fetchExt_erfolg` discipline, lifted to the dispatcher. No
  caller-supplied decoded value ever becomes a trusted fetch. -/

/-- Dispatch admission: consumed length plus remaining suffix is the
    fetched window, the length passes the guard, and the consumed
    prefix is executable. -/
def fpDispZugelassen (t : FpZustand) (fenster : List Byte)
    (i : FpDispInstr) (rest : List Byte) : Bool :=
  decide (fpDispLen i + rest.length = fenster.length) &&
    laengeOk (fpDispLen i) &&
    ausfuehrbarN t.kern.speicher t.kern.rip (fpDispLen i)

/-- Admission carries the length equation. -/
theorem fpDispZugelassen_summe (t : FpZustand) (fenster : List Byte)
    (i : FpDispInstr) (rest : List Byte)
    (h : fpDispZugelassen t fenster i rest = true) :
    fpDispLen i + rest.length = fenster.length := by
  unfold fpDispZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hsum, _⟩, _⟩ := h
  exact of_decide_eq_true hsum

/-- Admission carries the length guard. -/
theorem fpDispZugelassen_laenge (t : FpZustand) (fenster : List Byte)
    (i : FpDispInstr) (rest : List Byte)
    (h : fpDispZugelassen t fenster i rest = true) :
    laengeOk (fpDispLen i) = true := by
  unfold fpDispZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨_, hlen⟩, _⟩ := h
  exact hlen

/-- Admission carries execute permission of the consumed prefix. -/
theorem fpDispZugelassen_ausfuehrbar (t : FpZustand) (fenster : List Byte)
    (i : FpDispInstr) (rest : List Byte)
    (h : fpDispZugelassen t fenster i rest = true) :
    ausfuehrbarN t.kern.speicher t.kern.rip (fpDispLen i) = true := by
  unfold fpDispZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, hexe⟩ := h
  exact hexe

/-- Fetch and decode: the dispatcher over the given window, gated by
    dispatch admission. The second arm binds the pair whole (no pattern
    shadowing) so the admission evidence stays exact. -/
def fetchFpDisp (t : FpZustand) (fenster : List Byte) :
    Option (FpDispInstr × List Byte) :=
  match decodeFpDisp fenster with
  | none => none
  | some p =>
    if fpDispZugelassen t fenster p.1 p.2 then some p else none

/-- A successful fetch decodes to the admitted instruction: length
    equation, length guard and execute permission all hold -- the
    `fetchExt_erfolg` discipline for the extended dispatcher. -/
theorem fetchFpDisp_erfolg (t : FpZustand) (fenster : List Byte)
    (i : FpDispInstr) (rest : List Byte)
    (h : fetchFpDisp t fenster = some (i, rest)) :
    decodeFpDisp fenster = some (i, rest) ∧
      fpDispLen i + rest.length = fenster.length ∧
      laengeOk (fpDispLen i) = true ∧
      ausfuehrbarN t.kern.speicher t.kern.rip (fpDispLen i) = true := by
  have e : fetchFpDisp t fenster =
      match decodeFpDisp fenster with
      | none => (none : Option (FpDispInstr × List Byte))
      | some p =>
        if fpDispZugelassen t fenster p.1 p.2 then some p else none := rfl
  rw [e] at h
  cases hdec : decodeFpDisp fenster with
  | none =>
    simp [hdec] at h
  | some p =>
    rw [hdec] at h
    by_cases hz : fpDispZugelassen t fenster p.1 p.2 = true
    · simp [hz] at h
      rw [h] at hz
      exact ⟨by rw [h],
        fpDispZugelassen_summe t fenster _ _ hz,
        fpDispZugelassen_laenge t fenster _ _ hz,
        fpDispZugelassen_ausfuehrbar t fenster _ _ hz⟩
    · simp [hz] at h

/-- Fetch refusal is dispatcher refusal. -/
theorem fetchFpDisp_verweigert (t : FpZustand) (fenster : List Byte)
    (h : decodeFpDisp fenster = none) :
    fetchFpDisp t fenster = none := by
  unfold fetchFpDisp
  rw [h]

/-! ## 4. Conversion gate and state-level dispatch.

  The `fpHwCvttZugelassen` domain predicate is reused as the dispatcher's
  own gate (lifted, never redefined), but every gating fact below is
  proved HERE from the gate definition: the family byte-step gate
  theorems are never cited. Out-of-domain conversions refuse before any
  evaluator runs. -/

/-- Conversion-domain gate at dispatch level: the accepted predicate on
    the unified `.fp` leg, open everywhere else. -/
def fpDispGate (d : FpDispInstr) (t : FpZustand) : Bool :=
  match d with
  | .ext (.fp f) => fpHwCvttZugelassen f.befehl t
  | _ => true

/-- The gate on the unified `.fp` leg IS the accepted predicate. -/
theorem fpDispGate_ext_fp (f : FpDecodiert) (t : FpZustand) :
    fpDispGate (.ext (.fp f)) t = fpHwCvttZugelassen f.befehl t := rfl

/-- Every non-`.fp` form is ungated. -/
theorem fpDispGate_kein_fp (d : FpDispInstr) (t : FpZustand)
    (h : ∀ f : FpDecodiert, d ≠ .ext (.fp f)) :
    fpDispGate d t = true := by
  cases d with
  | ext i =>
    cases i with
    | pilot _ => rfl
    | narrow _ => rfl
    | muldiv _ => rfl
    | shift _ => rfl
    | setcc _ _ _ => rfl
    | cmov _ _ _ _ => rfl
    | fp f => exact absurd rfl (h f)
    | vec _ => rfl
  | s32 _ => rfl
  | mxcsr _ => rfl

/-- The gate equation on a conversion form unfolds to the domain check. -/
theorem fpDispGate_cvtt_gleichung (dst : Register) (src : XmmReg)
    (t : FpZustand) :
    fpHwCvttZugelassen (.cvttsd2si dst src) t =
      cvttHwGueltig (xmmTief t.xmm src) := rfl

/-- The gate refuses a NaN source: re-proved from the definition. -/
theorem fpDispGate_cvtt_nan (dst : Register) (src : XmmReg)
    (t : FpZustand) (hsrc : xmmTief t.xmm src = 0x7FF0000000000001) :
    fpDispGate (.ext (.fp ⟨.cvttsd2si dst src, 4⟩)) t = false := by
  show fpHwCvttZugelassen (.cvttsd2si dst src) t = false
  rw [fpDispGate_cvtt_gleichung, hsrc]
  exact cvttHwGueltig_nan

/-- The gate admits `42.0`: re-proved from the definition. -/
theorem fpDispGate_cvtt_42 (dst : Register) (src : XmmReg)
    (t : FpZustand) (hsrc : xmmTief t.xmm src = 0x4045000000000000) :
    fpDispGate (.ext (.fp ⟨.cvttsd2si dst src, 4⟩)) t = true := by
  show fpHwCvttZugelassen (.cvttsd2si dst src) t = true
  rw [fpDispGate_cvtt_gleichung, hsrc]
  exact cvttHwGueltig_42

/-- Dispatch outcome on the extended state. -/
inductive FpDispAusgang where
  | weiter : FpZustand → FpDispAusgang
  | verweigert : FpDispAusgang

/-- One dispatch step on the extended state: the unified leg runs
    `stepExt`, the s32 leg its accepted evaluator, the LDMXCSR leg its
    accepted load. STMXCSR has no register outcome here: it is a memory
    store and travels the §6 issue path on the machine. -/
def fpDispSchrittZustand (d : FpDispInstr) (t : FpZustand)
    (b : BereitProfil) : FpDispAusgang :=
  match d with
  | .ext i =>
    match stepExt i t b with
    | .weiter t' => .weiter t'
    | _ => .verweigert
  | .s32 s =>
    match s32Schritt s t with
    | some t' => .weiter t'
    | none => .verweigert
  | .mxcsr m =>
    match m.befehl with
    | .ldmxcsr _ _ =>
      match mxcsrSchritt m t mxcsrProfilModern mxcsrSteuerungOffen with
      | .weiter t' => .weiter t'
      | _ => .verweigert
    | .stmxcsr _ _ => .verweigert

/-- Selection: the unified leg IS the accepted unified step. -/
theorem fpDispSchrittZustand_ext (i : ExtInstr) (t t' : FpZustand)
    (b : BereitProfil) (h : stepExt i t b = .weiter t') :
    fpDispSchrittZustand (.ext i) t b = .weiter t' := by
  have e : fpDispSchrittZustand (.ext i) t b =
      match stepExt i t b with
      | .weiter t' => FpDispAusgang.weiter t'
      | _ => .verweigert := rfl
  rw [e, h]

/-- Selection: unified refusal is dispatch refusal. -/
theorem fpDispSchrittZustand_ext_verweigert (i : ExtInstr)
    (t : FpZustand) (b : BereitProfil)
    (h : stepExt i t b = .verweigert) :
    fpDispSchrittZustand (.ext i) t b = .verweigert := by
  have e : fpDispSchrittZustand (.ext i) t b =
      match stepExt i t b with
      | .weiter t' => FpDispAusgang.weiter t'
      | _ => .verweigert := rfl
  rw [e, h]

/-- Selection: the s32 leg IS the accepted s32 step. -/
theorem fpDispSchrittZustand_s32 (s : S32Decodiert) (t t' : FpZustand)
    (b : BereitProfil) (h : s32Schritt s t = some t') :
    fpDispSchrittZustand (.s32 s) t b = .weiter t' := by
  have e : fpDispSchrittZustand (.s32 s) t b =
      match s32Schritt s t with
      | some t' => FpDispAusgang.weiter t'
      | none => .verweigert := rfl
  rw [e, h]

/-- Selection: s32 refusal is dispatch refusal. -/
theorem fpDispSchrittZustand_s32_verweigert (s : S32Decodiert)
    (t : FpZustand) (b : BereitProfil)
    (h : s32Schritt s t = none) :
    fpDispSchrittZustand (.s32 s) t b = .verweigert := by
  have e : fpDispSchrittZustand (.s32 s) t b =
      match s32Schritt s t with
      | some t' => FpDispAusgang.weiter t'
      | none => .verweigert := rfl
  rw [e, h]

/-- Selection: the LDMXCSR leg IS the accepted load. -/
theorem fpDispSchrittZustand_ld (m : MxcsrDec) (t t' : FpZustand)
    (b : BereitProfil) (base : Register) (disp : BitVec 32)
    (hbef : m.befehl = .ldmxcsr base disp)
    (h : mxcsrSchritt m t mxcsrProfilModern mxcsrSteuerungOffen =
      .weiter t') :
    fpDispSchrittZustand (.mxcsr m) t b = .weiter t' := by
  have e : fpDispSchrittZustand (.mxcsr m) t b =
      match m.befehl with
      | .ldmxcsr _ _ =>
        match mxcsrSchritt m t mxcsrProfilModern mxcsrSteuerungOffen with
        | .weiter t' => FpDispAusgang.weiter t'
        | _ => .verweigert
      | .stmxcsr _ _ => .verweigert := rfl
  rw [e, hbef, h]

/-- STMXCSR has no register outcome: the store travels the issue path. -/
theorem fpDispSchrittZustand_st_verweigert (m : MxcsrDec)
    (t : FpZustand) (b : BereitProfil) (base : Register)
    (disp : BitVec 32) (hbef : m.befehl = .stmxcsr base disp) :
    fpDispSchrittZustand (.mxcsr m) t b = .verweigert := by
  have e : fpDispSchrittZustand (.mxcsr m) t b =
      match m.befehl with
      | .ldmxcsr _ _ =>
        match mxcsrSchritt m t mxcsrProfilModern mxcsrSteuerungOffen with
        | .weiter t' => FpDispAusgang.weiter t'
        | _ => .verweigert
      | .stmxcsr _ _ => .verweigert := rfl
  rw [e, hbef]

/-- The gated dispatch step: the conversion gate runs before any
    evaluator. A forged decoded value cannot inject an out-of-domain
    conversion. -/
def fpDispGated (d : FpDispInstr) (t : FpZustand)
    (b : BereitProfil) : FpDispAusgang :=
  if fpDispGate d t then fpDispSchrittZustand d t b else .verweigert

/-- A refused conversion domain refuses the gated step, whatever the
    accepted evaluator would compute. -/
theorem fpDispGated_gate_verweigert (d : FpDispInstr) (t : FpZustand)
    (b : BereitProfil) (h : fpDispGate d t = false) :
    fpDispGated d t b = .verweigert := by
  unfold fpDispGated
  simp [h]

/-- An open gate runs the dispatched evaluator. -/
theorem fpDispGated_gate_offen (d : FpDispInstr) (t : FpZustand)
    (b : BereitProfil) (h : fpDispGate d t = true) :
    fpDispGated d t b = fpDispSchrittZustand d t b := by
  unfold fpDispGated
  simp [h]

/-- One dispatched byte step from actual memory: fetch, gate, then the
    dispatched evaluator. Takes ONLY the state and the readiness
    profile: a forged `FpDispInstr` cannot inject an instruction. Any
    fetch, gate or step failure is `verweigert`. -/
def fpDispByteschritt (t : FpZustand) (b : BereitProfil) : FpDispAusgang :=
  match fetchFpDisp t (fpHwGeholt t) with
  | none => .verweigert
  | some (d, _) =>
    if fpDispGate d t then fpDispSchrittZustand d t b else .verweigert

/-- Selection: a fetched, gated instruction steps through dispatch. -/
theorem fpDispByteschritt_weiter (t : FpZustand) (b : BereitProfil)
    (d : FpDispInstr) (rest : List Byte) (o : FpDispAusgang)
    (hf : fetchFpDisp t (fpHwGeholt t) = some (d, rest))
    (hg : fpDispGate d t = true)
    (hs : fpDispSchrittZustand d t b = o) :
    fpDispByteschritt t b = o := by
  have e : fpDispByteschritt t b =
      match fetchFpDisp t (fpHwGeholt t) with
      | none => FpDispAusgang.verweigert
      | some (j, _) =>
        if fpDispGate j t then fpDispSchrittZustand j t b
        else .verweigert := rfl
  rw [e, hf]
  simp [hg, hs]

/-- Selection: fetch refusal is byte-step refusal. -/
theorem fpDispByteschritt_verweigert (t : FpZustand) (b : BereitProfil)
    (hf : fetchFpDisp t (fpHwGeholt t) = none) :
    fpDispByteschritt t b = .verweigert := by
  have e : fpDispByteschritt t b =
      match fetchFpDisp t (fpHwGeholt t) with
      | none => FpDispAusgang.verweigert
      | some (j, _) =>
        if fpDispGate j t then fpDispSchrittZustand j t b
        else .verweigert := rfl
  rw [e, hf]

/-- A refused conversion domain refuses the byte step, whatever the
    accepted evaluator would compute. -/
theorem fpDispByteschritt_gate_verweigert (t : FpZustand)
    (b : BereitProfil) (d : FpDispInstr) (rest : List Byte)
    (hf : fetchFpDisp t (fpHwGeholt t) = some (d, rest))
    (hg : fpDispGate d t = false) :
    fpDispByteschritt t b = .verweigert := by
  have e : fpDispByteschritt t b =
      match fetchFpDisp t (fpHwGeholt t) with
      | none => FpDispAusgang.verweigert
      | some (j, _) =>
        if fpDispGate j t then fpDispSchrittZustand j t b
        else .verweigert := rfl
  rw [e, hf]
  simp [hg]

/-! ## 5. Machine step: the dispatcher on the coherent machine.

  Register legs re-embed ONLY core data and keep machine memory and
  buffers; the memory-unchanged premise is the `HwSchritt.reg` gate, so
  no canonical `read32`/`write32` effect is ever substituted for a
  buffered access. Every register leg carries its fetch evidence
  (`fetchFpDisp` over the core's ACTUAL fetched window, hence execute
  permission), the `.ext` leg additionally the re-proved conversion
  gate, and the MXCSR leg the LDMXCSR form (STMXCSR travels the §6
  issue path). Memory moves only through `issueByte`, `loadByte` and
  `flushKern` on the shared TSO view. -/

/-- Observable dispatch events on the coherent machine. -/
inductive FpDispEreignis where
  | s32reg : Nat → S32Decodiert → FpDispEreignis
  | mxcsrLd : Nat → MxcsrDec → FpDispEreignis
  | extReg : Nat → ExtInstr → FpDispEreignis
  | leseBeob : Nat → Adresse → Byte → FpDispEreignis
  | schreibAusgabe : Nat → Adresse → Byte → FpDispEreignis
  | spülung : Nat → TSOEintrag → FpDispEreignis
  | verweigert : Nat → FpDispEreignis
  deriving DecidableEq, Repr

/-- One dispatch step on the coherent machine. -/
inductive FpDispSchritt : HwMaschine → HwMaschine → FpDispEreignis → Prop where
  | s32reg {m : HwMaschine} (c : Nat) (d : S32Decodiert) (t' : FpZustand)
      (rest : List Byte)
      (hfetch : fetchFpDisp (projFp m c) (geholt (projZustand m c)) =
        some (.s32 d, rest))
      (hstep : s32Schritt d (projFp m c) = some t')
      (hmem : t'.kern.speicher = m.mem) :
      FpDispSchritt m (setKernVonFp m c t') (.s32reg c d)
  | mxcsrLd {m : HwMaschine} (c : Nat) (d : MxcsrDec) (t' : FpZustand)
      (base : Register) (disp : BitVec 32) (rest : List Byte)
      (hfetch : fetchFpDisp (projFp m c) (geholt (projZustand m c)) =
        some (.mxcsr d, rest))
      (hbef : d.befehl = .ldmxcsr base disp)
      (hstep : mxcsrSchritt d (projFp m c) mxcsrProfilModern
        mxcsrSteuerungOffen = .weiter t')
      (hmem : t'.kern.speicher = m.mem) :
      FpDispSchritt m (setKernVonFp m c t') (.mxcsrLd c d)
  | extReg {m : HwMaschine} (c : Nat) (i : ExtInstr) (t' : FpZustand)
      (rest : List Byte)
      (hfetch : fetchFpDisp (projFp m c) (geholt (projZustand m c)) =
        some (.ext i, rest))
      (hgate : fpDispGate (.ext i) (projFp m c) = true)
      (hstep : stepExt i (projFp m c) (m.bereit c) = .weiter t')
      (hmem : t'.kern.speicher = m.mem) :
      FpDispSchritt m (setKernVonFp m c t') (.extReg c i)
  | lade {m : HwMaschine} (c : Nat) (a : Adresse) (v : Byte)
      (h : loadByte (tsoAnsicht m) c a = some v) :
      FpDispSchritt m m (.leseBeob c a v)
  | gibAus {m : HwMaschine} (c : Nat) (a : Adresse) (v : Byte)
      (s' : TSOZustand)
      (h : issueByte (tsoAnsicht m) c a v = some s') :
      FpDispSchritt m (setTso m s') (.schreibAusgabe c a v)
  | spüle {m : HwMaschine} (c : Nat) (e : TSOEintrag)
      (s' : TSOZustand)
      (h : flushKern (tsoAnsicht m) c = some s')
      (hkopf : (m.puffer c).head? = some e) :
      FpDispSchritt m (setTso m s') (.spülung c e)
  | fehler {m : HwMaschine} (c : Nat)
      (h : fetchFpDisp (projFp m c) (geholt (projZustand m c)) = none) :
      FpDispSchritt m m (.verweigert c)

/-- Every dispatch step preserves well-formedness. -/
theorem fpDispSchritt_wf (m m' : HwMaschine) (e : FpDispEreignis)
    (h : FpDispSchritt m m' e) (hwf : HwWf m) : HwWf m' := by
  cases h with
  | s32reg c d t' rest hfetch hstep hmem =>
    exact setKernDaten_wf _ c _ hwf
  | mxcsrLd c d t' base disp rest hfetch hbef hstep hmem =>
    exact setKernDaten_wf _ c _ hwf
  | extReg c i t' rest hfetch hgate hstep hmem =>
    exact setKernDaten_wf _ c _ hwf
  | lade c a v h => exact hwf
  | gibAus c a v s' h => exact setTso_wf _ s' hwf
  | spüle c e s' h hkopf => exact setTso_wf _ s' hwf
  | fehler c h => exact hwf

/-! ## 6. Exact agreement: the old evaluators are lifted, never redefined.

  Each register leg IS its accepted equation on the coherent machine:
  s32 and LDMXCSR legs are the `FpCtrlSchritt` legs, the unified leg is
  the `HwSchritt.reg` step, and the TSO legs are the coherent TSO steps.
  Stores (STMXCSR, MOVSS-store) travel as four buffered byte issues of
  the accepted stored word at the accepted address (§6, second half). -/

/-- A dispatch s32 step is the coherent s32 step. -/
theorem fpDispS32_ist_fpCtrl (m m' : HwMaschine) (c : Nat)
    (d : S32Decodiert)
    (h : FpDispSchritt m m' (.s32reg c d)) :
    FpCtrlSchritt m m' (.s32reg c d) := by
  cases h with
  | s32reg c d t' rest hfetch hstep hmem =>
    exact FpCtrlSchritt.s32reg c d t' hstep hmem

/-- A dispatch MXCSR-load step is the coherent MXCSR-load step. -/
theorem fpDispMxcsr_ist_fpCtrl (m m' : HwMaschine) (c : Nat)
    (d : MxcsrDec)
    (h : FpDispSchritt m m' (.mxcsrLd c d)) :
    FpCtrlSchritt m m' (.mxcsrLd c d) := by
  cases h with
  | mxcsrLd c d t' base disp rest hfetch hbef hstep hmem =>
    exact FpCtrlSchritt.mxcsrLd c d t' hstep hmem

/-- A dispatch unified step is the coherent `reg` step. -/
theorem fpDispExt_ist_hwReg (m m' : HwMaschine) (c : Nat)
    (i : ExtInstr)
    (h : FpDispSchritt m m' (.extReg c i)) :
    HwSchritt m m' (.regAusf c i) := by
  cases h with
  | extReg c i t' rest hfetch hgate hstep hmem =>
    exact HwSchritt.reg c i t' hstep hmem

/-- Dispatch observations are coherent observations. -/
theorem fpDispLade_ist_hw (m m' : HwMaschine) (c : Nat) (a : Adresse)
    (v : Byte)
    (h : FpDispSchritt m m' (.leseBeob c a v)) :
    HwSchritt m m' (.leseBeob c a v) := by
  cases h with
  | lade c a v h => exact HwSchritt.lade c a v h

/-- Dispatch store issues are coherent store issues. -/
theorem fpDispGibAus_ist_hw (m m' : HwMaschine) (c : Nat) (a : Adresse)
    (v : Byte)
    (h : FpDispSchritt m m' (.schreibAusgabe c a v)) :
    HwSchritt m m' (.schreibAusgabe c a v) := by
  cases h with
  | gibAus c a v s' h => exact HwSchritt.gibAus c a v s' h

/-- Dispatch drains are coherent drains. -/
theorem fpDispSpüle_ist_hw (m m' : HwMaschine) (c : Nat)
    (e : TSOEintrag)
    (h : FpDispSchritt m m' (.spülung c e)) :
    ∃ s' : TSOZustand, HwSchritt m m' (.spülung c e) := by
  cases h with
  | spüle c e s' h hkopf => exact ⟨s', HwSchritt.spüle c e s' h hkopf⟩

/-- STMXCSR travels as four buffered byte issues of the accepted stored
    word: the accepted `st` writes `mxcsrSpeicherWort` of the core
    control word, and this issues exactly that word's four bytes. -/
def fpDispMxcsrAusgabe (m : HwMaschine) (c : Nat) (a : Adresse)
    (w : MXCSR) : Option HwMaschine :=
  fpCtrlAusgabe32 m c a (mxcsrSpeicherWort w)

/-- The STMXCSR issue appends exactly the stored word's four canonical
    entries and changes no canonical byte. -/
theorem fpDispSt_ist_ausgabe32 (m m' : HwMaschine) (c : Nat)
    (a : Adresse) (w : MXCSR)
    (h : fpDispMxcsrAusgabe m c a w = some m') :
    m'.puffer c = m.puffer c ++
        fpEintraege32 a (mxcsrSpeicherWort w) ∧
      (∀ x : Adresse, m'.mem.bytes x = m.mem.bytes x) := by
  constructor
  · unfold fpDispMxcsrAusgabe at h
    exact fpCtrlAusgabe32_puffer _ _ _ _ _ h
  · intro x
    unfold fpDispMxcsrAusgabe at h
    exact fpCtrlAusgabe32_kein_speicher _ _ _ _ _ h x

/-- The STMXCSR issue preserves well-formedness. -/
theorem fpDispSt_wf (m m' : HwMaschine) (c : Nat) (a : Adresse)
    (w : MXCSR)
    (h : fpDispMxcsrAusgabe m c a w = some m') (hwf : HwWf m) :
    HwWf m' := by
  unfold fpDispMxcsrAusgabe at h
  exact fpCtrlAusgabe32_wf _ _ _ _ _ h hwf

/-- A successful STMXCSR issue from an empty foreign-free buffer
    establishes the 32-bit group for the stored word. -/
theorem fpDispSt_gruppe (m m' : HwMaschine) (c : Nat) (a : Adresse)
    (w : MXCSR)
    (hempty : m.puffer c = [])
    (hfrei : FpFremdFrei32 (tsoAnsicht m) c a)
    (h : fpDispMxcsrAusgabe m c a w = some m') :
    FpGruppe32 (tsoAnsicht m') c a (mxcsrSpeicherWort w) := by
  unfold fpDispMxcsrAusgabe at h
  exact fpCtrlAusgabe32_gruppe _ _ _ _ _ hempty hfrei h

/-- A MOVSS store travels the same way: the accepted `movssSpeichere`
    writes `setWidth 64` of the source low single, issued here as four
    buffered bytes at the accepted address. -/
def fpDispMovssAusgabe (m : HwMaschine) (c : Nat) (a : Adresse)
    (f : XmmDatei) (src : XmmReg) : Option HwMaschine :=
  fpCtrlAusgabe32 m c a (BitVec.setWidth 64 (xmmTief32 f src))

/-- The MOVSS-store issue appends exactly the stored word's four
    canonical entries and changes no canonical byte. -/
theorem fpDispMovss_ist_ausgabe32 (m m' : HwMaschine) (c : Nat)
    (a : Adresse) (f : XmmDatei) (src : XmmReg)
    (h : fpDispMovssAusgabe m c a f src = some m') :
    m'.puffer c = m.puffer c ++
        fpEintraege32 a (BitVec.setWidth 64 (xmmTief32 f src)) ∧
      (∀ x : Adresse, m'.mem.bytes x = m.mem.bytes x) := by
  constructor
  · unfold fpDispMovssAusgabe at h
    exact fpCtrlAusgabe32_puffer _ _ _ _ _ h
  · intro x
    unfold fpDispMovssAusgabe at h
    exact fpCtrlAusgabe32_kein_speicher _ _ _ _ _ h x

/-! ## 7. Refusals: what is not admitted is refused.

  Bad lengths, refused profiles, LOCK-prefixed MXCSR (`#UD` in the
  family, hence no `.weiter` and no machine step), the STMXCSR form on
  the register path (it travels §6), a refused conversion domain on the
  unified leg, and unreadable/unwritable bytes all refuse explicitly. -/

/-- A bad decode length admits no dispatch s32 step. -/
theorem fpDispS32_laenge_kein_schritt (m m' : HwMaschine) (c : Nat)
    (d : S32Decodiert)
    (hok : laengeOk d.laenge = false)
    (h : FpDispSchritt m m' (.s32reg c d)) : False := by
  cases h with
  | s32reg c d t' rest hfetch hstep hmem =>
    rw [s32Schritt_laenge_verweigert _ _ hok] at hstep
    cases hstep

/-- A refused profile admits no dispatch s32 step. -/
theorem fpDispS32_profil_kein_schritt (m m' : HwMaschine) (c : Nat)
    (d : S32Decodiert)
    (hfp : s32Eintritt (projFp m c).fp = false)
    (h : FpDispSchritt m m' (.s32reg c d)) : False := by
  cases h with
  | s32reg c d t' rest hfetch hstep hmem =>
    cases hok : laengeOk d.laenge with
    | false =>
      rw [s32Schritt_laenge_verweigert _ _ hok] at hstep
      cases hstep
    | true =>
      rw [s32Schritt_profil_verweigert _ _ hok hfp] at hstep
      cases hstep

/-- A bad decode length admits no dispatch MXCSR step. -/
theorem fpDispMxcsr_laenge_kein_schritt (m m' : HwMaschine) (c : Nat)
    (d : MxcsrDec)
    (hok : laengeOk d.laenge = false)
    (h : FpDispSchritt m m' (.mxcsrLd c d)) : False := by
  cases h with
  | mxcsrLd c d t' base disp rest hfetch hbef hstep hmem =>
    rw [mxcsrSchritt_laenge_verweigert _ _ _ _ hok] at hstep
    cases hstep

/-- A LOCK-prefixed MXCSR form faults with `#UD` in the family, so it
    never yields `.weiter` and admits no dispatch step. -/
theorem fpDispMxcsrLock_kein_schritt (m m' : HwMaschine) (c : Nat)
    (d : MxcsrDec)
    (hok : laengeOk d.laenge = true)
    (hlock : d.gesperrt = true)
    (h : FpDispSchritt m m' (.mxcsrLd c d)) : False := by
  cases h with
  | mxcsrLd c d t' base disp rest hfetch hbef hstep hmem =>
    rw [mxcsrSchritt_gesperrt_ud _ _ _ _ hok hlock] at hstep
    cases hstep

/-- STMXCSR admits no register step: the form is pinned to `.ldmxcsr`
    on this path and the store travels §6. -/
theorem fpDispMxcsrSt_kein_register (m m' : HwMaschine) (c : Nat)
    (d : MxcsrDec) (base : Register) (disp : BitVec 32)
    (hbef : d.befehl = .stmxcsr base disp)
    (h : FpDispSchritt m m' (.mxcsrLd c d)) : False := by
  cases h with
  | mxcsrLd c d t' b dd rest hfetch hbef' hstep hmem =>
    rw [hbef] at hbef'
    cases hbef'

/-- A refused conversion domain admits no dispatch unified step. -/
theorem fpDispExt_gate_kein_schritt (m m' : HwMaschine) (c : Nat)
    (i : ExtInstr)
    (hgate : fpDispGate (.ext i) (projFp m c) = false)
    (h : FpDispSchritt m m' (.extReg c i)) : False := by
  cases h with
  | extReg c i t' rest hfetch hg hstep hmem =>
    rw [hg] at hgate
    cases hgate

/-- An unreadable byte admits no dispatch observation. -/
theorem fpDispLaden_ohne_lesbar_kein_schritt (m m' : HwMaschine)
    (c : Nat) (a : Adresse) (v : Byte)
    (hperm : (tsoAnsicht m).mem.lesbar a = false)
    (h : FpDispSchritt m m' (.leseBeob c a v)) : False := by
  cases h with
  | lade c a v hload =>
    rw [load_verweigert _ _ _ hperm] at hload
    cases hload

/-- An unwritable byte admits no dispatch store issue. -/
theorem fpDispAusgabe_ohne_schreibbar_kein_schritt (m m' : HwMaschine)
    (c : Nat) (a : Adresse) (v : Byte)
    (hperm : (tsoAnsicht m).mem.schreibbar a = false)
    (h : FpDispSchritt m m' (.schreibAusgabe c a v)) : False := by
  cases h with
  | gibAus c a v s' hissue =>
    rw [issue_verweigert _ _ _ _ hperm] at hissue
    cases hissue

end Gabbro.Grammatik.X86
