/-
  File:      Grammatik/X86/HwMulDivWidth.lean
  Subject:   Multiply/divide and narrow widths connected to the coherent
             machine and the unified byte dispatcher.

  Lane 1127: lifts the accepted `MulDivWidthHardwareForms` evaluator
  (`wdSchritt`/`decodeWd`/`wdEncode`) unchanged into the unified
  dispatcher path of `ExtendedExecution` (Ext first, never shadowing
  the pilot) and into a `HwAdapter` over `HwMaschine`/`HwSchritt`
  (`HardwareExecution`). The divide fault is an outcome reusing the
  accepted `HwRegAusgang`, never a plugged successor state. No new
  machine, no redefined evaluator, no silicon proof beyond
  self-consistency (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.TSO
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.MulDiv
import Grammatik.X86.MulDivWidthHardwareForms
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.FeatureProfile
import Grammatik.X86.Gleitprofil
import Grammatik.X86.ScalarFloat
import Grammatik.X86.HardwareExecution

namespace Gabbro.Grammatik.X86

/-- Unified dispatcher instruction: the accepted unified chain first,
    the width family only where it refuses. -/
inductive WdHwInstr where
  | ext : ExtInstr → WdHwInstr
  | wd : WdDecodiert → WdHwInstr
  deriving DecidableEq, Repr

/-- Dispatcher: the unified decoder first, the width decoder only
    where the unified chain refuses. No pilot form is shadowed. -/
def decodeMulDivWidth : List Byte → Option (WdHwInstr × List Byte) :=
  fun bs =>
    match decodeExt bs with
    | some (i, rest) => some (.ext i, rest)
    | none =>
      match decodeWd bs with
      | some (d, rest) => some (.wd d, rest)
      | none => none

/-- Consumed length of one dispatcher instruction (checked data). -/
def wdHwLen : WdHwInstr → Nat
  | .ext i => extLen i
  | .wd d => d.laenge

/-- The dispatcher agrees with the unified chain wherever it accepts:
    no pilot or extension form is shadowed. -/
theorem decodeMulDivWidth_prefers_ext (bs : List Byte) (i : ExtInstr)
    (rest : List Byte) (h : decodeExt bs = some (i, rest)) :
    decodeMulDivWidth bs = some (.ext i, rest) := by
  unfold decodeMulDivWidth
  rw [h]

/-- Where the unified chain refuses, a covered width row is taken. -/
theorem decodeMulDivWidth_wd (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (h1 : decodeExt bs = none)
    (h2 : decodeWd bs = some (d, rest)) :
    decodeMulDivWidth bs = some (.wd d, rest) := by
  unfold decodeMulDivWidth
  rw [h1, h2]

/-- Where both chains refuse, the dispatcher refuses. -/
theorem decodeMulDivWidth_nichts (bs : List Byte)
    (h1 : decodeExt bs = none) (h2 : decodeWd bs = none) :
    decodeMulDivWidth bs = none := by
  unfold decodeMulDivWidth
  rw [h1, h2]

/-! ## 1. No shadowing: the unified chain refuses the new width rows.

  The 32-bit Group-3 rows (no REX), both immediate rows and both
  preparation rows are refused by the whole unified chain, so the
  width arm takes them exactly once. The three REX.W Group-3/0FAF
  rows overlap the accepted 64-bit multiply/divide codec and stay
  with the unified `muldiv` arm (proved below, never re-decided). -/

theorem ext_weist_wdmul32_zurueck :
    decodeExt [natByte 247, natByte 225] = none := by
  decide

theorem pin_ext_wdmul64 :
    decodeExt [natByte 73, natByte 247, natByte 224] =
      some (.muldiv ⟨.mulRax .r8, 3⟩, []) := by
  decide

theorem ext_weist_wddiv32_zurueck :
    decodeExt [natByte 247, natByte 241] = none := by
  decide

theorem pin_ext_wdidiv64 :
    decodeExt [natByte 73, natByte 247, natByte 251] =
      some (.muldiv ⟨.idivRax .r11, 3⟩, []) := by
  decide

theorem pin_ext_wdimul2 :
    decodeExt [natByte 77, natByte 15, natByte 175, natByte 207] =
      some (.muldiv ⟨.imul2 .r9 .r15, 4⟩, []) := by
  decide

theorem ext_weist_wdimul3k_zurueck :
    decodeExt [natByte 68, natByte 107, natByte 193, natByte 253] = none := by
  decide

theorem ext_weist_wdimul3k64_zurueck :
    decodeExt [natByte 73, natByte 107, natByte 199, natByte 128] = none := by
  decide

theorem ext_weist_wdimul3w_zurueck :
    decodeExt [natByte 105, natByte 208, natByte 160, natByte 134,
      natByte 1, natByte 0] = none := by
  decide

theorem ext_weist_wdimul3w64_zurueck :
    decodeExt [natByte 77, natByte 105, natByte 200, natByte 144,
      natByte 238, natByte 254, natByte 255] = none := by
  decide

theorem ext_weist_wdvor98_zurueck :
    decodeExt [natByte 152] = none := by
  decide

theorem ext_weist_wdvor98w64_zurueck :
    decodeExt [natByte 72, natByte 152] = none := by
  decide

theorem ext_weist_wdvor99_zurueck :
    decodeExt [natByte 153] = none := by
  decide

theorem ext_weist_wdvor99w64_zurueck :
    decodeExt [natByte 72, natByte 153] = none := by
  decide

/-! ## 2. Dispatcher pins: one byte string per case through the chain.

  New rows take the width arm with their accepted decode evidence;
  overlapping rows keep the unified `muldiv` arm; the pilot row is
  unchanged. Planted refusals stay refused through the dispatcher. -/

/-- Pin: the pilot row goes through unchanged. -/
theorem pin_wdHw_pilot_ret :
    decodeMulDivWidth (encode .ret) =
      some (.ext (.pilot ⟨.ret, 1⟩), []) :=
  decodeMulDivWidth_prefers_ext _ _ _ pin_ext_pilot_ret

/-- Pin: the new 32-bit MUL row takes the width arm. -/
theorem pin_wdHw_wdmul32 :
    decodeMulDivWidth [natByte 247, natByte 225] =
      some (.wd (⟨WdBefehl.mul WdBreite.w32 Register.rcx, 2⟩ : WdDecodiert),
        []) :=
  decodeMulDivWidth_wd _ _ _ ext_weist_wdmul32_zurueck pin_wdmul_ecx_dekode

/-- Pin: the new 32-bit DIV row takes the width arm. -/
theorem pin_wdHw_wddiv32 :
    decodeMulDivWidth [natByte 247, natByte 241] =
      some (.wd (⟨WdBefehl.divWd WdBreite.w32 Register.rcx, 2⟩ : WdDecodiert),
        []) :=
  decodeMulDivWidth_wd _ _ _ ext_weist_wddiv32_zurueck pin_wddiv_ecx_dekode

/-- Pin: the compact immediate row takes the width arm. -/
theorem pin_wdHw_wdimul3k :
    decodeMulDivWidth [natByte 68, natByte 107, natByte 193, natByte 253] =
      some (.wd (⟨WdBefehl.imul3 WdBreite.w32 Register.r8 Register.rcx (-3),
        4⟩ : WdDecodiert), []) :=
  decodeMulDivWidth_wd _ _ _ ext_weist_wdimul3k_zurueck
    pin_wdimul3_kompakt_dekode

/-- Pin: the 64-bit dword immediate row takes the width arm. -/
theorem pin_wdHw_wdimul3w64 :
    decodeMulDivWidth [natByte 77, natByte 105, natByte 200, natByte 144,
      natByte 238, natByte 254, natByte 255] =
      some (.wd (⟨WdBefehl.imul3 WdBreite.w64 Register.r9 Register.r8
        (-70000), 7⟩ : WdDecodiert), []) :=
  decodeMulDivWidth_wd _ _ _ ext_weist_wdimul3w64_zurueck
    pin_wdimul3_wort64_dekode

/-- Pin: CDQE takes the width arm. -/
theorem pin_wdHw_wdvor98w64 :
    decodeMulDivWidth [natByte 72, natByte 152] =
      some (.wd (⟨WdBefehl.vor98 WdBreite.w64, 2⟩ : WdDecodiert), []) := by
  have h := (pin_wdvor98_dekode).2
  exact decodeMulDivWidth_wd _ _ _ ext_weist_wdvor98w64_zurueck h

/-- Pin: CDQ takes the width arm. -/
theorem pin_wdHw_wdvor99 :
    decodeMulDivWidth [natByte 153] =
      some (.wd (⟨WdBefehl.vor99 WdBreite.w32, 1⟩ : WdDecodiert), []) := by
  have h := (pin_wdvor99_dekode).1
  exact decodeMulDivWidth_wd _ _ _ ext_weist_wdvor99_zurueck h

/-- Pin: the overlapping 64-bit MUL row keeps the unified arm. -/
theorem pin_wdHw_ext_mul64 :
    decodeMulDivWidth [natByte 73, natByte 247, natByte 224] =
      some (.ext (.muldiv ⟨.mulRax .r8, 3⟩), []) :=
  decodeMulDivWidth_prefers_ext _ _ _ pin_ext_wdmul64

/-- Pin: the overlapping 64-bit IMUL row keeps the unified arm. -/
theorem pin_wdHw_ext_imul2 :
    decodeMulDivWidth [natByte 77, natByte 15, natByte 175, natByte 207] =
      some (.ext (.muldiv ⟨.imul2 .r9 .r15, 4⟩), []) :=
  decodeMulDivWidth_prefers_ext _ _ _ pin_ext_wdimul2

/-- The unified chain refuses LOCK on the width row. -/
theorem ext_weist_wdlock_zurueck :
    decodeExt [natByte 240, natByte 247, natByte 225] = none := by
  decide

/-- The unified chain refuses the 8-bit row. -/
theorem ext_weist_wdf6_zurueck :
    decodeExt [natByte 246, natByte 225] = none := by
  decide

/-- The unified chain refuses the 16-bit override row. -/
theorem ext_weist_wdop16_zurueck :
    decodeExt [natByte 102, natByte 247, natByte 225] = none := by
  decide

/-- Planted refusal: LOCK stays refused through the dispatcher. -/
theorem wdHw_nichts_lock :
    decodeMulDivWidth [natByte 240, natByte 247, natByte 225] = none :=
  decodeMulDivWidth_nichts _ ext_weist_wdlock_zurueck wd_nichts_lock

/-- Planted refusal: the 8-bit form stays refused. -/
theorem wdHw_nichts_f6 :
    decodeMulDivWidth [natByte 246, natByte 225] = none :=
  decodeMulDivWidth_nichts _ ext_weist_wdf6_zurueck wd_nichts_f6

/-- Planted refusal: the 16-bit override stays refused. -/
theorem wdHw_nichts_op16 :
    decodeMulDivWidth [natByte 102, natByte 247, natByte 225] = none :=
  decodeMulDivWidth_nichts _ ext_weist_wdop16_zurueck wd_nichts_op16_f7

/-! ## 3. One step: exact evaluation selection over the accepted helpers.

  The unified arm IS the accepted unified evaluator; the width arm
  IS the accepted width evaluator on the `kern` half. Nothing is
  redefined: each arm names its helper. -/

/-- One unified step: Ext through `stepExt`, width through `wdSchritt`
    on the core half. The divide trap is `halt`; refusal is
    `verweigert`. -/
def wdHwSchritt (i : WdHwInstr) (t : FpZustand)
    (b : BereitProfil) : ExtAusgang :=
  match i with
  | .ext j => stepExt j t b
  | .wd d =>
    match wdSchritt d t.kern with
    | .ok s' => .weiter { t with kern := s' }
    | .hardwareHalt => .halt
    | .misslungen => .verweigert

/-- Selection: the unified arm IS the accepted unified step. -/
theorem wdHwSchritt_ext (j : ExtInstr) (t : FpZustand)
    (b : BereitProfil) (o : ExtAusgang)
    (h : stepExt j t b = o) :
    wdHwSchritt (.ext j) t b = o := by
  have e : wdHwSchritt (.ext j) t b = stepExt j t b := rfl
  rw [e, h]

/-- Selection: the width arm IS the accepted width evaluator. -/
theorem wdHwSchritt_wd_ok (d : WdDecodiert) (t : FpZustand)
    (b : BereitProfil) (s' : Zustand)
    (h : wdSchritt d t.kern = .ok s') :
    wdHwSchritt (.wd d) t b = .weiter { t with kern := s' } := by
  have e : wdHwSchritt (.wd d) t b =
      match wdSchritt d t.kern with
      | .ok s' => ExtAusgang.weiter { t with kern := s' }
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-- Selection: the width divide trap IS the unified halt. -/
theorem wdHwSchritt_wd_halt (d : WdDecodiert) (t : FpZustand)
    (b : BereitProfil)
    (h : wdSchritt d t.kern = .hardwareHalt) :
    wdHwSchritt (.wd d) t b = .halt := by
  have e : wdHwSchritt (.wd d) t b =
      match wdSchritt d t.kern with
      | .ok s' => ExtAusgang.weiter { t with kern := s' }
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-- Selection: width refusal is unified refusal. -/
theorem wdHwSchritt_wd_verweigert (d : WdDecodiert) (t : FpZustand)
    (b : BereitProfil)
    (h : wdSchritt d t.kern = .misslungen) :
    wdHwSchritt (.wd d) t b = .verweigert := by
  have e : wdHwSchritt (.wd d) t b =
      match wdSchritt d t.kern with
      | .ok s' => ExtAusgang.weiter { t with kern := s' }
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-! ## 4. The old evaluators are lifted, never redefined.

  At 64 bits the width step IS the accepted 64-bit multiply/divide
  step; 32-bit writes zero-extend exactly like the accepted narrow
  merge. No competing product, quotient or merge is defined here. -/

/-- 64-bit MUL is the accepted 64-bit MUL step. -/
theorem wd_mul64_ist_mulRax (s : Zustand) (src : Register) (l : Nat) :
    wdSchritt ⟨WdBefehl.mul WdBreite.w64 src, l⟩ s =
      mulDivSchritt ⟨.mulRax src, l⟩ s := by
  rfl

/-- 64-bit DIV is the accepted 64-bit DIV step. -/
theorem wd_div64_ist_divRax (s : Zustand) (src : Register) (l : Nat) :
    wdSchritt ⟨WdBefehl.divWd WdBreite.w64 src, l⟩ s =
      mulDivSchritt ⟨.divRax src, l⟩ s := by
  rfl

/-- 64-bit IDIV is the accepted 64-bit IDIV step. -/
theorem wd_idiv64_ist_idivRax (s : Zustand) (src : Register) (l : Nat) :
    wdSchritt ⟨WdBefehl.idivWd WdBreite.w64 src, l⟩ s =
      mulDivSchritt ⟨.idivRax src, l⟩ s := by
  rfl

/-- 64-bit two-operand IMUL is the accepted 64-bit IMUL step. -/
theorem wd_imul2_64_ist_imul2 (s : Zustand) (dst src : Register)
    (l : Nat) :
    wdSchritt ⟨WdBefehl.imul2 WdBreite.w64 dst src, l⟩ s =
      mulDivSchritt ⟨.imul2 dst src, l⟩ s := by
  rfl

/-- A 32-bit width write zero-extends like the accepted narrow merge. -/
theorem wdSchreiben_narrow32 (oldVal v : Wort) :
    wdSchreiben WdBreite.w32 v = mergeRegNarrow .b32 oldVal v := by
  rfl

/-- A 64-bit width write is whole like the accepted narrow merge. -/
theorem wdSchreiben_narrow64 (oldVal v : Wort) :
    wdSchreiben WdBreite.w64 v = mergeRegNarrow .b64 oldVal v := by
  rfl

/-! ## 5. Memory discipline: the width step never touches memory.

  Every success arm carries `speicher := s.speicher`; traps and
  refusals carry no state at all. Memory moves only through the
  TSO issue path (§8), never through a substituted word effect. -/

/-- A successful width step leaves canonical memory alone. -/
theorem wdSchritt_speicher (d : WdDecodiert) (s s' : Zustand)
    (h : wdSchritt d s = MulDivErgebnis.ok s') :
    s'.speicher = s.speicher := by
  unfold wdSchritt at h
  cases hlen : laengeOk d.laenge with
  | false =>
    simp [hlen] at h
  | true =>
    simp [hlen] at h
    cases hbef : d.befehl with
    | mul w src =>
      cases w with
      | w32 =>
        simp [hbef] at h
        cases h
        rfl
      | w64 =>
        simp [hbef] at h
        cases h
        rfl
    | divWd w src =>
      cases w with
      | w32 =>
        simp [hbef] at h
        cases hq : divWeitU32 (s.register Register.rdx)
          (s.register Register.rax) (s.register src) with
        | some qr =>
          simp [hq] at h
          cases h
          rfl
        | none =>
          simp [hq] at h
      | w64 =>
        simp [hbef] at h
        cases hq : divWeitU (s.register Register.rdx)
          (s.register Register.rax) (s.register src) with
        | some qr =>
          simp [hq] at h
          cases h
          rfl
        | none =>
          simp [hq] at h
    | idivWd w src =>
      cases w with
      | w32 =>
        simp [hbef] at h
        cases hq : divWeitS32 (s.register Register.rdx)
          (s.register Register.rax) (s.register src) with
        | some qr =>
          simp [hq] at h
          cases h
          rfl
        | none =>
          simp [hq] at h
      | w64 =>
        simp [hbef] at h
        cases hq : divWeitS (s.register Register.rdx)
          (s.register Register.rax) (s.register src) with
        | some qr =>
          simp [hq] at h
          cases h
          rfl
        | none =>
          simp [hq] at h
    | imul2 w dst src =>
      simp [hbef] at h
      cases h
      rfl
    | imul3 w dst src imm =>
      simp [hbef] at h
      cases h
      rfl
    | vor98 w =>
      simp [hbef] at h
      cases h
      cases w <;> rfl
    | vor99 w =>
      simp [hbef] at h
      cases h
      cases w <;> rfl

/-! ## 6. Machine adapter: the width family on the coherent machine.

  The producer plug instantiates `HwAdapter WdDecodiert` with the
  accepted API: a successful width step re-embeds core data over the
  shared memory; traps and refusals admit no successor state (the
  divide fault is an outcome in §7, never an `Option`-plugged
  successor, following the `adapterFault670` discipline). -/

/-- The width plug: one checked width event step on the coherent
    machine. `none` = trap or refusal, never a silent successor. -/
def adapterMulDivWidth : HwAdapter WdDecodiert :=
  ⟨fun m c d =>
    match wdSchritt d (projZustand m c) with
    | .ok s' =>
      some (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
    | .hardwareHalt => none
    | .misslungen => none⟩

/-- Every adapter step preserves well-formedness: only core data
    moves, profiles are untouched. -/
theorem adapterMulDivWidth_wf (m : HwMaschine) (c : Nat)
    (d : WdDecodiert) (m' : HwMaschine) (hwf : HwWf m)
    (h : (adapterMulDivWidth).schritt m c d = some m') :
    HwWf m' := by
  unfold adapterMulDivWidth at h
  simp only at h
  cases hsch : wdSchritt d (projZustand m c) with
  | ok s' =>
    rw [hsch] at h
    simp only at h
    cases h
    unfold setKernVonFp
    exact setKernDaten_wf _ _ _ hwf
  | hardwareHalt =>
    rw [hsch] at h
    simp only at h
    cases h
  | misslungen =>
    rw [hsch] at h
    simp only at h
    cases h

/-- Agreement: the adapter succeeds exactly where the accepted width
    step succeeds, with the successor core data re-embedded. -/
theorem adapterMulDivWidth_ok (m : HwMaschine) (c : Nat)
    (d : WdDecodiert) (s' : Zustand)
    (h : wdSchritt d (projZustand m c) = .ok s') :
    (adapterMulDivWidth).schritt m c d =
      some (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩) := by
  unfold adapterMulDivWidth
  simp only [h]

/-- The successor core sees the accepted successor registers over
    the shared memory. -/
theorem adapterMulDivWidth_proj (m : HwMaschine) (c : Nat)
    (d : WdDecodiert) (s' : Zustand)
    (h : wdSchritt d (projZustand m c) = .ok s') :
    ((setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩).kerne c).register =
      s'.register ∧
    (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩).mem = m.mem ∧
    s'.speicher = m.mem := by
  refine ⟨setKernVonFp_register m c _,
    setKernVonFp_speicher m c _, ?_⟩
  have hmem := wdSchritt_speicher d (projZustand m c) s' h
  have hproj : (projZustand m c).speicher = m.mem := rfl
  rw [hproj] at hmem
  exact hmem

/-- A bad decode length admits no adapter step. -/
theorem adapterMulDivWidth_verweigert_bei_laenge (m : HwMaschine)
    (c : Nat) (d : WdDecodiert)
    (h : laengeOk d.laenge = false) :
    (adapterMulDivWidth).schritt m c d = none := by
  have hstep := wd_laenge_misslungen d (projZustand m c) h
  unfold adapterMulDivWidth
  simp only [hstep]

/-- A divide trap admits no adapter successor: halt is an outcome
    (§7), never a plugged state. -/
theorem adapterMulDivWidth_verweigert_bei_halt (m : HwMaschine)
    (c : Nat) (d : WdDecodiert)
    (h : wdSchritt d (projZustand m c) = .hardwareHalt) :
    (adapterMulDivWidth).schritt m c d = none := by
  unfold adapterMulDivWidth
  simp only [h]

/-! ## 7. Machine outcome: the divide fault as an outcome.

  Reuses the accepted `HwRegAusgang` unchanged (never edited here):
  success re-embeds core data, the divide trap is `halt`, refusal is
  `verweigert`. A halt carries no state and no register claim. -/

/-- One width machine step on core `c`: the accepted width step on
    the core projection, re-embedded on success. Memory and buffers
    are kept by construction (§5). -/
def wdHwRegSchritt (m : HwMaschine) (c : Nat)
    (d : WdDecodiert) : HwRegAusgang :=
  match wdSchritt d (projZustand m c) with
  | .ok s' => .weiter (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
  | .hardwareHalt => .halt
  | .misslungen => .verweigert

/-- Selection: a successful width step continues on the machine. -/
theorem wdHwRegSchritt_weiter (m : HwMaschine) (c : Nat)
    (d : WdDecodiert) (s' : Zustand)
    (h : wdSchritt d (projZustand m c) = .ok s') :
    wdHwRegSchritt m c d =
      .weiter (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩) := by
  have e : wdHwRegSchritt m c d =
      match wdSchritt d (projZustand m c) with
      | .ok s' => HwRegAusgang.weiter
        (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-- Selection: the width divide trap is the machine halt. -/
theorem wdHwRegSchritt_halt (m : HwMaschine) (c : Nat)
    (d : WdDecodiert)
    (h : wdSchritt d (projZustand m c) = .hardwareHalt) :
    wdHwRegSchritt m c d = .halt := by
  have e : wdHwRegSchritt m c d =
      match wdSchritt d (projZustand m c) with
      | .ok s' => HwRegAusgang.weiter
        (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-- Selection: width refusal is machine refusal. -/
theorem wdHwRegSchritt_verweigert (m : HwMaschine) (c : Nat)
    (d : WdDecodiert)
    (h : wdSchritt d (projZustand m c) = .misslungen) :
    wdHwRegSchritt m c d = .verweigert := by
  have e : wdHwRegSchritt m c d =
      match wdSchritt d (projZustand m c) with
      | .ok s' => HwRegAusgang.weiter
        (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-- A machine halt carries no successor: the faulting step makes no
    register claim on that arm. -/
theorem wdHwRegSchritt_halt_ist_kein_weiter (m : HwMaschine)
    (c : Nat) (d : WdDecodiert) (m' : HwMaschine)
    (h : wdHwRegSchritt m c d = .halt) :
    wdHwRegSchritt m c d ≠ .weiter m' := by
  rw [h]
  intro hc
  cases hc

/-- A machine continue preserves well-formedness. -/
theorem wdHwRegSchritt_weiter_wf (m : HwMaschine) (c : Nat)
    (d : WdDecodiert) (m' : HwMaschine) (hwf : HwWf m)
    (h : wdHwRegSchritt m c d = .weiter m') :
    HwWf m' := by
  have e : wdHwRegSchritt m c d =
      match wdSchritt d (projZustand m c) with
      | .ok s' => HwRegAusgang.weiter
        (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e] at h
  cases hsch : wdSchritt d (projZustand m c) with
  | ok s' =>
    rw [hsch] at h
    simp only at h
    cases h
    unfold setKernVonFp
    exact setKernDaten_wf _ _ _ hwf
  | hardwareHalt =>
    rw [hsch] at h
    simp only at h
    cases h
  | misslungen =>
    rw [hsch] at h
    simp only at h
    cases h

/-! ## 8. Joint witness: two cores, family steps, buffered store.

  Both cores run accepted width steps over one shared canonical
  memory (core 0 divides `17 / 5`, core 1 multiplies `17 * 5`);
  afterwards core 0 issues a buffered byte store that only the owner
  observes by forwarding, and the drain changes actual shared memory
  from 0 to 42. A zero divisor halts and a bad length refuses beside
  the run. Every claim projects to plain values before `decide`
  (machines contain functions); the general equations pin the full
  states. -/

/-- Witness registers: RDX:RAX holds 17, RCX holds 5. -/
def wdHwWitReg : Register → Wort := fun q =>
  if q = Register.rax then 17
  else if q = Register.rdx then 0
  else if q = Register.rcx then 5
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness registers with a zero divisor in RCX. -/
def wdHwWitRegNull : Register → Wort := fun q =>
  if q = Register.rax then 17
  else if q = Register.rdx then 0
  else if q = Register.rcx then 0
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness cores over a register file: both cores run at 4096. -/
def wdHwWitKern (r : Register → Wort) : Nat → HwKern
  | 0 => ⟨r, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨r, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon. -/
def wdHwWitStart : HwMaschine :=
  ⟨zeugeSpeicher, wdHwWitKern wdHwWitReg, fun _ => [],
    basisHw, fun _ => basisBereit⟩

/-- Witness machine with a zero divisor on core 0. -/
def wdHwWitStartNull : HwMaschine :=
  ⟨zeugeSpeicher, wdHwWitKern wdHwWitRegNull, fun _ => [],
    basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed. -/
theorem wdHwWitStart_wf : HwWf wdHwWitStart := by
  intro c f _
  cases f <;> rfl

/-- The zero-divisor machine is well-formed. -/
theorem wdHwWitStartNull_wf : HwWf wdHwWitStartNull := by
  intro c f _
  cases f <;> rfl

/-- Core 0 divides `17 / 5` through the machine outcome. -/
def wdHwOutDiv : HwRegAusgang :=
  wdHwRegSchritt wdHwWitStart 0 ⟨WdBefehl.divWd .w32 .rcx, 2⟩

/-- Core 1 multiplies `17 * 5` through the machine outcome. -/
def wdHwOutMul : HwRegAusgang :=
  wdHwRegSchritt wdHwWitStart 1 ⟨WdBefehl.mul .w32 .rcx, 2⟩

/-- Read a core register out of a machine outcome. -/
def wdHwRegOut (o : HwRegAusgang) (c : Nat) (q : Register) :
    Option Wort :=
  match o with
  | .weiter m => some ((m.kerne c).register q)
  | _ => none

/-- Core 0 quotient: EAX holds 3. -/
theorem wdHw_div_rax :
    wdHwRegOut wdHwOutDiv 0 Register.rax = some 3 := by
  decide

/-- Core 0 remainder: EDX holds 2. -/
theorem wdHw_div_rdx :
    wdHwRegOut wdHwOutDiv 0 Register.rdx = some 2 := by
  decide

/-- Core 1 product: EAX holds 85. -/
theorem wdHw_mul_rax :
    wdHwRegOut wdHwOutMul 1 Register.rax = some 85 := by
  decide

/-- Core 1 high word: EDX holds 0. -/
theorem wdHw_mul_rdx :
    wdHwRegOut wdHwOutMul 1 Register.rdx = some 0 := by
  decide

/-- Witness data address. -/
def wdHwWitAdr : Adresse := BitVec.ofNat 64 8192

/-- Witness TSO start: canonical memory, empty buffers. -/
def wdHwWitTso0 : TSOZustand := ⟨zeugeSpeicher, fun _ => []⟩

/-- Core 0 issues byte 42 at the data cell. -/
def wdHwWitTso1 : Option TSOZustand :=
  issueByte wdHwWitTso0 0 wdHwWitAdr (BitVec.ofNat 8 42)

/-- Core 0 observes its own byte (forwarding). -/
def wdHwWitEigen : Option (Option Byte) :=
  match wdHwWitTso1 with
  | some s => some (loadByte s 0 wdHwWitAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def wdHwWitFremd : Option (Option Byte) :=
  match wdHwWitTso1 with
  | some s => some (loadByte s 1 wdHwWitAdr)
  | none => none

/-- Core 0 drains its oldest entry. -/
def wdHwWitTso2 : Option TSOZustand :=
  match wdHwWitTso1 with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def wdHwWitNachFlush : Option (Option Byte) :=
  match wdHwWitTso2 with
  | some s => some (some (s.mem.bytes wdHwWitAdr))
  | none => none

/-- Core 1 reads the drained byte from shared memory. -/
def wdHwWitFremdNach : Option (Option Byte) :=
  match wdHwWitTso2 with
  | some s => some (loadByte s 1 wdHwWitAdr)
  | none => none

/-- The data cell starts zeroed. -/
theorem wdHw_anfang_null :
    zeugeSpeicher.bytes wdHwWitAdr = BitVec.ofNat 8 0 := by
  rfl

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem wdHw_weiterleitung :
    wdHwWitEigen = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem wdHw_fremd_alt :
    wdHwWitFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem wdHw_spuelung_aendert_speicher :
    wdHwWitNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem wdHw_fremd_neu :
    wdHwWitFremdNach = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- A zero divisor halts the machine step with no successor. -/
theorem wdHw_nullteiler_halt :
    wdHwRegSchritt wdHwWitStartNull 0
      (⟨WdBefehl.divWd WdBreite.w32 Register.rcx, 2⟩ : WdDecodiert) =
      .halt := by
  have h0 : (trunc .b32 ((projZustand wdHwWitStartNull 0).register
      Register.rcx)).toNat = 0 := by
    decide
  have hqr := divWeitU32_verweigert_bei_null
    ((projZustand wdHwWitStartNull 0).register Register.rdx)
    ((projZustand wdHwWitStartNull 0).register Register.rax)
    ((projZustand wdHwWitStartNull 0).register Register.rcx) h0
  have hstep := wd_div32_halt
    (⟨WdBefehl.divWd WdBreite.w32 Register.rcx, 2⟩ : WdDecodiert)
    (projZustand wdHwWitStartNull 0) Register.rcx (by decide) rfl hqr
  exact wdHwRegSchritt_halt _ _ _ hstep

/-- A bad decode length refuses the machine step. -/
theorem wdHw_schlechte_laenge_verweigert :
    wdHwRegSchritt wdHwWitStart 0
      (⟨WdBefehl.mul WdBreite.w32 Register.rcx, 0⟩ : WdDecodiert) =
      .verweigert := by
  have hstep := wd_laenge_misslungen
    (⟨WdBefehl.mul WdBreite.w32 Register.rcx, 0⟩ : WdDecodiert)
    (projZustand wdHwWitStart 0) (by decide)
  exact wdHwRegSchritt_verweigert _ _ _ hstep

/-- The joint witness: a reached two-core width run (divide on core
    0, multiply on core 1) beside a buffered store that only the
    owner forwards and a drain that changes actual shared memory
    from 0 to 42 -- with the halt, refusal and decode refusals beside
    it. Non-degenerate: the drain changes actual shared memory. -/
theorem wdHw_zeuge :
    wdHwRegOut wdHwOutDiv 0 Register.rax = some 3 ∧
      wdHwRegOut wdHwOutDiv 0 Register.rdx = some 2 ∧
      wdHwRegOut wdHwOutMul 1 Register.rax = some 85 ∧
      wdHwRegOut wdHwOutMul 1 Register.rdx = some 0 ∧
      wdHwWitEigen = some (some (BitVec.ofNat 8 42)) ∧
      wdHwWitFremd = some (some (BitVec.ofNat 8 0)) ∧
      wdHwWitNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      wdHwWitFremdNach = some (some (BitVec.ofNat 8 42)) ∧
      zeugeSpeicher.bytes wdHwWitAdr = BitVec.ofNat 8 0 ∧
      HwWf wdHwWitStart ∧
      wdHwRegSchritt wdHwWitStartNull 0
        (⟨WdBefehl.divWd WdBreite.w32 Register.rcx, 2⟩ :
          WdDecodiert) = .halt ∧
      wdHwRegSchritt wdHwWitStart 0
        (⟨WdBefehl.mul WdBreite.w32 Register.rcx, 0⟩ :
          WdDecodiert) = .verweigert ∧
      decodeMulDivWidth [natByte 240, natByte 247, natByte 225] =
        none := by
  refine ⟨wdHw_div_rax, wdHw_div_rdx, wdHw_mul_rax, wdHw_mul_rdx,
    wdHw_weiterleitung, wdHw_fremd_alt, wdHw_spuelung_aendert_speicher,
    wdHw_fremd_neu, wdHw_anfang_null, wdHwWitStart_wf,
    wdHw_nullteiler_halt, wdHw_schlechte_laenge_verweigert,
    wdHw_nichts_lock⟩

/- CUTS:
   Proved here: the accepted width family (`MulDivWidthHardwareForms`
   over the accepted 64-bit `MulDiv` evaluator) connected to the
   coherent machine and the unified byte dispatcher -- the dispatcher
   prefers the accepted unified chain (no pilot or extension form is
   shadowed, overlapping 64-bit rows keep their unified arm, new
   32-bit/immediate/preparation rows take the width arm), one unified
   step selects the accepted evaluators exactly, 64-bit width steps
   ARE the accepted 64-bit steps and 32-bit writes zero-extend like
   the accepted narrow merge, width success never touches memory,
   the `HwAdapter WdDecodiert` plug preserves `HwWf` with exact
   agreement and planted refusals, the divide fault is a machine
   outcome reusing the accepted `HwRegAusgang`, and a reached
   two-core run with owner-only forwarding and a memory-changing
   drain stands beside halt/refusal evidence.
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are the accepted
     canonical subsets with self-consistency only, not x86 truth.
     Silicon assumptions named: REX.W promotion, 32-bit
     zero-extension on writes, `#DE` on divisor zero or quotient
     overflow, CF/OF carry rules and the kept-undefined-flag
     modelling are inherited unchanged from the accepted family
     file; nothing here re-checks them against silicon.
   - No 8/16-bit multiply/divide (refused: `wdHw_nichts_f6` and the
     family's essential OPEN), no one-operand IMUL digit `/5`, no
     memory-addressed forms, no LOCK path (refused).
   - No source/IR/ABI/loader/entry/budget link, no per-access
     target-to-W/GX simulation, no whole-word atomicity beyond
     byte drains, no timing/power behaviour.
   - The overlapping 64-bit rows are covered twice (unified
     `muldiv` arm and §4 lift equations) by construction, never
     executed twice: the dispatcher takes the unified arm first.
-/

#print axioms decodeMulDivWidth
#print axioms wdHwSchritt
#print axioms wd_mul64_ist_mulRax
#print axioms wdSchreiben_narrow32
#print axioms wdSchritt_speicher
#print axioms adapterMulDivWidth
#print axioms adapterMulDivWidth_wf
#print axioms adapterMulDivWidth_ok
#print axioms wdHwRegSchritt_halt
#print axioms wdHwRegSchritt_halt_ist_kein_weiter
#print axioms wdHwWitStart_wf
#print axioms wdHw_zeuge

end Gabbro.Grammatik.X86
