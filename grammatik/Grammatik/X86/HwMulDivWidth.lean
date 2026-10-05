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

end Gabbro.Grammatik.X86
