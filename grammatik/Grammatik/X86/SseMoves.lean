/-
  File:      Grammatik/X86/SseMoves.lean
  Subject:   SSE/SSE2 moves, loads, stores and unpack connected to the
             coherent machine.

  Lane 1355: covers the ledger-1341 `fehlt` rows 0F 10/11/28/29
  (MOVUPS/MOVUPD/MOVAPS/MOVAPD), the MOVSS/MOVSD stores (loads already
  decode), MOVLPS/MOVHPS/MOVLHPS/MOVHLPS (0F 12/13/16/17), UNPCKL/UNPCKH
  PS/PD (0F 14/15) and the non-temporal stores (0F 2B/C3, 66 0F 2B/E7).
  MOVDQA/MOVDQU stay with lane 686 (`VectorIntegerHardwareForms`,
  never redefined here). Decoder plus encoder with round trip, pure
  XMM semantics reusing the accepted `Vektor` functions, a
  `HwAdapter` plug over the coherent machine in the style of
  `HwMulDivWidth`, and a reached two-core witness. No hardware
  correspondence beyond self-consistency (see CUTS).
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Kern.Codec
import Grammatik.X86.Kern.Vektor
import Grammatik.X86.Speicher.Speicher
import Grammatik.X86.TSO.Kern.TSO
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloat
import Grammatik.X86.Befehle.Vektor.VectorCodec
import Grammatik.X86.Hw.Grundlage.HardwareExecution

namespace Gabbro.Grammatik.X86

/-- SSE/SSE2 move and unpack rows of this lane. Register operands are
    XMM; memory operands reuse base-plus-displacement addressing over
    the GPR file. MOVDQA/MOVDQU are NOT here (lane 686 owns them). -/
inductive SseMoveOp where
  | movupsLd (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | movupsSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movapsLd (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | movapsSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movupdLd (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | movupdSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movapdLd (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | movapdSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movssSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movsdSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movlpsLd (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | movlpsSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movhpsLd (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | movhpsSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movlhpsRR (dst src : XmmReg)
  | movhlpsRR (dst src : XmmReg)
  | unpcklpsRR (dst src : XmmReg)
  | unpckhpsRR (dst src : XmmReg)
  | unpcklpdRR (dst src : XmmReg)
  | unpckhpdRR (dst src : XmmReg)
  | movntpsSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movntpdSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movntdqSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movntiSt (base : Register) (src : Register) (disp : BitVec 32)
  | movdLdRR (dst : XmmReg) (src : Register)
  | movdStRR (dst : Register) (src : XmmReg)
  | movqLdRR (dst : XmmReg) (src : XmmReg)
  | movqStRR (dst : XmmReg) (src : XmmReg)
  deriving DecidableEq, Repr

/-! ## 1. Canonical byte encodings.

  Always with a canonical REX prefix (W=0, X=0: `64 + 4*R + B`,
  exactly like the accepted `vectorRex`), then the legacy prefix
  (`66` = 102 for the PD rows, `F3` = 243 for the MOVSS store,
  `F2` = 242 for the MOVSD store), the `0F` escape, the opcode byte
  and a ModRM: mod=3 register-direct for the `*RR` rows (reg=dst,
  r/m=src), mod=2 base+disp32 with the pilot SIB rule for the memory
  rows (reg=XMM side, r/m=base; for MOVNTI the reg field is the GPR
  source). Intel SDM Vol. 2A/2B opcode map (edition 093): MOVUPS
  `0F 10/11`, MOVLPS `0F 12/13`, UNPCKLPS `0F 14`, UNPCKHPS `0F 15`,
  MOVHPS `0F 16/17`, MOVAPS `0F 28/29`, MOVNTPS `0F 2B`,
  MOVD `66 0F 6E/7E`, MOVNTI `0F C3`, MOVUPD `66 0F 10/11`,
  MOVAPD `66 0F 28/29`, UNPCKLPD/UNPCKHPD `66 0F 14/15`,
  MOVNTPD `66 0F 2B`, MOVNTDQ `66 0F E7`, MOVSS store `F3 0F 11`,
  MOVSD store `F2 0F 11`, MOVQ load `F3 0F 7E /r`, MOVQ store
  `66 0F D6 /r` (register forms only). MOVLHPS is `0F 12 /r` mod=3,
  MOVHLPS `0F 16 /r` mod=3. -/

/-- Canonical REX byte for one move row (W=0, X=0). -/
def sseRex (rB bB : Nat) : Byte := natByte (64 + 4 * rB + bB)

/-- Legacy mandatory prefix byte, if any: 102 = `66`, 243 = `F3`,
    242 = `F2`. -/
def ssePrefix : SseMoveOp → Option Nat
  | .movupdLd _ _ _ => some 102
  | .movupdSt _ _ _ => some 102
  | .movapdLd _ _ _ => some 102
  | .movapdSt _ _ _ => some 102
  | .movsdSt _ _ _ => some 242
  | .movssSt _ _ _ => some 243
  | .unpcklpdRR _ _ => some 102
  | .unpckhpdRR _ _ => some 102
  | .movntpdSt _ _ _ => some 102
  | .movntdqSt _ _ _ => some 102
  | .movdLdRR _ _ => some 102
  | .movdStRR _ _ => some 102
  | .movqLdRR _ _ => some 243
  | .movqStRR _ _ => some 102
  | _ => none

/-- Opcode byte after the `0F` escape. -/
def sseSecond : SseMoveOp → Nat
  | .movupsLd _ _ _ => 16
  | .movupsSt _ _ _ => 17
  | .movupdLd _ _ _ => 16
  | .movupdSt _ _ _ => 17
  | .movapsLd _ _ _ => 40
  | .movapsSt _ _ _ => 41
  | .movapdLd _ _ _ => 40
  | .movapdSt _ _ _ => 41
  | .movssSt _ _ _ => 17
  | .movsdSt _ _ _ => 17
  | .movlpsLd _ _ _ => 18
  | .movlpsSt _ _ _ => 19
  | .movhpsLd _ _ _ => 22
  | .movhpsSt _ _ _ => 23
  | .movlhpsRR _ _ => 18
  | .movhlpsRR _ _ => 22
  | .unpcklpsRR _ _ => 20
  | .unpckhpsRR _ _ => 21
  | .unpcklpdRR _ _ => 20
  | .unpckhpdRR _ _ => 21
  | .movntpsSt _ _ _ => 43
  | .movntpdSt _ _ _ => 43
  | .movntdqSt _ _ _ => 231
  | .movntiSt _ _ _ => 195
  | .movdLdRR _ _ => 110
  | .movdStRR _ _ => 126
  | .movqLdRR _ _ => 126
  | .movqStRR _ _ => 214

/-- Canonical byte encoding of one covered row. Register rows are 4
    bytes without a legacy prefix (`REX 0F op modrm`) and 5 with one;
    memory rows add ModRM plus disp32 (plus the SIB byte for a base
    with low code 4, exactly like the pilot `encode`). -/
def encodeSse : SseMoveOp → List Byte
  | op@(.movlhpsRR dst src) =>
    [sseRex (xmmHigh dst) (xmmHigh src), natByte 15,
      natByte (sseSecond op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.movhlpsRR dst src) =>
    [sseRex (xmmHigh dst) (xmmHigh src), natByte 15,
      natByte (sseSecond op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.unpcklpsRR dst src) =>
    [sseRex (xmmHigh dst) (xmmHigh src), natByte 15,
      natByte (sseSecond op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.unpckhpsRR dst src) =>
    [sseRex (xmmHigh dst) (xmmHigh src), natByte 15,
      natByte (sseSecond op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.unpcklpdRR dst src) =>
    [sseRex (xmmHigh dst) (xmmHigh src), natByte 102, natByte 15,
      natByte (sseSecond op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.unpckhpdRR dst src) =>
    [sseRex (xmmHigh dst) (xmmHigh src), natByte 102, natByte 15,
      natByte (sseSecond op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.movdLdRR dst src) =>
    [sseRex (xmmHigh dst) (regHigh src), natByte 102, natByte 15,
      natByte (sseSecond op), modrmReg (xmmLow dst) (regLow src)]
  | op@(.movdStRR dst src) =>
    [sseRex (regHigh dst) (xmmHigh src), natByte 102, natByte 15,
      natByte (sseSecond op), modrmReg (regLow dst) (xmmLow src)]
  | op@(.movqLdRR dst src) =>
    [sseRex (xmmHigh dst) (xmmHigh src), natByte 243, natByte 15,
      natByte (sseSecond op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.movqStRR dst src) =>
    [sseRex (xmmHigh dst) (xmmHigh src), natByte 102, natByte 15,
      natByte (sseSecond op), modrmReg (xmmLow dst) (xmmLow src)]
  | op =>
    let pref : List Byte :=
      match ssePrefix op with
      | some p => [natByte p]
      | none => []
    let head : List Byte :=
      match op with
      | .movupsLd dst base _ =>
        [sseRex (xmmHigh dst) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow dst) (regLow base)]
      | .movupsSt base src _ =>
        [sseRex (xmmHigh src) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow src) (regLow base)]
      | .movapsLd dst base _ =>
        [sseRex (xmmHigh dst) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow dst) (regLow base)]
      | .movapsSt base src _ =>
        [sseRex (xmmHigh src) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow src) (regLow base)]
      | .movupdLd dst base _ =>
        [sseRex (xmmHigh dst) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow dst) (regLow base)]
      | .movupdSt base src _ =>
        [sseRex (xmmHigh src) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow src) (regLow base)]
      | .movapdLd dst base _ =>
        [sseRex (xmmHigh dst) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow dst) (regLow base)]
      | .movapdSt base src _ =>
        [sseRex (xmmHigh src) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow src) (regLow base)]
      | .movssSt base src _ =>
        [sseRex (xmmHigh src) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow src) (regLow base)]
      | .movsdSt base src _ =>
        [sseRex (xmmHigh src) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow src) (regLow base)]
      | .movlpsLd dst base _ =>
        [sseRex (xmmHigh dst) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow dst) (regLow base)]
      | .movlpsSt base src _ =>
        [sseRex (xmmHigh src) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow src) (regLow base)]
      | .movhpsLd dst base _ =>
        [sseRex (xmmHigh dst) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow dst) (regLow base)]
      | .movhpsSt base src _ =>
        [sseRex (xmmHigh src) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow src) (regLow base)]
      | .movntpsSt base src _ =>
        [sseRex (xmmHigh src) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow src) (regLow base)]
      | .movntpdSt base src _ =>
        [sseRex (xmmHigh src) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow src) (regLow base)]
      | .movntdqSt base src _ =>
        [sseRex (xmmHigh src) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (xmmLow src) (regLow base)]
      | .movntiSt base src _ =>
        [sseRex (regHigh src) (regHigh base)] ++ pref ++
          [natByte 15, natByte (sseSecond op),
            modrmMem (regLow src) (regLow base)]
      | _ => []
    let disp : BitVec 32 :=
      match op with
      | .movupsLd _ _ d => d
      | .movupsSt _ _ d => d
      | .movapsLd _ _ d => d
      | .movapsSt _ _ d => d
      | .movupdLd _ _ d => d
      | .movupdSt _ _ d => d
      | .movapdLd _ _ d => d
      | .movapdSt _ _ d => d
      | .movssSt _ _ d => d
      | .movsdSt _ _ d => d
      | .movlpsLd _ _ d => d
      | .movlpsSt _ _ d => d
      | .movhpsLd _ _ d => d
      | .movhpsSt _ _ d => d
      | .movntpsSt _ _ d => d
      | .movntpdSt _ _ d => d
      | .movntdqSt _ _ d => d
      | .movntiSt _ _ d => d
      | _ => BitVec.ofNat 32 0
    let sib : Bool :=
      match op with
      | .movupsLd _ base _ => decide (regLow base = 4)
      | .movupsSt base _ _ => decide (regLow base = 4)
      | .movapsLd _ base _ => decide (regLow base = 4)
      | .movapsSt base _ _ => decide (regLow base = 4)
      | .movupdLd _ base _ => decide (regLow base = 4)
      | .movupdSt base _ _ => decide (regLow base = 4)
      | .movapdLd _ base _ => decide (regLow base = 4)
      | .movapdSt base _ _ => decide (regLow base = 4)
      | .movssSt base _ _ => decide (regLow base = 4)
      | .movsdSt base _ _ => decide (regLow base = 4)
      | .movlpsLd _ base _ => decide (regLow base = 4)
      | .movlpsSt base _ _ => decide (regLow base = 4)
      | .movhpsLd _ base _ => decide (regLow base = 4)
      | .movhpsSt base _ _ => decide (regLow base = 4)
      | .movntpsSt base _ _ => decide (regLow base = 4)
      | .movntpdSt base _ _ => decide (regLow base = 4)
      | .movntdqSt base _ _ => decide (regLow base = 4)
      | .movntiSt base _ _ => decide (regLow base = 4)
      | _ => false
    if sib then head ++ natByte 36 :: leBytes32 disp
    else head ++ leBytes32 disp

/-! ## 2. Canonical decoder.

  The decoder parses bytes, never encode-equality. Only the canonical
  REX prefix (`64 + 4*R + B`: W=0, X=0), then an optional legacy
  prefix (`66`/`F3`/`F2`), the `0F` escape, the opcode byte and a
  ModRM: mod=3 for the register rows (reg=first operand, r/m=second;
  GPR side via `codeReg` for MOVD/MOVNTI) and mod=2 base+disp32 with
  the pilot SIB rule for the memory rows. Anything else refuses with
  `none`. `0F 12`/`0F 16` are shared: mod=2 is the partial load,
  mod=3 the register shuffle (66-prefixed mod=3 is undefined and
  refuses); `0F 14/15` mod=2 is undefined and refuses. -/

/-- A decoded move row: the form plus its decode length (checked
    `1..15` data, exactly as the pilot `Decodiert`). -/
structure SseDecodiert where
  op : SseMoveOp
  laenge : Nat
  deriving DecidableEq, Repr

/-- REX extension bits of a canonical REX byte (W=0, X=0 only;
    every other first byte refuses). -/
def sseRexBits : Nat → Option (Nat × Nat)
  | 64 => some (0, 0)
  | 65 => some (0, 1)
  | 68 => some (1, 0)
  | 69 => some (1, 1)
  | _ => none

/-- Decode one register-direct ModRM byte: mod must be 3. `pref` is
    0 (none), 1 (`66`), 2 (`F3`); `F2` admits no register row. -/
def decodeSseReg (pref rBit bBit opByte : Nat) :
    List Byte → Option (SseMoveOp × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if byteNat m / 64 == 3 then
      match opByte, pref with
      | 18, 0 =>
        match codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
        | some dst, some src => some ((.movlhpsRR dst src), rest)
        | _, _ => none
      | 22, 0 =>
        match codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
        | some dst, some src => some ((.movhlpsRR dst src), rest)
        | _, _ => none
      | 20, 0 =>
        match codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
        | some dst, some src => some ((.unpcklpsRR dst src), rest)
        | _, _ => none
      | 20, 1 =>
        match codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
        | some dst, some src => some ((.unpcklpdRR dst src), rest)
        | _, _ => none
      | 21, 0 =>
        match codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
        | some dst, some src => some ((.unpckhpsRR dst src), rest)
        | _, _ => none
      | 21, 1 =>
        match codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
        | some dst, some src => some ((.unpckhpdRR dst src), rest)
        | _, _ => none
      | 110, 1 =>
        match codeXmm (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
        | some dst, some src => some ((.movdLdRR dst src), rest)
        | _, _ => none
      | 126, 1 =>
        match codeReg (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
        | some dst, some src => some ((.movdStRR dst src), rest)
        | _, _ => none
      | 126, 2 =>
        match codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
        | some dst, some src => some ((.movqLdRR dst src), rest)
        | _, _ => none
      | 214, 1 =>
        match codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
        | some dst, some src => some ((.movqStRR dst src), rest)
        | _, _ => none
      | _, _ => none
    else none

/-- Memory-row dispatch after ModRM and displacement: the opcode
    byte selects load vs store and the prefix selects the shape;
    mod must be 2 (base+disp32 with the pilot SIB rule), and the reg
    field is the XMM side except for MOVNTI (GPR source). -/
def decodeSseMemNach (pref rBit bBit opByte reg rm : Nat) (d : BitVec 32)
    (rest3 : List Byte) : Option (SseMoveOp × List Byte) :=
  match codeXmm (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
  | some xx, some base =>
    match pref, opByte with
    | 0, 16 => some ((.movupsLd xx base d), rest3)
    | 0, 17 => some ((.movupsSt base xx d), rest3)
    | 0, 40 => some ((.movapsLd xx base d), rest3)
    | 0, 41 => some ((.movapsSt base xx d), rest3)
    | 0, 18 => some ((.movlpsLd xx base d), rest3)
    | 0, 19 => some ((.movlpsSt base xx d), rest3)
    | 0, 22 => some ((.movhpsLd xx base d), rest3)
    | 0, 23 => some ((.movhpsSt base xx d), rest3)
    | 0, 43 => some ((.movntpsSt base xx d), rest3)
    | 1, 16 => some ((.movupdLd xx base d), rest3)
    | 1, 17 => some ((.movupdSt base xx d), rest3)
    | 1, 40 => some ((.movapdLd xx base d), rest3)
    | 1, 41 => some ((.movapdSt base xx d), rest3)
    | 1, 43 => some ((.movntpdSt base xx d), rest3)
    | 1, 231 => some ((.movntdqSt base xx d), rest3)
    | 2, 17 => some ((.movssSt base xx d), rest3)
    | 3, 17 => some ((.movsdSt base xx d), rest3)
    | 0, 195 =>
      match codeReg (rBit * 8 + reg) with
      | some src => some ((.movntiSt base src d), rest3)
      | none => none
    | _, _ => none
  | _, _ => none

def decodeSseMem (pref rBit bBit opByte : Nat) :
    List Byte → Option (SseMoveOp × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if byteNat m / 64 == 2 then
      if rm == 4 then
        match rest with
        | [] => none
        | sib :: rest2 =>
          if byteNat sib == 36 then
            match parseLe32 rest2 with
            | none => none
            | some (d, rest3) => decodeSseMemNach pref rBit bBit opByte reg rm d rest3
          else none
      else
        match parseLe32 rest with
        | none => none
        | some (d, rest3) => decodeSseMemNach pref rBit bBit opByte reg rm d rest3
    else none

/-- Shared `0F 12` / `0F 16` rows (no prefix only): mod=3 is the
    register shuffle (length 4), mod=2 the partial load (length
    8 plus SIB); anything else refuses. -/
def decodeSseTeils (rBit bBit opByte : Nat) :
    List Byte → Option (SseDecodiert × List Byte)
  | [] => none
  | m :: tl =>
    if byteNat m / 64 == 3 then
      match decodeSseReg 0 rBit bBit opByte (m :: tl) with
      | some (o, r) => some ((⟨o, 4⟩ : SseDecodiert), r)
      | none => none
    else
      let extra := if byteNat m % 8 == 4 then 1 else 0
      match decodeSseMem 0 rBit bBit opByte (m :: tl) with
      | some (o, r) => some ((⟨o, 8 + extra⟩ : SseDecodiert), r)
      | none => none

/-- Decode after the legacy prefix: the opcode byte, then ModRM.
    Lengths: register rows 4 (no prefix) or 5 (`66`/`F3`); memory
    rows 8 or 9 (`66`/`F3`/`F2`), plus one SIB byte. -/
def decodeSsePref (rBit bBit pref : Nat) :
    List Byte → Option (SseDecodiert × List Byte)
  | [] => none
  | op :: rest3 =>
    match pref, byteNat op with
    | 0, 18 => decodeSseTeils rBit bBit 18 rest3
    | 0, 22 => decodeSseTeils rBit bBit 22 rest3
    | p, 20 =>
      match decodeSseReg p rBit bBit 20 rest3 with
      | some (o, r) => some ((⟨o, if p == 0 then 4 else 5⟩ : SseDecodiert), r)
      | none => none
    | p, 21 =>
      match decodeSseReg p rBit bBit 21 rest3 with
      | some (o, r) => some ((⟨o, if p == 0 then 4 else 5⟩ : SseDecodiert), r)
      | none => none
    | p, 110 =>
      match decodeSseReg p rBit bBit 110 rest3 with
      | some (o, r) => some ((⟨o, 5⟩ : SseDecodiert), r)
      | none => none
    | p, 126 =>
      match decodeSseReg p rBit bBit 126 rest3 with
      | some (o, r) => some ((⟨o, 5⟩ : SseDecodiert), r)
      | none => none
    | p, 214 =>
      match decodeSseReg p rBit bBit 214 rest3 with
      | some (o, r) => some ((⟨o, 5⟩ : SseDecodiert), r)
      | none => none
    | p, s =>
      match rest3 with
      | [] => none
      | m :: _ =>
        let extra :=
          if byteNat m / 64 == 2 && byteNat m % 8 == 4 then 1 else 0
        match decodeSseMem p rBit bBit s rest3 with
        | some (o, r) =>
          some ((⟨o, (if p == 0 then 8 else 9) + extra⟩ : SseDecodiert), r)
        | none => none

/-- After a legacy prefix: consume the `0F` escape, then dispatch
    on the opcode byte. -/
def decodeSseNachPref (rBit bBit pref : Nat) :
    List Byte → Option (SseDecodiert × List Byte)
  | [] => none
  | p2 :: rest2 =>
    if byteNat p2 == 15 then decodeSsePref rBit bBit pref rest2
    else none

/-- Decode after the canonical REX prefix: the optional legacy
    prefix, then the `0F` escape, then the opcode byte, then ModRM.
    Lengths: register rows 4 (no prefix) or 5 (`66`/`F3`);
    memory rows 8 or 9 (`66`/`F3`/`F2`), plus one SIB byte. -/
def decodeSseNach (rBit bBit : Nat) :
    List Byte → Option (SseDecodiert × List Byte)
  | [] => none
  | p1 :: rest =>
    if byteNat p1 == 102 then decodeSseNachPref rBit bBit 1 rest
    else if byteNat p1 == 243 then decodeSseNachPref rBit bBit 2 rest
    else if byteNat p1 == 242 then decodeSseNachPref rBit bBit 3 rest
    else if byteNat p1 == 15 then decodeSsePref rBit bBit 0 rest
    else none

/-- Top-level move decode: the REX prefix selects the extension
    bits; anything without a canonical REX refuses. -/
def decodeSse : List Byte → Option (SseDecodiert × List Byte)
  | [] => none
  | r :: tail =>
    match sseRexBits (byteNat r) with
    | some (rh, bh) => decodeSseNach rh bh tail
    | none => none

/-! ## 3. Round trip: decoding inverts encoding on every covered row.

  Register rows by `cases` + `simp` over the decoder equations;
  memory rows (both SIB shapes) additionally by the accepted
  `parseLe32_leBytes32` equation, exactly like the accepted
  `roundtrip_movdqaLd`. -/

set_option maxHeartbeats 4000000

/-- Round trip for MOVLHPS. -/
theorem roundtrip_movlhps (dst src : XmmReg) (suffix : List Byte) :
    decodeSse (encodeSse (.movlhpsRR dst src) ++ suffix) =
      some ((⟨.movlhpsRR dst src, 4⟩ : SseDecodiert), suffix) := by
  cases dst <;> cases src <;>
    simp [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref, decodeSsePref,
      decodeSseTeils, decodeSseReg, sseRex, sseRexBits, sseSecond,
      codeXmm, xmmCode, xmmHigh, xmmLow, modrmReg, natByte, byteNat]

/-- Round trip for MOVHLPS. -/
theorem roundtrip_movhlps (dst src : XmmReg) (suffix : List Byte) :
    decodeSse (encodeSse (.movhlpsRR dst src) ++ suffix) =
      some ((⟨.movhlpsRR dst src, 4⟩ : SseDecodiert), suffix) := by
  cases dst <;> cases src <;>
    simp [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref, decodeSsePref,
      decodeSseTeils, decodeSseReg, sseRex, sseRexBits, sseSecond,
      codeXmm, xmmCode, xmmHigh, xmmLow, modrmReg, natByte, byteNat]

/-- Round trip for UNPCKLPS. -/
theorem roundtrip_unpcklps (dst src : XmmReg) (suffix : List Byte) :
    decodeSse (encodeSse (.unpcklpsRR dst src) ++ suffix) =
      some ((⟨.unpcklpsRR dst src, 4⟩ : SseDecodiert), suffix) := by
  cases dst <;> cases src <;>
    simp [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref, decodeSsePref,
      decodeSseTeils, decodeSseReg, sseRex, sseRexBits, sseSecond,
      codeXmm, xmmCode, xmmHigh, xmmLow, modrmReg, natByte, byteNat]

/-- Round trip for UNPCKHPS. -/
theorem roundtrip_unpckhps (dst src : XmmReg) (suffix : List Byte) :
    decodeSse (encodeSse (.unpckhpsRR dst src) ++ suffix) =
      some ((⟨.unpckhpsRR dst src, 4⟩ : SseDecodiert), suffix) := by
  cases dst <;> cases src <;>
    simp [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref, decodeSsePref,
      decodeSseTeils, decodeSseReg, sseRex, sseRexBits, sseSecond,
      codeXmm, xmmCode, xmmHigh, xmmLow, modrmReg, natByte, byteNat]

/-- Round trip for UNPCKLPD. -/
theorem roundtrip_unpcklpd (dst src : XmmReg) (suffix : List Byte) :
    decodeSse (encodeSse (.unpcklpdRR dst src) ++ suffix) =
      some ((⟨.unpcklpdRR dst src, 5⟩ : SseDecodiert), suffix) := by
  cases dst <;> cases src <;>
    simp [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref, decodeSsePref,
      decodeSseTeils, decodeSseReg, sseRex, sseRexBits, sseSecond,
      codeXmm, xmmCode, xmmHigh, xmmLow, modrmReg, natByte, byteNat]

/-- Round trip for UNPCKHPD. -/
theorem roundtrip_unpckhpd (dst src : XmmReg) (suffix : List Byte) :
    decodeSse (encodeSse (.unpckhpdRR dst src) ++ suffix) =
      some ((⟨.unpckhpdRR dst src, 5⟩ : SseDecodiert), suffix) := by
  cases dst <;> cases src <;>
    simp [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref, decodeSsePref,
      decodeSseTeils, decodeSseReg, sseRex, sseRexBits, sseSecond,
      codeXmm, xmmCode, xmmHigh, xmmLow, modrmReg, natByte, byteNat]

/-- Round trip for MOVD load (XMM destination, GPR source). -/
theorem roundtrip_movdLd (dst : XmmReg) (src : Register)
    (suffix : List Byte) :
    decodeSse (encodeSse (.movdLdRR dst src) ++ suffix) =
      some ((⟨.movdLdRR dst src, 5⟩ : SseDecodiert), suffix) := by
  cases dst <;> cases src <;>
    simp [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref, decodeSsePref,
      decodeSseTeils, decodeSseReg, sseRex, sseRexBits, sseSecond,
      codeXmm, codeReg, xmmCode, xmmHigh, xmmLow,
      regCode, regHigh, regLow, modrmReg, natByte, byteNat]

/-- Round trip for MOVD store (GPR destination, XMM source). -/
theorem roundtrip_movdSt (dst : Register) (src : XmmReg)
    (suffix : List Byte) :
    decodeSse (encodeSse (.movdStRR dst src) ++ suffix) =
      some ((⟨.movdStRR dst src, 5⟩ : SseDecodiert), suffix) := by
  cases dst <;> cases src <;>
    simp [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref, decodeSsePref,
      decodeSseTeils, decodeSseReg, sseRex, sseRexBits, sseSecond,
      codeXmm, codeReg, xmmCode, xmmHigh, xmmLow,
      regCode, regHigh, regLow, modrmReg, natByte, byteNat]

/-- Round trip for MOVQ load (low quadword, high bits zeroed). -/
theorem roundtrip_movqLd (dst src : XmmReg) (suffix : List Byte) :
    decodeSse (encodeSse (.movqLdRR dst src) ++ suffix) =
      some ((⟨.movqLdRR dst src, 5⟩ : SseDecodiert), suffix) := by
  cases dst <;> cases src <;>
    simp [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref, decodeSsePref,
      decodeSseTeils, decodeSseReg, sseRex, sseRexBits, sseSecond,
      codeXmm, xmmCode, xmmHigh, xmmLow, modrmReg, natByte, byteNat]

/-- Round trip for MOVQ store (low quadword). -/
theorem roundtrip_movqSt (dst src : XmmReg) (suffix : List Byte) :
    decodeSse (encodeSse (.movqStRR dst src) ++ suffix) =
      some ((⟨.movqStRR dst src, 5⟩ : SseDecodiert), suffix) := by
  cases dst <;> cases src <;>
    simp [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref, decodeSsePref,
      decodeSseTeils, decodeSseReg, sseRex, sseRexBits, sseSecond,
      codeXmm, xmmCode, xmmHigh, xmmLow, modrmReg, natByte, byteNat]

end Gabbro.Grammatik.X86
