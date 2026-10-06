/-
  File:      Grammatik/X86/SseMoves.lean
  Subject:   SSE/SSE2 moves, loads, stores and unpack connected to the
             coherent machine.

  Lane 1355: covers the ledger-1341 `fehlt` rows 0F 10/11/28/29
  (MOVUPS/MOVUPD/MOVAPS/MOVAPD), the MOVSD store (its load already
  decodes; the MOVSS store already decodes via the accepted `s32`
  row and stays there), MOVLPS/MOVHPS/MOVLHPS/MOVHLPS (0F 12/13/16/17), UNPCKL/UNPCKH
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
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder
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

/-- Round trip for the MOVUPS load, both SIB shapes. -/
theorem roundtrip_movupsLd (dst : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movupsLd dst base d) ++ suffix) =
      some ((⟨.movupsLd dst base d,
        (encodeSse (.movupsLd dst base d)).length⟩ : SseDecodiert),
        suffix) := by
  cases dst <;> cases base <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-- Round trip for the MOVUPS store, both SIB shapes. -/
theorem roundtrip_movupsSt (base : Register) (src : XmmReg)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movupsSt base src d) ++ suffix) =
      some ((⟨.movupsSt base src d,
        (encodeSse (.movupsSt base src d)).length⟩ : SseDecodiert),
        suffix) := by
  cases base <;> cases src <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-- Round trip for the MOVUPD load, both SIB shapes. -/
theorem roundtrip_movupdLd (dst : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movupdLd dst base d) ++ suffix) =
      some ((⟨.movupdLd dst base d,
        (encodeSse (.movupdLd dst base d)).length⟩ : SseDecodiert),
        suffix) := by
  cases dst <;> cases base <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-- Round trip for the MOVUPD store, both SIB shapes. -/
theorem roundtrip_movupdSt (base : Register) (src : XmmReg)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movupdSt base src d) ++ suffix) =
      some ((⟨.movupdSt base src d,
        (encodeSse (.movupdSt base src d)).length⟩ : SseDecodiert),
        suffix) := by
  cases base <;> cases src <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-- Round trip for the MOVAPS load, both SIB shapes. -/
theorem roundtrip_movapsLd (dst : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movapsLd dst base d) ++ suffix) =
      some ((⟨.movapsLd dst base d,
        (encodeSse (.movapsLd dst base d)).length⟩ : SseDecodiert),
        suffix) := by
  cases dst <;> cases base <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-- Round trip for the MOVAPS store, both SIB shapes. -/
theorem roundtrip_movapsSt (base : Register) (src : XmmReg)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movapsSt base src d) ++ suffix) =
      some ((⟨.movapsSt base src d,
        (encodeSse (.movapsSt base src d)).length⟩ : SseDecodiert),
        suffix) := by
  cases base <;> cases src <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-- Round trip for the MOVAPD load, both SIB shapes. -/
theorem roundtrip_movapdLd (dst : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movapdLd dst base d) ++ suffix) =
      some ((⟨.movapdLd dst base d,
        (encodeSse (.movapdLd dst base d)).length⟩ : SseDecodiert),
        suffix) := by
  cases dst <;> cases base <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-- Round trip for the MOVAPD store, both SIB shapes. -/
theorem roundtrip_movapdSt (base : Register) (src : XmmReg)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movapdSt base src d) ++ suffix) =
      some ((⟨.movapdSt base src d,
        (encodeSse (.movapdSt base src d)).length⟩ : SseDecodiert),
        suffix) := by
  cases base <;> cases src <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-- Round trip for the MOVSD store, both SIB shapes. -/
theorem roundtrip_movsdSt (base : Register) (src : XmmReg)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movsdSt base src d) ++ suffix) =
      some ((⟨.movsdSt base src d,
        (encodeSse (.movsdSt base src d)).length⟩ : SseDecodiert),
        suffix) := by
  cases base <;> cases src <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-- Round trip for the MOVLPS load, both SIB shapes. -/
theorem roundtrip_movlpsLd (dst : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movlpsLd dst base d) ++ suffix) =
      some ((⟨.movlpsLd dst base d,
        (encodeSse (.movlpsLd dst base d)).length⟩ : SseDecodiert),
        suffix) := by
  cases dst <;> cases base <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-- Round trip for the MOVLPS store, both SIB shapes. -/
theorem roundtrip_movlpsSt (base : Register) (src : XmmReg)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movlpsSt base src d) ++ suffix) =
      some ((⟨.movlpsSt base src d,
        (encodeSse (.movlpsSt base src d)).length⟩ : SseDecodiert),
        suffix) := by
  cases base <;> cases src <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-- Round trip for the MOVHPS load, both SIB shapes. -/
theorem roundtrip_movhpsLd (dst : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movhpsLd dst base d) ++ suffix) =
      some ((⟨.movhpsLd dst base d,
        (encodeSse (.movhpsLd dst base d)).length⟩ : SseDecodiert),
        suffix) := by
  cases dst <;> cases base <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-- Round trip for the MOVHPS store, both SIB shapes. -/
theorem roundtrip_movhpsSt (base : Register) (src : XmmReg)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movhpsSt base src d) ++ suffix) =
      some ((⟨.movhpsSt base src d,
        (encodeSse (.movhpsSt base src d)).length⟩ : SseDecodiert),
        suffix) := by
  cases base <;> cases src <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-- Round trip for the MOVNTPS store, both SIB shapes. -/
theorem roundtrip_movntpsSt (base : Register) (src : XmmReg)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movntpsSt base src d) ++ suffix) =
      some ((⟨.movntpsSt base src d,
        (encodeSse (.movntpsSt base src d)).length⟩ : SseDecodiert),
        suffix) := by
  cases base <;> cases src <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-- Round trip for the MOVNTPD store, both SIB shapes. -/
theorem roundtrip_movntpdSt (base : Register) (src : XmmReg)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movntpdSt base src d) ++ suffix) =
      some ((⟨.movntpdSt base src d,
        (encodeSse (.movntpdSt base src d)).length⟩ : SseDecodiert),
        suffix) := by
  cases base <;> cases src <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-- Round trip for the MOVNTDQ store, both SIB shapes. -/
theorem roundtrip_movntdqSt (base : Register) (src : XmmReg)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movntdqSt base src d) ++ suffix) =
      some ((⟨.movntdqSt base src d,
        (encodeSse (.movntdqSt base src d)).length⟩ : SseDecodiert),
        suffix) := by
  cases base <;> cases src <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-- Round trip for the MOVNTI store, both SIB shapes. -/
theorem roundtrip_movntiSt (base src : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeSse (encodeSse (.movntiSt base src d) ++ suffix) =
      some ((⟨.movntiSt base src d,
        (encodeSse (.movntiSt base src d)).length⟩ : SseDecodiert),
        suffix) := by
  cases base <;> cases src <;>
    simp_all [encodeSse, decodeSse, decodeSseNach, decodeSseNachPref,
      decodeSsePref, decodeSseTeils, decodeSseMem, decodeSseMemNach,
      decodeSseReg, sseRex, sseRexBits, ssePrefix, sseSecond, codeXmm,
      codeReg, xmmCode, xmmHigh, xmmLow, regCode, regHigh, regLow,
      modrmMem, modrmReg, parseLe32_leBytes32, length_leBytes32,
      natByte, byteNat]

/-! ## 4. Capstone agreement: the accepted chain first, moves where
    it refuses.

  `kapDecodeSse` is a NEW definition over the accepted `kapDecode`
  (never edited here): the old chain decides every byte string it
  accepts, the move decoder only where it refuses. The ledger-1341
  `fehlt` rows are exactly the new arm; a maintainer extends the
  accepted `kapDecode` chain with the `decodeSse` arm in the same
  position (after every existing arm). -/

/-- Extended chain: the accepted capstone chain first, the move
    decoder only where the whole accepted chain refuses. -/
def kapDecodeSse : List Byte →
    Option ((KapDekodiert ⊕ SseDecodiert) × List Byte) :=
  fun bs =>
    match kapDecode bs with
    | some (k, rest) => some (.inl k, rest)
    | none =>
      match decodeSse bs with
      | some (n, rest) => some (.inr n, rest)
      | none => none

/-- The extended chain agrees with the accepted chain on every byte
    string the accepted chain decodes: nothing is shadowed. -/
theorem kapDecodeSse_kanonisch (bs : List Byte) (k : KapDekodiert)
    (rest : List Byte) (h : kapDecode bs = some (k, rest)) :
    kapDecodeSse bs = some (.inl k, rest) := by
  unfold kapDecodeSse
  rw [h]

/-- Where the accepted chain refuses, a covered move row is taken. -/
theorem kapDecodeSse_erweitert (bs : List Byte) (n : SseDecodiert)
    (rest : List Byte) (h1 : kapDecode bs = none)
    (h2 : decodeSse bs = some (n, rest)) :
    kapDecodeSse bs = some (.inr n, rest) := by
  unfold kapDecodeSse
  rw [h1, h2]

/-- Where both refuse, the extended chain refuses. -/
theorem kapDecodeSse_nichts (bs : List Byte)
    (h1 : kapDecode bs = none) (h2 : decodeSse bs = none) :
    kapDecodeSse bs = none := by
  unfold kapDecodeSse
  rw [h1, h2]

/-- The accepted chain refuses the MOVUPS load (ledger 1341 `fehlt`). -/
theorem kap_weist_movupsLd_zurueck :
    kapDecode (encodeSse (.movupsLd .xmm0 .rax (BitVec.ofNat 32 0))) =
      none := by
  decide

/-- The accepted chain refuses the MOVAPS store (SIB shape). -/
theorem kap_weist_movapsSt_zurueck :
    kapDecode (encodeSse (.movapsSt .rsp .xmm1 (BitVec.ofNat 32 16))) =
      none := by
  decide

/-- The accepted chain refuses the MOVUPD load. -/
theorem kap_weist_movupdLd_zurueck :
    kapDecode (encodeSse (.movupdLd .xmm2 .rbx (BitVec.ofNat 32 0))) =
      none := by
  decide

/-- OVERLAP: the accepted `s32` chain takes `F3 0F 11` mod=2 as
    the MOVSS store, so the extended chain keeps the accepted arm.
    The accepted `movssSpeichere` row (with fetched execution) owns
    this shape; this lane covers no MOVSS store row. -/
theorem pin_kap_movssSt_s32 :
    kapDecode [natByte 64, natByte 243, natByte 15, natByte 17,
      natByte 153, natByte 0, natByte 0, natByte 0, natByte 0] =
      some (.s32 ⟨.movssSpeichere .rcx .xmm3 (BitVec.ofNat 32 0), 9⟩,
        []) := by
  decide

/-- Overlap through the extended chain: the `F3 0F 11` store keeps
    the accepted `s32` arm. -/
theorem pin_kapSse_movssSt_s32 :
    kapDecodeSse [natByte 64, natByte 243, natByte 15, natByte 17,
      natByte 153, natByte 0, natByte 0, natByte 0, natByte 0] =
      some (.inl (.s32 ⟨.movssSpeichere .rcx .xmm3
        (BitVec.ofNat 32 0), 9⟩), []) :=
  kapDecodeSse_kanonisch _ _ _ pin_kap_movssSt_s32

/-- The accepted chain refuses the MOVSD store. -/
theorem kap_weist_movsdSt_zurueck :
    kapDecode (encodeSse (.movsdSt .rdx .xmm4 (BitVec.ofNat 32 0))) =
      none := by
  decide

/-- The accepted chain refuses MOVLHPS. -/
theorem kap_weist_movlhps_zurueck :
    kapDecode (encodeSse (.movlhpsRR .xmm0 .xmm1)) = none := by
  decide

/-- The accepted chain refuses UNPCKLPD. -/
theorem kap_weist_unpcklpd_zurueck :
    kapDecode (encodeSse (.unpcklpdRR .xmm5 .xmm6)) = none := by
  decide

/-- The accepted chain refuses MOVNTI. -/
theorem kap_weist_movnti_zurueck :
    kapDecode (encodeSse (.movntiSt .rsi .rdi (BitVec.ofNat 32 0))) =
      none := by
  decide

/-- The accepted chain refuses the MOVD load. -/
theorem kap_weist_movdLd_zurueck :
    kapDecode (encodeSse (.movdLdRR .xmm7 .rax)) = none := by
  decide

/-- The accepted chain refuses the MOVNTDQ store. -/
theorem kap_weist_movntdq_zurueck :
    kapDecode (encodeSse (.movntdqSt .rbp .xmm8 (BitVec.ofNat 32 0))) =
      none := by
  decide

/-- New row through the extended chain: MOVUPS load. -/
theorem pin_kapSse_movupsLd :
    kapDecodeSse (encodeSse (.movupsLd .xmm0 .rax (BitVec.ofNat 32 0))) =
      some (.inr ⟨.movupsLd .xmm0 .rax (BitVec.ofNat 32 0),
        (encodeSse (.movupsLd .xmm0 .rax
          (BitVec.ofNat 32 0))).length⟩, []) :=
  kapDecodeSse_erweitert _ _ _ kap_weist_movupsLd_zurueck
    (roundtrip_movupsLd .xmm0 .rax (BitVec.ofNat 32 0) [])

/-- A bare `0F` escape without the canonical REX refuses. -/
theorem sse_nichts_bare0F :
    decodeSse [natByte 15, natByte 16, natByte 131, natByte 0, natByte 0,
      natByte 0, natByte 0] = none := rfl

/-- A REX.W first byte refuses (canonical W=0 only). -/
theorem sse_nichts_rexW :
    decodeSse [natByte 72, natByte 15, natByte 16, natByte 192] = none := rfl

/-- A truncated prefix (REX + `66` only) refuses. -/
theorem sse_nichts_kurz :
    decodeSse [natByte 64, natByte 102] = none := rfl

/-- mod=1 after a covered opcode refuses (only mod=2 mem / mod=3 reg). -/
theorem sse_nichts_mod1 :
    decodeSse [natByte 64, natByte 15, natByte 16, natByte 64] = none := rfl

/-- `66 0F 12` mod=3 refuses (no 66 shuffle row exists). -/
theorem sse_nichts_66_12reg :
    decodeSse [natByte 64, natByte 102, natByte 15, natByte 18,
      natByte 195] = none := rfl

/-- `0F 14` mod=2 refuses (no UNPCKLPS memory row exists). -/
theorem sse_nichts_14mem :
    decodeSse [natByte 64, natByte 15, natByte 20, natByte 131,
      natByte 0, natByte 0, natByte 0, natByte 0] = none := rfl

/-! ## 5. Register semantics on the shared XMM state.

  The ten register rows step on the SAME `FpZustand` the scalar FP
  steps use (`xmmSet` writes the whole 128-bit register, `ripNach`
  advances RIP, `mergeRegNarrow .b32` zero-extends the MOVD store
  exactly like the accepted narrow merge). Lane interleaves reuse
  the accepted `laneNat`/`vecMk` vocabulary; memory rows, the
  non-temporal stores and MOVNTI admit no register successor. -/

/-- GPR file update. -/
def sseRegSet (r : Register → Wort) (dst : Register) (v : Wort) :
    Register → Wort :=
  fun q => if q = dst then v else r q

/-- The updated GPR answers `v` at `dst`. -/
theorem sseRegSet_gleich (r : Register → Wort) (dst : Register)
    (v : Wort) : sseRegSet r dst v dst = v := by
  simp [sseRegSet]

/-- Every other GPR keeps its value. -/
theorem sseRegSet_fremd (r : Register → Wort) (dst q : Register)
    (v : Wort) (h : q ≠ dst) : sseRegSet r dst v q = r q := by
  unfold sseRegSet
  rw [if_neg h]

/-- UNPCKLPS interleave: low 32-bit lanes `[a0, b0, a1, b1]`
    (SDM Vol. 2B: `DEST[31:0] ← SRC1[31:0]`, `DEST[63:32] ←
    SRC2[31:0]`, `DEST[95:64] ← SRC1[63:32]`, `DEST[127:96] ←
    SRC2[63:32]`). -/
def sseUnpckLo32 (a b : Vektor) : Vektor :=
  vecMk .b32 (fun i => match i with
    | 0 => laneNat .b32 a 0
    | 1 => laneNat .b32 b 0
    | 2 => laneNat .b32 a 1
    | _ => laneNat .b32 b 1)

/-- UNPCKHPS interleave: high 32-bit lanes `[a2, b2, a3, b3]`. -/
def sseUnpckHi32 (a b : Vektor) : Vektor :=
  vecMk .b32 (fun i => match i with
    | 0 => laneNat .b32 a 2
    | 1 => laneNat .b32 b 2
    | 2 => laneNat .b32 a 3
    | _ => laneNat .b32 b 3)

/-- UNPCKLPS lane 0 is the destination low lane. -/
theorem sseUnpckLo32_lane0 (a b : Vektor) :
    laneNat .b32 (sseUnpckLo32 a b) 0 = laneNat .b32 a 0 := by
  unfold sseUnpckLo32
  rw [laneGet_mk _ _ _ (by decide)]
  exact Nat.mod_eq_of_lt (laneNat_lt _ _ _)

/-- UNPCKLPS lane 1 is the source low lane. -/
theorem sseUnpckLo32_lane1 (a b : Vektor) :
    laneNat .b32 (sseUnpckLo32 a b) 1 = laneNat .b32 b 0 := by
  unfold sseUnpckLo32
  rw [laneGet_mk _ _ _ (by decide)]
  exact Nat.mod_eq_of_lt (laneNat_lt _ _ _)

/-- UNPCKLPS lane 2 is the destination second lane. -/
theorem sseUnpckLo32_lane2 (a b : Vektor) :
    laneNat .b32 (sseUnpckLo32 a b) 2 = laneNat .b32 a 1 := by
  unfold sseUnpckLo32
  rw [laneGet_mk _ _ _ (by decide)]
  exact Nat.mod_eq_of_lt (laneNat_lt _ _ _)

/-- UNPCKLPS lane 3 is the source second lane. -/
theorem sseUnpckLo32_lane3 (a b : Vektor) :
    laneNat .b32 (sseUnpckLo32 a b) 3 = laneNat .b32 b 1 := by
  unfold sseUnpckLo32
  rw [laneGet_mk _ _ _ (by decide)]
  exact Nat.mod_eq_of_lt (laneNat_lt _ _ _)

/-- UNPCKHPS lane 0 is the destination third lane. -/
theorem sseUnpckHi32_lane0 (a b : Vektor) :
    laneNat .b32 (sseUnpckHi32 a b) 0 = laneNat .b32 a 2 := by
  unfold sseUnpckHi32
  rw [laneGet_mk _ _ _ (by decide)]
  exact Nat.mod_eq_of_lt (laneNat_lt _ _ _)

/-- UNPCKHPS lane 1 is the source third lane. -/
theorem sseUnpckHi32_lane1 (a b : Vektor) :
    laneNat .b32 (sseUnpckHi32 a b) 1 = laneNat .b32 b 2 := by
  unfold sseUnpckHi32
  rw [laneGet_mk _ _ _ (by decide)]
  exact Nat.mod_eq_of_lt (laneNat_lt _ _ _)

/-- UNPCKHPS lane 2 is the destination fourth lane. -/
theorem sseUnpckHi32_lane2 (a b : Vektor) :
    laneNat .b32 (sseUnpckHi32 a b) 2 = laneNat .b32 a 3 := by
  unfold sseUnpckHi32
  rw [laneGet_mk _ _ _ (by decide)]
  exact Nat.mod_eq_of_lt (laneNat_lt _ _ _)

/-- UNPCKHPS lane 3 is the source fourth lane. -/
theorem sseUnpckHi32_lane3 (a b : Vektor) :
    laneNat .b32 (sseUnpckHi32 a b) 3 = laneNat .b32 b 3 := by
  unfold sseUnpckHi32
  rw [laneGet_mk _ _ _ (by decide)]
  exact Nat.mod_eq_of_lt (laneNat_lt _ _ _)

/-- Length guard: canonical length and decode-length range. -/
def sseLaengeOk (d : SseDecodiert) : Bool :=
  d.laenge == (encodeSse d.op).length && laengeOk d.laenge

/-- One register step on the extended state: the ten register rows.
    Memory rows, the non-temporal stores and MOVNTI admit no
    register successor (catch-all `none`): their bytes move only
    through the TSO issue path (§3/§6 of `HardwareExecution`), never
    through a substituted word effect. RIP advances by the decode
    length, exactly like the accepted vector step. -/
def sseRegSchritt (d : SseDecodiert) (t : FpZustand) :
    Option FpZustand :=
  match d.op with
  | .movlhpsRR dst src =>
    some { t with xmm := xmmSet t.xmm dst (vecJoin (vLo (t.xmm dst)) (vLo (t.xmm src))), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } }
  | .movhlpsRR dst src =>
    some { t with xmm := xmmSet t.xmm dst (vecJoin (vHi (t.xmm src)) (vHi (t.xmm dst))), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } }
  | .unpcklpsRR dst src =>
    some { t with xmm := xmmSet t.xmm dst (sseUnpckLo32 (t.xmm dst) (t.xmm src)), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } }
  | .unpckhpsRR dst src =>
    some { t with xmm := xmmSet t.xmm dst (sseUnpckHi32 (t.xmm dst) (t.xmm src)), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } }
  | .unpcklpdRR dst src =>
    some { t with xmm := xmmSet t.xmm dst (vecJoin (vLo (t.xmm dst)) (vLo (t.xmm src))), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } }
  | .unpckhpdRR dst src =>
    some { t with xmm := xmmSet t.xmm dst (vecJoin (vHi (t.xmm dst)) (vHi (t.xmm src))), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } }
  | .movdLdRR dst src =>
    some { t with xmm := xmmSet t.xmm dst (BitVec.ofNat 128 ((t.kern.register src).toNat % 2 ^ 32)), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } }
  | .movdStRR dst src =>
    some { t with kern := { t.kern with register := sseRegSet t.kern.register dst (mergeRegNarrow .b32 (t.kern.register dst) (vLo (t.xmm src))), rip := ripNach t.kern.rip d.laenge } }
  | .movqLdRR dst src =>
    some { t with xmm := xmmSet t.xmm dst (vecJoin (vLo (t.xmm src)) (BitVec.ofNat 64 0)), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } }
  | .movqStRR dst src =>
    some { t with xmm := xmmSet t.xmm dst (vecJoin (vLo (t.xmm src)) (vHi (t.xmm dst))), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } }
  | _ => none

/-- Selection: MOVLHPS is the accepted low-to-high half move. -/
theorem sseRegSchritt_movlhps (d : SseDecodiert) (t : FpZustand)
    (dst src : XmmReg) (h : d.op = .movlhpsRR dst src) :
    sseRegSchritt d t = some { t with xmm := xmmSet t.xmm dst (vecJoin (vLo (t.xmm dst)) (vLo (t.xmm src))), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } } := by
  simp [sseRegSchritt, h]

/-- Selection: MOVHLPS is the accepted high-to-low half move. -/
theorem sseRegSchritt_movhlps (d : SseDecodiert) (t : FpZustand)
    (dst src : XmmReg) (h : d.op = .movhlpsRR dst src) :
    sseRegSchritt d t = some { t with xmm := xmmSet t.xmm dst (vecJoin (vHi (t.xmm src)) (vHi (t.xmm dst))), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } } := by
  simp [sseRegSchritt, h]

/-- Selection: UNPCKLPS is the accepted low interleave. -/
theorem sseRegSchritt_unpcklps (d : SseDecodiert) (t : FpZustand)
    (dst src : XmmReg) (h : d.op = .unpcklpsRR dst src) :
    sseRegSchritt d t = some { t with xmm := xmmSet t.xmm dst (sseUnpckLo32 (t.xmm dst) (t.xmm src)), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } } := by
  simp [sseRegSchritt, h]

/-- Selection: UNPCKHPS is the accepted high interleave. -/
theorem sseRegSchritt_unpckhps (d : SseDecodiert) (t : FpZustand)
    (dst src : XmmReg) (h : d.op = .unpckhpsRR dst src) :
    sseRegSchritt d t = some { t with xmm := xmmSet t.xmm dst (sseUnpckHi32 (t.xmm dst) (t.xmm src)), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } } := by
  simp [sseRegSchritt, h]

/-- Selection: UNPCKLPD is the accepted low quadword interleave. -/
theorem sseRegSchritt_unpcklpd (d : SseDecodiert) (t : FpZustand)
    (dst src : XmmReg) (h : d.op = .unpcklpdRR dst src) :
    sseRegSchritt d t = some { t with xmm := xmmSet t.xmm dst (vecJoin (vLo (t.xmm dst)) (vLo (t.xmm src))), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } } := by
  simp [sseRegSchritt, h]

/-- Selection: UNPCKHPD is the accepted high quadword interleave. -/
theorem sseRegSchritt_unpckhpd (d : SseDecodiert) (t : FpZustand)
    (dst src : XmmReg) (h : d.op = .unpckhpdRR dst src) :
    sseRegSchritt d t = some { t with xmm := xmmSet t.xmm dst (vecJoin (vHi (t.xmm dst)) (vHi (t.xmm src))), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } } := by
  cases d with
  | mk op len =>
    change op = .unpckhpdRR dst src at h
    subst h
    rfl

/-- Selection: MOVD load zero-extends the 32-bit GPR source. -/
theorem sseRegSchritt_movdLd (d : SseDecodiert) (t : FpZustand)
    (dst : XmmReg) (src : Register) (h : d.op = .movdLdRR dst src) :
    sseRegSchritt d t = some { t with xmm := xmmSet t.xmm dst (BitVec.ofNat 128 ((t.kern.register src).toNat % 2 ^ 32)), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } } := by
  simp [sseRegSchritt, h]

/-- Selection: MOVD store is the accepted 32-bit narrow merge. -/
theorem sseRegSchritt_movdSt (d : SseDecodiert) (t : FpZustand)
    (dst : Register) (src : XmmReg) (h : d.op = .movdStRR dst src) :
    sseRegSchritt d t = some { t with kern := { t.kern with register := sseRegSet t.kern.register dst (mergeRegNarrow .b32 (t.kern.register dst) (vLo (t.xmm src))), rip := ripNach t.kern.rip d.laenge } } := by
  simp [sseRegSchritt, h]

/-- Selection: MOVQ load zeroes the high quadword. -/
theorem sseRegSchritt_movqLd (d : SseDecodiert) (t : FpZustand)
    (dst src : XmmReg) (h : d.op = .movqLdRR dst src) :
    sseRegSchritt d t = some { t with xmm := xmmSet t.xmm dst (vecJoin (vLo (t.xmm src)) (BitVec.ofNat 64 0)), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } } := by
  simp [sseRegSchritt, h]

/-- Selection: MOVQ store keeps the destination high quadword. -/
theorem sseRegSchritt_movqSt (d : SseDecodiert) (t : FpZustand)
    (dst src : XmmReg) (h : d.op = .movqStRR dst src) :
    sseRegSchritt d t = some { t with xmm := xmmSet t.xmm dst (vecJoin (vLo (t.xmm src)) (vHi (t.xmm dst))), kern := { t.kern with rip := ripNach t.kern.rip d.laenge } } := by
  simp [sseRegSchritt, h]

/-- Memory discipline: a successful register step leaves canonical
    memory alone (only XMM, GPR and RIP move). Memory rows have no
    successor (`cases h` closes them); register rows substitute the
    successor and project (kernel definitional unfolding only). -/
theorem sseRegSchritt_speicher (d : SseDecodiert) (t t' : FpZustand)
    (h : sseRegSchritt d t = some t') :
    t'.kern.speicher = t.kern.speicher := by
  cases d with
  | mk op len =>
    cases op with
    | movupsLd _ _ _ => cases h
    | movupsSt _ _ _ => cases h
    | movupdLd _ _ _ => cases h
    | movupdSt _ _ _ => cases h
    | movapsLd _ _ _ => cases h
    | movapsSt _ _ _ => cases h
    | movapdLd _ _ _ => cases h
    | movapdSt _ _ _ => cases h
    | movsdSt _ _ _ => cases h
    | movlpsLd _ _ _ => cases h
    | movlpsSt _ _ _ => cases h
    | movhpsLd _ _ _ => cases h
    | movhpsSt _ _ _ => cases h
    | movntpsSt _ _ _ => cases h
    | movntpdSt _ _ _ => cases h
    | movntdqSt _ _ _ => cases h
    | movntiSt _ _ _ => cases h
    | movlhpsRR _ _ => cases h; rfl
    | movhlpsRR _ _ => cases h; rfl
    | unpcklpsRR _ _ => cases h; rfl
    | unpckhpsRR _ _ => cases h; rfl
    | unpcklpdRR _ _ => cases h; rfl
    | unpckhpdRR _ _ => cases h; rfl
    | movdLdRR _ _ => cases h; rfl
    | movdStRR _ _ => cases h; rfl
    | movqLdRR _ _ => cases h; rfl
    | movqStRR _ _ => cases h; rfl

/-- Memory-row predicate: the loads, the stores, the non-temporal
    stores and MOVNTI. The ten register rows are not memory rows. -/
def sseIstSpeicher : SseMoveOp → Bool
  | .movupsLd _ _ _ => true
  | .movupsSt _ _ _ => true
  | .movupdLd _ _ _ => true
  | .movupdSt _ _ _ => true
  | .movapsLd _ _ _ => true
  | .movapsSt _ _ _ => true
  | .movapdLd _ _ _ => true
  | .movapdSt _ _ _ => true
  | .movsdSt _ _ _ => true
  | .movlpsLd _ _ _ => true
  | .movlpsSt _ _ _ => true
  | .movhpsLd _ _ _ => true
  | .movhpsSt _ _ _ => true
  | .movntpsSt _ _ _ => true
  | .movntpdSt _ _ _ => true
  | .movntdqSt _ _ _ => true
  | .movntiSt _ _ _ => true
  | _ => false

/-- A memory row admits no register successor. -/
theorem sseRegSchritt_verweigert_speicher (d : SseDecodiert)
    (t : FpZustand) (h : sseIstSpeicher d.op = true) :
    sseRegSchritt d t = none := by
  cases e : d.op <;> simp_all [sseRegSchritt, sseIstSpeicher, e]

/-! ## 6. Machine adapter: the move family on the coherent machine.

  The producer plug instantiates `HwAdapter SseDecodiert`: the
  length guard first, then the accepted register step on the core
  projection, re-embedded on success. Traps and refusals admit no
  successor state (memory rows refuse by §5; a bad length refuses by
  the guard). -/

/-- The move plug: one checked move event step on the coherent
    machine. `none` = guard failure, trap or refusal, never a
    silent successor. -/
def adapterSseMoves : HwAdapter SseDecodiert :=
  ⟨fun m c d =>
    if sseLaengeOk d then
      match sseRegSchritt d (projFp m c) with
      | some t' => some (setKernVonFp m c t')
      | none => none
    else none⟩

/-- Every adapter step preserves well-formedness: only core data
    moves, profiles are untouched. -/
theorem adapterSseMoves_wf (m : HwMaschine) (c : Nat)
    (d : SseDecodiert) (m' : HwMaschine) (hwf : HwWf m)
    (h : adapterSseMoves.schritt m c d = some m') :
    HwWf m' := by
  unfold adapterSseMoves at h
  simp only at h
  by_cases hc : sseLaengeOk d = true
  · rw [if_pos hc] at h
    cases hs : sseRegSchritt d (projFp m c) with
    | some t' =>
      rw [hs] at h
      cases h
      unfold setKernVonFp
      exact setKernDaten_wf _ _ _ hwf
    | none =>
      rw [hs] at h
      cases h
  · rw [if_neg hc] at h
    cases h

/-- Agreement: the adapter succeeds exactly where the guard passes
    and the accepted register step succeeds, with the successor
    core data re-embedded. -/
theorem adapterSseMoves_ok (m : HwMaschine) (c : Nat)
    (d : SseDecodiert) (t' : FpZustand) (hl : sseLaengeOk d = true)
    (h : sseRegSchritt d (projFp m c) = some t') :
    adapterSseMoves.schritt m c d =
      some (setKernVonFp m c t') := by
  unfold adapterSseMoves
  simp only
  rw [if_pos hl, h]

/-- The successor core sees the accepted successor data over the
    shared memory. -/
theorem adapterSseMoves_proj (m : HwMaschine) (c : Nat)
    (d : SseDecodiert) (t' : FpZustand)
    (h : sseRegSchritt d (projFp m c) = some t') :
    ((setKernVonFp m c t').kerne c).register = t'.kern.register ∧
    ((setKernVonFp m c t').kerne c).xmm = t'.xmm ∧
    (setKernVonFp m c t').mem = m.mem ∧
    t'.kern.speicher = m.mem := by
  refine ⟨setKernVonFp_register m c t', ?_, setKernVonFp_speicher m c t', ?_⟩
  · unfold setKernVonFp setKernDaten
    simp
  · have hmem := sseRegSchritt_speicher d (projFp m c) t' h
    have hproj : (projFp m c).kern.speicher = m.mem := projFp_speicher m c
    rw [hproj] at hmem
    exact hmem

/-- A failed length guard admits no adapter step. -/
theorem adapterSseMoves_verweigert_bei_laenge (m : HwMaschine)
    (c : Nat) (d : SseDecodiert)
    (h : sseLaengeOk d = false) :
    adapterSseMoves.schritt m c d = none := by
  have hc : ¬ sseLaengeOk d = true := by
    rw [h]
    decide
  unfold adapterSseMoves
  simp only
  rw [if_neg hc]

/-- A memory row admits no adapter successor: memory moves only
    through the TSO issue path, never through a substituted word
    effect. -/
theorem adapterSseMoves_verweigert_speicher (m : HwMaschine)
    (c : Nat) (d : SseDecodiert)
    (h : sseIstSpeicher d.op = true) :
    adapterSseMoves.schritt m c d = none := by
  unfold adapterSseMoves
  simp only
  by_cases hc : sseLaengeOk d = true
  · rw [if_pos hc, sseRegSchritt_verweigert_speicher d _ h]
  · rw [if_neg hc]

end Gabbro.Grammatik.X86
