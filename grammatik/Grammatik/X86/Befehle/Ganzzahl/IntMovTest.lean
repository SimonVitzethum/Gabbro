/-
  File:      Grammatik/X86/IntMovTest.lean
  Subject:   MOV, TEST, bare LEA, multi-byte NOP, ENDBR64, PUSH/POP,
             LEAVE, RET-imm, INT3 and UD2 over the coherent machine.

  Lane 1351: decoder + encoder (round trip) and a HwAdapter plug reusing
  the accepted evaluators unchanged (NarrowOps, ShiftLogic, AddressEncoding,
  HwAddressed, HwStackCalls, Ausfuehrung). Rows owned by accepted decoders
  (REX.W TEST-reg by decodeCore/decodeIntHw, 90+r/86/87 by decodeSx, REX.W
  B8-imm64 by the pilot) are refused here, never redefined. No silicon
  correspondence beyond self-consistency (see CUTS).
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Kern.Codec
import Grammatik.X86.Kern.Wort
import Grammatik.X86.Kern.Ausfuehrung
import Grammatik.X86.Speicher.Speicher
import Grammatik.X86.Speicher.AddressEncoding
import Grammatik.X86.Befehle.Arithmetik.ShiftLogic
import Grammatik.X86.Befehle.Arithmetik.NarrowOps
import Grammatik.X86.Befehle.Ganzzahl.IntegerCore
import Grammatik.X86.Befehle.Ganzzahl.IntSignXchg
import Grammatik.X86.TSO.Kern.TSO
import Grammatik.X86.TSO.Verriegelt.XchgOrderNeed
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Familien.HwAddressed
import Grammatik.X86.Hw.Familien.HwStackCalls
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder

namespace Gabbro.Grammatik.X86

/-- Family vocabulary: MOV (modrm, imm8, B8-imm, C6/C7), TEST (modrm,
    accumulator-imm, F6/F7-group), bare LEA, NOP (memory and register
    multi-byte forms), ENDBR64, PUSH/POP (register and memory), LEAVE,
    RET with imm16 pop count, INT3 and UD2. XCHG rows stay with the
    accepted decodeSx and are refused here. -/
inductive MtForm where
  | movRR (b : Breite) (dst src : Register)
  | movRM (b : Breite) (f : AdrForm) (src : Register)
  | movMR (b : Breite) (dst : Register) (f : AdrForm)
  | movRI8 (r : Register) (v : Byte)
  | movRIB16 (r : Register) (v : BitVec 16)
  | movRImm8 (r : Register) (v : Byte)
  | movRImm16 (r : Register) (v : BitVec 16)
  | movRImm32 (r : Register) (v : BitVec 32)
  | movMImm8 (f : AdrForm) (v : Byte)
  | movMImm16 (f : AdrForm) (v : BitVec 16)
  | movMImm32 (f : AdrForm) (v : BitVec 32)
  | movMImm64 (f : AdrForm) (v : BitVec 32)
  | testRR (b : Breite) (lhs rhs : Register)
  | testRM (b : Breite) (f : AdrForm) (rhs : Register)
  | testAI8 (r : Register) (v : Byte)
  | testAI16 (r : Register) (v : BitVec 16)
  | testAI32 (r : Register) (v : BitVec 32)
  | testAI64 (r : Register) (v : BitVec 32)
  | testRImm8 (r : Register) (v : Byte)
  | testRImm16 (r : Register) (v : BitVec 16)
  | testRImm32 (r : Register) (v : BitVec 32)
  | testRImm64 (r : Register) (v : BitVec 32)
  | testMImm8 (f : AdrForm) (v : Byte)
  | testMImm16 (f : AdrForm) (v : BitVec 16)
  | testMImm32 (f : AdrForm) (v : BitVec 32)
  | testMImm64 (f : AdrForm) (v : BitVec 32)
  | leaBare (dst : Register) (f : AdrForm)
  | nopMem (f : AdrForm)
  | nopReg (r : Register)
  | endbr64
  | pushR (b : Breite) (r : Register)
  | pushM (b : Breite) (f : AdrForm)
  | popR (b : Breite) (r : Register)
  | popM (b : Breite) (f : AdrForm)
  | leave
  | retImm (n : BitVec 16)
  | int3
  | ud2
  deriving DecidableEq, Repr

/-- A decoded family instruction with its consumed length. -/
structure MtDecodiert where
  befehl : MtForm
  laenge : Nat
  deriving DecidableEq, Repr

/-- Canonical prefix parse: optional 66H then optional REX (0x40-0x4F).
    Returns operand-size-16 flag, REX R/X/B/W bits and the prefix length.
    A 66H alone at end of input still parses; the opcode match fails later. -/
def mtPraefix : List Byte → Option (Bool × Nat × Nat × Nat × Bool × Nat)
  | b0 :: b1 :: _rest =>
    if byteNat b0 == 102 then
      if 64 ≤ byteNat b1 ∧ byteNat b1 < 80 then
        let rv := byteNat b1 - 64
        some (true, rv / 4 % 2, rv / 2 % 2, rv % 2, 72 ≤ byteNat b1, 2)
      else some (true, 0, 0, 0, false, 1)
    else if 64 ≤ byteNat b0 ∧ byteNat b0 < 80 then
      let rv := byteNat b0 - 64
      some (false, rv / 4 % 2, rv / 2 % 2, rv % 2, 72 ≤ byteNat b0, 1)
    else some (false, 0, 0, 0, false, 0)
  | [b0] =>
    if byteNat b0 == 102 then some (true, 0, 0, 0, false, 1)
    else if 64 ≤ byteNat b0 ∧ byteNat b0 < 80 then
      let rv := byteNat b0 - 64
      some (false, rv / 4 % 2, rv / 2 % 2, rv % 2, 72 ≤ byteNat b0, 1)
    else some (false, 0, 0, 0, false, 0)
  | [] => none

/-- Operand width of a word form: REX.W wins over 66H, else 32 bits.
    This is the architectural promotion rule for 89/8B/A9/C7. -/
def mtWeiteMov (op16 w : Bool) : Breite :=
  if w then .b64 else if op16 then .b16 else .b32

/-- Byte-register admissibility: without REX, codes 4-7 name the high
    bytes AH/CH/DH/BH, which have no Register in this model, so only
    codes 0-3 decode. With REX every code names a low byte. -/
def mtByteRegOk (rex : Bool) (code : Nat) : Bool :=
  if rex then true else code < 4

/-- Split one ModRM byte into mod, reg and rm fields. -/
def mtSplitModrm (m : Byte) : Nat × Nat × Nat :=
  (byteNat m / 64, byteNat m / 8 % 8, byteNat m % 8)

/-- 16-bit little-endian immediate tail. -/
def mtParseLe16 : List Byte → Option (BitVec 16 × List Byte)
  | b0 :: b1 :: rest =>
    some (BitVec.ofNat 16 (b0.toNat + 256 * b1.toNat), rest)
  | _ => none

/-- 16-bit little-endian immediate encoding. -/
def mtLeBytes16 (v : BitVec 16) : List Byte :=
  [natByte (v.toNat % 256), natByte (v.toNat / 256)]

/-- MOV through one ModRM byte: 88/89 store, 8A/8B load. Register-direct
    (mod=3) moves between registers; otherwise the accepted
    parseAdrTail selects the memory form. `n` is the full input length,
    so the recorded length counts prefixes and the opcode. -/
def mtDecodeMovRM (isLoad isByte : Bool) (b : Breite)
    (rBit xBit bBit : Nat) (rex : Bool) (n : Nat) :
    List Byte → Option (MtDecodiert × List Byte)
  | m :: rest =>
    let (mod, rg, rm) := mtSplitModrm m
    if mod == 3 then
      match codeReg (rBit * 8 + rg), codeReg (bBit * 8 + rm) with
      | some rReg, some mReg =>
        if isByte &&
            (!mtByteRegOk rex (rBit * 8 + rg) ||
              !mtByteRegOk rex (bBit * 8 + rm)) then none
        else
          let form :=
            if isLoad then MtForm.movRR b rReg mReg
            else MtForm.movRR b mReg rReg
          some (⟨form, n - rest.length⟩, rest)
      | _, _ => none
    else
      match parseAdrTail rBit xBit bBit (m :: rest) with
      | none => none
      | some (regR, f, rest') =>
        if isByte && !mtByteRegOk rex (rBit * 8 + rg) then none
        else
          let form :=
            if isLoad then MtForm.movMR b regR f
            else MtForm.movRM b f regR
          some (⟨form, n - rest'.length⟩, rest')
  | [] => none

/-- TEST through one ModRM byte: 84 for bytes, 85 for words. Like MOV,
    AND-for-flags-only; the flag snapshot is fixed in the step, never
    in the decoder. Memory reads reuse the accepted parseAdrTail. -/
def mtDecodeTestRM (isByte : Bool) (b : Breite)
    (rBit xBit bBit : Nat) (rex : Bool) (n : Nat) :
    List Byte → Option (MtDecodiert × List Byte)
  | m :: rest =>
    let (mod, rg, rm) := mtSplitModrm m
    if mod == 3 then
      match codeReg (rBit * 8 + rg), codeReg (bBit * 8 + rm) with
      | some rReg, some mReg =>
        if isByte &&
            (!mtByteRegOk rex (rBit * 8 + rg) ||
              !mtByteRegOk rex (bBit * 8 + rm)) then none
        else some (⟨MtForm.testRR b rReg mReg, n - rest.length⟩, rest)
      | _, _ => none
    else
      match parseAdrTail rBit xBit bBit (m :: rest) with
      | none => none
      | some (regR, f, rest') =>
        if isByte && !mtByteRegOk rex (rBit * 8 + rg) then none
        else some (⟨MtForm.testRM b f regR, n - rest'.length⟩, rest')
  | [] => none

/-- Register-direct immediate tail after the ModRM byte: C6/C7 move,
    F6/F7 TEST, at the named width. -/
def mtDecodeImmReg (op : Nat) (b : Breite) (r : Register) (n : Nat) :
    List Byte → Option (MtDecodiert × List Byte)
  | tail =>
    match b with
    | .b8 =>
      match tail with
      | imm :: rest =>
        let form := if op == 198 then MtForm.movRImm8 r imm
          else MtForm.testRImm8 r imm
        some (⟨form, n - rest.length⟩, rest)
      | [] => none
    | .b16 =>
      match mtParseLe16 tail with
      | some (v, rest') =>
        let form := if op == 199 then MtForm.movRImm16 r v
          else MtForm.testRImm16 r v
        some (⟨form, n - rest'.length⟩, rest')
      | none => none
    | .b64 =>
      match parseLe32 tail with
      | some (v, rest') =>
        some (⟨MtForm.testRImm64 r v, n - rest'.length⟩, rest')
      | none => none
    | .b32 =>
      match parseLe32 tail with
      | some (v, rest') =>
        let form := if op == 199 then MtForm.movRImm32 r v
          else MtForm.testRImm32 r v
        some (⟨form, n - rest'.length⟩, rest')
      | none => none

/-- Memory immediate tail after the address form: C6/C7 move, F6/F7
    TEST, at the named width. -/
def mtDecodeImmMem (op : Nat) (b : Breite) (f : AdrForm) (n : Nat) :
    List Byte → Option (MtDecodiert × List Byte)
  | tail =>
    match b with
    | .b8 =>
      match tail with
      | imm :: rest =>
        let form := if op == 198 then MtForm.movMImm8 f imm
          else MtForm.testMImm8 f imm
        some (⟨form, n - rest.length⟩, rest)
      | [] => none
    | .b16 =>
      match mtParseLe16 tail with
      | some (v, rest') =>
        let form := if op == 199 then MtForm.movMImm16 f v
          else MtForm.testMImm16 f v
        some (⟨form, n - rest'.length⟩, rest')
      | none => none
    | .b64 =>
      match parseLe32 tail with
      | some (v, rest') =>
        let form := if op == 199 then MtForm.movMImm64 f v
          else MtForm.testMImm64 f v
        some (⟨form, n - rest'.length⟩, rest')
      | none => none
    | .b32 =>
      match parseLe32 tail with
      | some (v, rest') =>
        let form := if op == 199 then MtForm.movMImm32 f v
          else MtForm.testMImm32 f v
        some (⟨form, n - rest'.length⟩, rest')
      | none => none

/-- Immediate forms: B0-B7 (mov r8, imm8), B8-BF (mov reg, imm16/32;
    REX.W imm64 stays with the pilot), A8/A9 (TEST accumulator, imm),
    C6/C7 /0 (mov r/m, imm) and F6/F7 /0,/1 (TEST r/m, imm). Digits
    beyond the TEST pair refuse; the NOT/NEG/MUL/DIV rows stay with
    their owners. `n` is the full input length for the length count. -/
def mtDecodeImm (op : Nat) (op16 : Bool) (rBit xBit bBit : Nat)
    (wBit rex : Bool) (n : Nat) :
    List Byte → Option (MtDecodiert × List Byte)
  | tail =>
    if 176 ≤ op ∧ op < 184 then
      match tail with
      | imm :: rest =>
        match codeReg (bBit * 8 + (op - 176)) with
        | some r =>
          if mtByteRegOk rex (bBit * 8 + (op - 176)) then
            some (⟨MtForm.movRI8 r imm, n - rest.length⟩, rest)
          else none
        | none => none
      | [] => none
    else if 184 ≤ op ∧ op < 192 then
      if wBit || !op16 then none
      else
        match codeReg (bBit * 8 + (op - 184)) with
        | some r =>
          match mtParseLe16 tail with
          | some (v, rest') =>
            some (⟨MtForm.movRIB16 r v, n - rest'.length⟩, rest')
          | none => none
        | none => none
    else if op == 168 then
      match codeReg (bBit * 8), tail with
      | some r, imm :: rest =>
        if mtByteRegOk rex (bBit * 8) then
          some (⟨MtForm.testAI8 r imm, n - rest.length⟩, rest)
        else none
      | _, _ => none
    else if op == 169 then
      let b := mtWeiteMov op16 wBit
      match codeReg (bBit * 8) with
      | some r =>
        match b with
        | .b16 =>
          match mtParseLe16 tail with
          | some (v, rest') =>
            some (⟨MtForm.testAI16 r v, n - rest'.length⟩, rest')
          | none => none
        | .b64 =>
          match parseLe32 tail with
          | some (v, rest') =>
            some (⟨MtForm.testAI64 r v, n - rest'.length⟩, rest')
          | none => none
        | _ =>
          match parseLe32 tail with
          | some (v, rest') =>
            some (⟨MtForm.testAI32 r v, n - rest'.length⟩, rest')
          | none => none
      | none => none
    else if op == 198 || op == 199 || op == 246 || op == 247 then
      match tail with
      | m :: tail2 =>
        let (mod, rg, rm) := mtSplitModrm m
        let digitOk :=
          (if op == 198 || op == 199 then rg == 0
            else rg == 0 || rg == 1) && rBit == 0
        if !digitOk then none
        else
          let b :=
            if op == 198 || op == 246 then Breite.b8
            else mtWeiteMov op16 wBit
          if mod == 3 then
            if op == 199 && wBit then none
            else
              match codeReg (bBit * 8 + rm) with
              | some r =>
                if (op == 198 || op == 246) &&
                    !mtByteRegOk rex (bBit * 8 + rm) then none
                else mtDecodeImmReg op b r n tail2
              | none => none
          else
            match parseAdrTail rBit xBit bBit (m :: tail2) with
            | some (_, f, rest') => mtDecodeImmMem op b f n rest'
            | none => none
      | [] => none
    else none

/-- Group digit of the ModRM byte following the opcode, 7 when absent. -/
def mtDigit : List Byte → Nat
  | m :: _ => byteNat m / 8 % 8
  | [] => 7

/-- LEA-bare, PUSH/POP, LEAVE, RET-imm, INT3 and the 0F tail (UD2 and
    multi-byte NOP). REX.W LEA stays with decodeCore/decodeLea, 66H LEA
    and 66H UD2 refuse, REX multi-byte NOP refuses. Group digits outside
    8F digit 0 and FF digit 6 refuse (architecturally invalid in 64-bit). -/
def mtDecodeMisc (op : Nat) (op16 : Bool) (rBit xBit bBit : Nat)
    (wBit : Bool) (plen n : Nat) :
    List Byte → Option (MtDecodiert × List Byte)
  | tail =>
    if op == 141 then
      if op16 || wBit then none
      else
        match tail with
        | m :: tail2 =>
          let (mod, _, _) := mtSplitModrm m
          if mod == 3 then none
          else
            match parseAdrTail rBit xBit bBit (m :: tail2) with
            | some (dstR, f, rest') =>
              some (⟨MtForm.leaBare dstR f, n - rest'.length⟩, rest')
            | none => none
        | [] => none
    else if op == 143 || op == 255 then
      let digitOk := ((op == 143 && mtDigit tail == 0) ||
        (op == 255 && mtDigit tail == 6)) && rBit == 0
      if !digitOk then none
      else
        let b := if op16 && !wBit then Breite.b16 else Breite.b64
        match tail with
        | m :: tail2 =>
          let (mod, _, rm) := mtSplitModrm m
          if mod == 3 then
            match codeReg (bBit * 8 + rm) with
            | some r =>
              let form :=
                if op == 143 then MtForm.popR b r else MtForm.pushR b r
              some (⟨form, n - tail2.length⟩, tail2)
            | none => none
          else
            match parseAdrTail rBit xBit bBit (m :: tail2) with
            | some (_, f, rest') =>
              let form :=
                if op == 143 then MtForm.popM b f else MtForm.pushM b f
              some (⟨form, n - rest'.length⟩, rest')
            | none => none
        | [] => none
    else if op == 201 then
      if plen == 0 then some (⟨MtForm.leave, n - tail.length⟩, tail)
      else none
    else if op == 194 then
      if plen == 0 then
        match mtParseLe16 tail with
        | some (v, rest') =>
          some (⟨MtForm.retImm v, n - rest'.length⟩, rest')
        | none => none
      else none
    else if op == 204 then
      if plen == 0 then some (⟨MtForm.int3, n - tail.length⟩, tail)
      else none
    else if op == 15 then
      match tail with
      | b1 :: rest2 =>
        if byteNat b1 == 11 then
          if plen == 0 then some (⟨MtForm.ud2, n - rest2.length⟩, rest2)
          else none
        else if byteNat b1 == 31 then
          if rBit != 0 then none
          else
            match rest2 with
            | m :: tail3 =>
              let (mod, rg, rm) := mtSplitModrm m
              if rg != 0 then none
              else if mod == 3 then
                match codeReg (bBit * 8 + rm) with
                | some r =>
                  some (⟨MtForm.nopReg r, n - tail3.length⟩, tail3)
                | none => none
              else
                match parseAdrTail 0 xBit bBit (m :: tail3) with
                | some (_, f, rest') =>
                  some (⟨MtForm.nopMem f, n - rest'.length⟩, rest')
                | none => none
            | [] => none
        else none
      | [] => none
    else none

/-- Opcode dispatch after the canonical prefix: MOV/TEST modrm and
    immediate rows, the misc family, and explicit refusal of 90H (every
    90H encoding stays with the accepted decodeSx). REX.W word-MOV
    memory rows stay with the accepted decodeC; only the register-direct
    row is taken here. -/
def mtDecodeOpcode (opc : Nat) (op16 : Bool) (rBit xBit bBit : Nat)
    (wBit rex : Bool) (plen n : Nat) :
    List Byte → Option (MtDecodiert × List Byte)
  | tail =>
    if 136 ≤ opc ∧ opc < 140 then
      let isLoad := 138 ≤ opc
      let isByte := opc == 136 || opc == 138
      let b := if isByte then Breite.b8 else mtWeiteMov op16 wBit
      if opc == 137 && wBit then none
      else if !isByte && wBit then
        match tail with
        | m :: _ =>
          let (mod, _, _) := mtSplitModrm m
          if mod == 3 then
            mtDecodeMovRM isLoad isByte b rBit xBit bBit true n tail
          else none
        | [] => none
      else if opc == 137 && plen == 1 && !op16 && xBit == 0 then
        match tail with
        | m :: _ =>
          let (mod, _, _) := mtSplitModrm m
          if mod == 2 || mod == 3 then none
          else mtDecodeMovRM isLoad isByte b rBit xBit bBit rex n tail
        | [] => none
      else mtDecodeMovRM isLoad isByte b rBit xBit bBit rex n tail
    else if opc == 132 || opc == 133 then
      if opc == 133 && wBit then none
      else
        let isByte := opc == 132
        let b := if isByte then Breite.b8 else mtWeiteMov op16 wBit
        mtDecodeTestRM isByte b rBit xBit bBit rex n tail
    else if opc == 168 || opc == 169 || (176 ≤ opc ∧ opc < 192) ||
        opc == 198 || opc == 199 || opc == 246 || opc == 247 then
      mtDecodeImm opc op16 rBit xBit bBit wBit rex n tail
    else if opc == 141 || opc == 143 || opc == 255 || opc == 201 ||
        opc == 194 || opc == 204 || opc == 15 then
      mtDecodeMisc opc op16 rBit xBit bBit wBit plen n tail
    else none

/-- Top-level family decoder: exact F3 0F 1E FA (ENDBR64) first, then
    the canonical 66H/REX prefix parse with opcode dispatch. -/
def decodeMovTest : List Byte → Option (MtDecodiert × List Byte)
  | [] => none
  | f3 :: r0 =>
    let n := (f3 :: r0).length
    if byteNat f3 == 243 then
      match r0 with
      | b1 :: b2 :: b3 :: rest' =>
        if byteNat b1 == 15 && byteNat b2 == 30 && byteNat b3 == 250 then
          some (⟨MtForm.endbr64, n - rest'.length⟩, rest')
        else none
      | _ => none
    else
      match mtPraefix (f3 :: r0) with
      | none => none
      | some (op16, rBit, xBit, bBit, wBit, plen) =>
        let rest := (f3 :: r0).drop plen
        match rest with
        | op :: tail =>
          let rex := plen > (if op16 then 1 else 0)
          mtDecodeOpcode (byteNat op) op16 rBit xBit bBit wBit rex plen
            n tail
        | [] => none

/-! ## 2. Decode pins: the family takes its rows, refuses others'. -/

theorem pin_mt_movRR32 :
    decodeMovTest [natByte 137, natByte 192] =
      some (⟨MtForm.movRR .b32 .rax .rax, 2⟩, []) := by
  decide

theorem pin_mt_movRR88 :
    decodeMovTest [natByte 136, natByte 192] =
      some (⟨MtForm.movRR .b8 .rax .rax, 2⟩, []) := by
  decide

theorem pin_mt_movRR8B :
    decodeMovTest [natByte 139, natByte 200] =
      some (⟨MtForm.movRR .b32 .rcx .rax, 2⟩, []) := by
  decide

theorem pin_mt_movRR8A :
    decodeMovTest [natByte 138, natByte 216] =
      some (⟨MtForm.movRR .b8 .rbx .rax, 2⟩, []) := by
  decide

theorem pin_mt_movRR66 :
    decodeMovTest [natByte 102, natByte 137, natByte 192] =
      some (⟨MtForm.movRR .b16 .rax .rax, 3⟩, []) := by
  decide

theorem pin_mt_movRRw64_refuses :
    decodeMovTest [natByte 72, natByte 137, natByte 192] = none := by
  decide

theorem pin_mt_movRRw64_8b :
    decodeMovTest [natByte 72, natByte 139, natByte 192] =
      some (⟨MtForm.movRR .b64 .rax .rax, 3⟩, []) := by
  decide

theorem pin_mt_movRI8 :
    decodeMovTest [natByte 176, natByte 42] =
      some (⟨MtForm.movRI8 .rax (natByte 42), 2⟩, []) := by
  decide

theorem pin_mt_movRIB16_r8 :
    decodeMovTest [natByte 102, natByte 65, natByte 184, natByte 5,
      natByte 0] =
      some (⟨MtForm.movRIB16 .r8 (BitVec.ofNat 16 5), 5⟩, []) := by
  decide

theorem pin_mt_movRImm32 :
    decodeMovTest [natByte 199, natByte 192, natByte 5, natByte 0,
      natByte 0, natByte 0] =
      some (⟨MtForm.movRImm32 .rax (BitVec.ofNat 32 5), 6⟩, []) := by
  decide

theorem pin_mt_testRImm32 :
    decodeMovTest [natByte 247, natByte 192, natByte 1, natByte 0,
      natByte 0, natByte 0] =
      some (⟨MtForm.testRImm32 .rax (BitVec.ofNat 32 1), 6⟩, []) := by
  decide

theorem pin_mt_89_nw_mem_mod1 :
    (decodeMovTest [natByte 64, natByte 137, natByte 69,
      natByte 5]).isSome = true := by
  decide

theorem pin_mt_c7_w64_mem :
    (decodeMovTest [natByte 72, natByte 199, natByte 69, natByte 8,
      natByte 1, natByte 0, natByte 0, natByte 0]).isSome = true := by
  decide

theorem pin_mt_movRIB16 :
    decodeMovTest [natByte 102, natByte 184, natByte 5, natByte 0] =
      some (⟨MtForm.movRIB16 .rax (BitVec.ofNat 16 5), 4⟩, []) := by
  decide

theorem pin_mt_testAI8 :
    decodeMovTest [natByte 168, natByte 1] =
      some (⟨MtForm.testAI8 .rax (natByte 1), 2⟩, []) := by
  decide

theorem pin_mt_testAI32 :
    decodeMovTest [natByte 169, natByte 1, natByte 0, natByte 0, natByte 0] =
      some (⟨MtForm.testAI32 .rax (BitVec.ofNat 32 1), 5⟩, []) := by
  decide

theorem pin_mt_testAI64 :
    decodeMovTest [natByte 72, natByte 169, natByte 1, natByte 0,
      natByte 0, natByte 0] =
      some (⟨MtForm.testAI64 .rax (BitVec.ofNat 32 1), 6⟩, []) := by
  decide

theorem pin_mt_movRImm8 :
    decodeMovTest [natByte 198, natByte 192, natByte 7] =
      some (⟨MtForm.movRImm8 .rax (natByte 7), 3⟩, []) := by
  decide

theorem pin_mt_testRImm8 :
    decodeMovTest [natByte 246, natByte 192, natByte 1] =
      some (⟨MtForm.testRImm8 .rax (natByte 1), 3⟩, []) := by
  decide

theorem pin_mt_testRR84 :
    decodeMovTest [natByte 132, natByte 192] =
      some (⟨MtForm.testRR .b8 .rax .rax, 2⟩, []) := by
  decide

theorem pin_mt_testRR85 :
    decodeMovTest [natByte 133, natByte 192] =
      some (⟨MtForm.testRR .b32 .rax .rax, 2⟩, []) := by
  decide

theorem pin_mt_testRR85_16 :
    decodeMovTest [natByte 102, natByte 133, natByte 192] =
      some (⟨MtForm.testRR .b16 .rax .rax, 3⟩, []) := by
  decide

theorem pin_mt_popR :
    decodeMovTest [natByte 143, natByte 192] =
      some (⟨MtForm.popR .b64 .rax, 2⟩, []) := by
  decide

theorem pin_mt_pushR :
    decodeMovTest [natByte 255, natByte 240] =
      some (⟨MtForm.pushR .b64 .rax, 2⟩, []) := by
  decide

theorem pin_mt_pushRrsi :
    decodeMovTest [natByte 255, natByte 246] =
      some (⟨MtForm.pushR .b64 .rsi, 2⟩, []) := by
  decide

theorem pin_mt_leave :
    decodeMovTest [natByte 201] = some (⟨MtForm.leave, 1⟩, []) := by
  decide

theorem pin_mt_retImm :
    decodeMovTest [natByte 194, natByte 4, natByte 0] =
      some (⟨MtForm.retImm (BitVec.ofNat 16 4), 3⟩, []) := by
  decide

theorem pin_mt_int3 :
    decodeMovTest [natByte 204] = some (⟨MtForm.int3, 1⟩, []) := by
  decide

theorem pin_mt_nopReg :
    decodeMovTest [natByte 15, natByte 31, natByte 192] =
      some (⟨MtForm.nopReg .rax, 3⟩, []) := by
  decide

theorem pin_mt_nopReg66 :
    decodeMovTest [natByte 102, natByte 15, natByte 31, natByte 192] =
      some (⟨MtForm.nopReg .rax, 4⟩, []) := by
  decide

theorem pin_mt_ud2 :
    decodeMovTest [natByte 15, natByte 11] =
      some (⟨MtForm.ud2, 2⟩, []) := by
  decide

theorem pin_mt_endbr64 :
    decodeMovTest [natByte 243, natByte 15, natByte 30, natByte 250] =
      some (⟨MtForm.endbr64, 4⟩, []) := by
  decide

/-- Memory rows decode (address form checked by the later round trips). -/
theorem pin_mt_mem_ok :
    (decodeMovTest [natByte 137, natByte 69, natByte 5]).isSome = true ∧
    (decodeMovTest [natByte 139, natByte 69, natByte 5]).isSome = true ∧
    (decodeMovTest [natByte 141, natByte 69, natByte 5]).isSome = true ∧
    (decodeMovTest [natByte 199, natByte 69, natByte 5, natByte 9,
      natByte 0, natByte 0, natByte 0]).isSome = true ∧
    (decodeMovTest [natByte 247, natByte 77, natByte 8, natByte 1,
      natByte 0, natByte 0, natByte 0]).isSome = true ∧
    (decodeMovTest [natByte 15, natByte 31, natByte 69,
      natByte 8]).isSome = true := by
  decide

/-- Rows owned elsewhere refuse here: every 90H (decodeSx), REX.W B8
    (pilot imm64), REX.W 85 (decodeCore/decodeIntHw), wrong group
    digits, LEA mod=3, and prefixed LEAVE/RET/INT3. -/
theorem pin_mt_fremd_verweigert :
    decodeMovTest [natByte 144] = none ∧
    decodeMovTest [natByte 72, natByte 184, natByte 1, natByte 0,
      natByte 0, natByte 0, natByte 0, natByte 0, natByte 0,
      natByte 0] = none ∧
    decodeMovTest [natByte 72, natByte 133, natByte 192] = none ∧
    decodeMovTest [natByte 246, natByte 208, natByte 1] = none ∧
    decodeMovTest [natByte 199, natByte 200, natByte 1, natByte 0,
      natByte 0, natByte 0] = none ∧
    decodeMovTest [natByte 143, natByte 200] = none ∧
    decodeMovTest [natByte 255, natByte 192] = none ∧
    decodeMovTest [natByte 141, natByte 192] = none ∧
    decodeMovTest [natByte 198, natByte 200, natByte 7] = none ∧
    decodeMovTest [natByte 102, natByte 201] = none := by
  decide

/-! ## 3. Chain verdicts: refusal of the new rows, acceptance elsewhere.

  Each verdict is a closed `decide`. Refused rows are taken by the
  family decoder (§2). Accepted rows stay with their accepted owners
  (per-row citations in CUTS): REX.W TEST-reg with decodeCore, REX.W
  B8-imm64 and REX.W 89-reg with the pilot, bare B8-imm32 and REX.W
  C7-reg with decodeC, REX.W 89/8B memory with the accepted memory
  rows, REX 89 mod 2/3 with decodeNarrow. §4 probes settled the
  boundary rows. -/

theorem pin_kap_89 :
    kapDecode [natByte 137, natByte 192] = none := by
  decide

theorem pin_kap_8b :
    kapDecode [natByte 139, natByte 200] = none := by
  decide

theorem pin_kap_88 :
    kapDecode [natByte 136, natByte 192] = none := by
  decide

theorem pin_kap_8a :
    kapDecode [natByte 138, natByte 216] = none := by
  decide

theorem pin_kap_89_66 :
    kapDecode [natByte 102, natByte 137, natByte 192] = none := by
  decide

theorem pin_kap_89_w64 :
    (kapDecode [natByte 72, natByte 137, natByte 192]).isSome = true := by
  decide

theorem pin_kap_b0 :
    kapDecode [natByte 176, natByte 42] = none := by
  decide

theorem pin_kap_b8 :
    (kapDecode [natByte 184, natByte 1, natByte 0, natByte 0,
      natByte 0]).isSome = true := by
  decide

theorem pin_kap_b8_66 :
    kapDecode [natByte 102, natByte 184, natByte 5, natByte 0] = none := by
  decide

theorem pin_kap_89_mem :
    kapDecode [natByte 137, natByte 69, natByte 5] = none := by
  decide

theorem pin_kap_a8 :
    kapDecode [natByte 168, natByte 1] = none := by
  decide

theorem pin_kap_a9 :
    kapDecode [natByte 169, natByte 1, natByte 0, natByte 0,
      natByte 0] = none := by
  decide

theorem pin_kap_a9_w64 :
    kapDecode [natByte 72, natByte 169, natByte 1, natByte 0, natByte 0,
      natByte 0] = none := by
  decide

theorem pin_kap_c6 :
    kapDecode [natByte 198, natByte 192, natByte 7] = none := by
  decide

theorem pin_kap_c7_w64 :
    (kapDecode [natByte 72, natByte 199, natByte 192, natByte 5, natByte 0,
      natByte 0, natByte 0]).isSome = true := by
  decide

theorem pin_kap_f6 :
    kapDecode [natByte 246, natByte 192, natByte 1] = none := by
  decide

theorem pin_kap_84 :
    kapDecode [natByte 132, natByte 192] = none := by
  decide

theorem pin_kap_85 :
    kapDecode [natByte 133, natByte 192] = none := by
  decide

theorem pin_kap_85_66 :
    kapDecode [natByte 102, natByte 133, natByte 192] = none := by
  decide

theorem pin_kap_misc_verweigert :
    kapDecode [natByte 143, natByte 192] = none ∧
    kapDecode [natByte 255, natByte 240] = none ∧
    kapDecode [natByte 201] = none ∧
    kapDecode [natByte 194, natByte 4, natByte 0] = none ∧
    kapDecode [natByte 204] = none ∧
    kapDecode [natByte 15, natByte 31, natByte 192] = none ∧
    kapDecode [natByte 102, natByte 15, natByte 31, natByte 192] = none ∧
    kapDecode [natByte 15, natByte 11] = none ∧
    kapDecode [natByte 243, natByte 15, natByte 30, natByte 250] = none ∧
    kapDecode [natByte 144] = none := by
  decide

theorem pin_kap_8b_mem :
    kapDecode [natByte 139, natByte 69, natByte 5] = none := by
  decide

theorem pin_kap_8d :
    kapDecode [natByte 141, natByte 69, natByte 5] = none := by
  decide

theorem pin_kap_c7_mem :
    kapDecode [natByte 199, natByte 69, natByte 5, natByte 9, natByte 0,
      natByte 0, natByte 0] = none := by
  decide

theorem pin_kap_f7_mem :
    kapDecode [natByte 247, natByte 77, natByte 8, natByte 1, natByte 0,
      natByte 0, natByte 0] = none := by
  decide

theorem pin_kap_nop_mem :
    kapDecode [natByte 15, natByte 31, natByte 69, natByte 8] = none := by
  decide

theorem pin_kap_89_w64_mem :
    (kapDecode [natByte 72, natByte 137, natByte 69,
      natByte 8]).isSome = true := by
  decide

/-! ## 4. Scope probes: ownership of the boundary rows.

  Each probe states refusal; a failure identifies a wired owner, and the
  row is then excluded from the family decoder with the owner cited. -/

theorem probe_kap_8b_w64 :
    kapDecode [natByte 72, natByte 139, natByte 192] = none := by
  decide

theorem pin_kap_8b_w64_mem :
    (kapDecode [natByte 72, natByte 139, natByte 69,
      natByte 8]).isSome = true := by
  decide

theorem probe_kap_88_w64 :
    kapDecode [natByte 72, natByte 136, natByte 192] = none := by
  decide

theorem probe_kap_8a_w64 :
    kapDecode [natByte 72, natByte 138, natByte 192] = none := by
  decide

theorem probe_kap_c7_reg :
    kapDecode [natByte 199, natByte 192, natByte 5, natByte 0, natByte 0,
      natByte 0] = none := by
  decide

theorem probe_kap_c7_reg_66 :
    kapDecode [natByte 102, natByte 199, natByte 192, natByte 5,
      natByte 0] = none := by
  decide

theorem probe_kap_c7_reg_rex :
    kapDecode [natByte 65, natByte 199, natByte 192, natByte 5, natByte 0,
      natByte 0, natByte 0] = none := by
  decide

theorem probe_kap_f7_reg :
    kapDecode [natByte 247, natByte 192, natByte 1, natByte 0, natByte 0,
      natByte 0] = none := by
  decide

theorem probe_kap_f7_reg_rex :
    kapDecode [natByte 64, natByte 247, natByte 192, natByte 1, natByte 0,
      natByte 0, natByte 0] = none := by
  decide

theorem probe_kap_b8_66_rex :
    kapDecode [natByte 102, natByte 65, natByte 184, natByte 5,
      natByte 0] = none := by
  decide

theorem probe_kap_c6_rex :
    kapDecode [natByte 64, natByte 198, natByte 192, natByte 7] = none := by
  decide

theorem probe_kap_c7_mem_66 :
    kapDecode [natByte 102, natByte 199, natByte 69, natByte 5, natByte 9,
      natByte 0] = none := by
  decide

theorem pin_kap_89_nw :
    (kapDecode [natByte 64, natByte 137, natByte 192]).isSome = true := by
  decide

theorem pin_kap_89_nw_mem :
    (kapDecode [natByte 64, natByte 137, natByte 129, natByte 1, natByte 0,
      natByte 0, natByte 0]).isSome = true := by
  decide

theorem probe_kap_c7_w64_mem :
    kapDecode [natByte 72, natByte 199, natByte 69, natByte 8, natByte 1,
      natByte 0, natByte 0, natByte 0] = none := by
  decide

theorem probe_kap_c7_66_rex :
    kapDecode [natByte 102, natByte 65, natByte 199, natByte 192,
      natByte 5, natByte 0] = none := by
  decide

theorem probe_kap_c7_nw_mem :
    kapDecode [natByte 64, natByte 199, natByte 69, natByte 8, natByte 1,
      natByte 0, natByte 0, natByte 0] = none := by
  decide

theorem probe_kap_f7_w64_mem :
    kapDecode [natByte 72, natByte 247, natByte 69, natByte 8, natByte 1,
      natByte 0, natByte 0, natByte 0] = none := by
  decide

theorem probe_kap_c6_w64_mem :
    kapDecode [natByte 72, natByte 198, natByte 69, natByte 8,
      natByte 7] = none := by
  decide

theorem probe_kap_f6_w64_mem :
    kapDecode [natByte 72, natByte 246, natByte 69, natByte 8,
      natByte 1] = none := by
  decide

theorem probe_kap_8f_w64 :
    kapDecode [natByte 72, natByte 143, natByte 192] = none := by
  decide

theorem probe_kap_ff_w64 :
    kapDecode [natByte 72, natByte 255, natByte 240] = none := by
  decide

/-! ## 5. Canonical encoder.

  Every row encodes to bytes the family decoder takes back (§6). The
  register rows use the 8B load-form opcode uniformly (89 mod 2/3 with
  a W0/X0 REX stays with decodeNarrow); memory rows reuse the accepted
  encodeAdr tail with a width-canonical REX. Digit rows fix R = 0 as
  the decoder demands; PUSH-memory uses rsi for digit 6. Widths the
  decoder never takes (64-bit memory MOV/TEST-reg, 8/32-bit stack
  words) refuse loudly. -/

/-- Canonical REX over an accepted address tail: the W form at 64 bits
    (encodeAdr always emits the 72-based REX), the W-cleared twin
    below, dropped when bare 0x40 unless `force` holds (byte operands
    with codes 4-7 need a REX to name the low bytes SPL/BPL/SIL/DIL
    instead of AH/CH/DH/BH). -/
def mtRexFuer (b : Breite) (rex : Byte) (force : Bool) : List Byte :=
  let w0 := natByte (byteNat rex - 8)
  match b with
  | .b64 => [rex]
  | _ => if byteNat w0 == 64 && !force then [] else [w0]

/-- Canonical REX for register-direct rows (X = 0, no SIB): W/R/B
    bits, omitted when bare unless `force` holds (byte codes 4-7). -/
def mtRexReg (w r b : Nat) (force : Bool) : List Byte :=
  if w == 1 || r == 1 || b == 1 || force
    then [natByte (64 + 8 * w + 4 * r + b)]
  else []

/-- Canonical 66H prefix at 16 bits. -/
def mtPre16 (b : Breite) : List Byte :=
  match b with | .b16 => [natByte 102] | _ => []

/-- The decodeNarrow hole: a bare W0/X0 REX with a mod-2 ModRM under
    opcode 89 stays with decodeNarrow, so the encoder declines it. -/
def mtNarrowLoch (rexList tail : List Byte) : Bool :=
  match rexList, tail with
  | [r], m :: _ =>
    decide (64 ≤ byteNat r ∧ byteNat r < 72 ∧ byteNat r / 2 % 2 = 0 ∧
      byteNat m / 64 = 2)
  | _, _ => false

/-- Encode one memory operand: prefix, canonical REX, opcode, tail.
    The reg field comes from `reg` (digit rows use rax, PUSH uses
    rsi for digit 6). When `narrowFalle` holds (89 word stores), the
    decodeNarrow hole refuses. Unencodable address forms refuse. -/
def encodeMtMem (pre : List Byte) (b : Breite) (op : Nat) (reg : Register)
    (f : AdrForm) (narrowFalle : Bool) : Option (List Byte) :=
  match encodeAdr reg f with
  | some (rex :: tail) =>
    let rexList :=
      mtRexFuer b rex (b == .b8 && decide (4 ≤ regLow reg))
    if narrowFalle && mtNarrowLoch rexList tail then none
    else some (pre ++ rexList ++ [natByte op] ++ tail)
  | _ => none

/-- Canonical byte encoding of one family form. Register MOV uses the
    8B load opcode at every width; TEST uses 84/85; the accumulator,
    B8 and group rows use their fixed opcodes; LEA is bare (W-cleared
    REX, never REX.W); NOP/C9/C2/CC/UD2/ENDBR64 are fixed bytes. -/
def encodeMt : MtForm → Option (List Byte)
  | .movRR b dst src =>
    let op := if b == .b8 then 138 else 139
    let w := if b == .b64 then 1 else 0
    some (mtPre16 b ++
      mtRexReg w (regHigh dst) (regHigh src)
        (b == .b8 &&
          (decide (4 ≤ regLow dst) || decide (4 ≤ regLow src))) ++
      [natByte op, modrmReg (regLow dst) (regLow src)])
  | .movRM b f src =>
    if b == .b64 then none
    else
      let op := if b == .b8 then 136 else 137
      encodeMtMem (mtPre16 b) b op src f (op == 137)
  | .movMR b dst f =>
    if b == .b64 then none
    else
      let op := if b == .b8 then 138 else 139
      encodeMtMem (mtPre16 b) b op dst f false
  | .movRI8 r v =>
    some (mtRexReg 0 0 (regHigh r) (decide (4 ≤ regLow r)) ++
      [natByte (176 + regLow r), v])
  | .movRIB16 r v =>
    some ([natByte 102] ++ mtRexReg 0 0 (regHigh r) false ++
      [natByte (184 + regLow r)] ++ mtLeBytes16 v)
  | .movRImm8 r v =>
    some (mtRexReg 0 0 (regHigh r) (decide (4 ≤ regLow r)) ++
      [natByte 198, modrmReg 0 (regLow r), v])
  | .movRImm16 r v =>
    some ([natByte 102] ++ mtRexReg 0 0 (regHigh r) false ++
      [natByte 199, modrmReg 0 (regLow r)] ++ mtLeBytes16 v)
  | .movRImm32 r v =>
    some (mtRexReg 0 0 (regHigh r) false ++
      [natByte 199, modrmReg 0 (regLow r)] ++ leBytes32 v)
  | .movMImm8 f v =>
    match encodeMtMem [] .b8 198 .rax f false with
    | some bs => some (bs ++ [v])
    | none => none
  | .movMImm16 f v =>
    match encodeMtMem [natByte 102] .b16 199 .rax f false with
    | some bs => some (bs ++ mtLeBytes16 v)
    | none => none
  | .movMImm32 f v =>
    match encodeMtMem [] .b32 199 .rax f false with
    | some bs => some (bs ++ leBytes32 v)
    | none => none
  | .movMImm64 f v =>
    match encodeMtMem [] .b64 199 .rax f false with
    | some bs => some (bs ++ leBytes32 v)
    | none => none
  | .testRR b lhs rhs =>
    if b == .b64 then none
    else
      let op := if b == .b8 then 132 else 133
      let w := 0
      some (mtPre16 b ++
        mtRexReg w (regHigh lhs) (regHigh rhs)
          (b == .b8 &&
            (decide (4 ≤ regLow lhs) || decide (4 ≤ regLow rhs))) ++
        [natByte op, modrmReg (regLow lhs) (regLow rhs)])
  | .testRM b f rhs =>
    if b == .b64 then none
    else
      let op := if b == .b8 then 132 else 133
      encodeMtMem (mtPre16 b) b op rhs f false
  | .testAI8 r v =>
    some (mtRexReg 0 0 (regHigh r) (decide (4 ≤ regLow r)) ++
      [natByte 168, v])
  | .testAI16 r v =>
    some ([natByte 102] ++ mtRexReg 0 0 (regHigh r) false ++
      [natByte 169] ++ mtLeBytes16 v)
  | .testAI32 r v =>
    some (mtRexReg 0 0 (regHigh r) false ++
      [natByte 169] ++ leBytes32 v)
  | .testAI64 r v =>
    some (mtRexReg 1 0 (regHigh r) false ++
      [natByte 169] ++ leBytes32 v)
  | .testRImm8 r v =>
    some (mtRexReg 0 0 (regHigh r) (decide (4 ≤ regLow r)) ++
      [natByte 246, modrmReg 0 (regLow r), v])
  | .testRImm16 r v =>
    some ([natByte 102] ++ mtRexReg 0 0 (regHigh r) false ++
      [natByte 247, modrmReg 0 (regLow r)] ++ mtLeBytes16 v)
  | .testRImm32 r v =>
    some (mtRexReg 0 0 (regHigh r) false ++
      [natByte 247, modrmReg 0 (regLow r)] ++ leBytes32 v)
  | .testRImm64 r v =>
    some (mtRexReg 1 0 (regHigh r) false ++
      [natByte 247, modrmReg 0 (regLow r)] ++ leBytes32 v)
  | .testMImm8 f v =>
    match encodeMtMem [] .b8 246 .rax f false with
    | some bs => some (bs ++ [v])
    | none => none
  | .testMImm16 f v =>
    match encodeMtMem [natByte 102] .b16 247 .rax f false with
    | some bs => some (bs ++ mtLeBytes16 v)
    | none => none
  | .testMImm32 f v =>
    match encodeMtMem [] .b32 247 .rax f false with
    | some bs => some (bs ++ leBytes32 v)
    | none => none
  | .testMImm64 f v =>
    match encodeMtMem [] .b64 247 .rax f false with
    | some bs => some (bs ++ leBytes32 v)
    | none => none
  | .leaBare dst f => encodeMtMem [] .b32 141 dst f false
  | .nopMem f =>
    match encodeAdr .rax f with
    | some (rex :: tail) =>
      some (mtRexFuer .b32 rex false ++
        [natByte 15, natByte 31] ++ tail)
    | _ => none
  | .nopReg r =>
    some (mtRexReg 0 0 (regHigh r) false ++
      [natByte 15, natByte 31, modrmReg 0 (regLow r)])
  | .endbr64 => some [natByte 243, natByte 15, natByte 30, natByte 250]
  | .pushR b r =>
    if b == .b16 || b == .b64 then
      let w := if b == .b64 then 1 else 0
      some (mtPre16 b ++ mtRexReg w 0 (regHigh r) false ++
        [natByte 255, modrmReg 6 (regLow r)])
    else none
  | .pushM b f =>
    if b == .b16 || b == .b64 then
      encodeMtMem (mtPre16 b) b 255 .rsi f false
    else none
  | .popR b r =>
    if b == .b16 || b == .b64 then
      let w := if b == .b64 then 1 else 0
      some (mtPre16 b ++ mtRexReg w 0 (regHigh r) false ++
        [natByte 143, modrmReg 0 (regLow r)])
    else none
  | .popM b f =>
    if b == .b16 || b == .b64 then
      encodeMtMem (mtPre16 b) b 143 .rax f false
    else none
  | .leave => some [natByte 201]
  | .retImm n => some ([natByte 194] ++ mtLeBytes16 n)
  | .int3 => some [natByte 204]
  | .ud2 => some [natByte 15, natByte 11]

/-! ## 6. Round trips: the encoder inverts the decoder.

  General befehl round trips (suffix-general, register case analysis)
  for the finite rows; lengths are pinned in §2 and closed below.
  Memory rows use closed instances over shared address witnesses
  (a general mem round trip awaits a parseAdrTail∘encodeAdr inversion
  lemma, named in CUTS, never assumed). -/

/-- Shared memory witness: [rbp + 5] (disp8). -/
def fMT : AdrForm := ⟨some .rbp, none, 1, BitVec.ofNat 32 5, .d8, false⟩

/-- Shared memory witness: [rax + rcx*4 + 7] (SIB disp8). -/
def fMTSib : AdrForm :=
  ⟨some .rax, some .rcx, 2, BitVec.ofNat 32 7, .d8, false⟩

theorem roundtrip_mt_movRR (b : Breite) (dst src : Register)
    (suffix : List Byte) :
    ((encodeMt (.movRR b dst src)).bind
      (fun bs => decodeMovTest (bs ++ suffix))).map
      (fun p => (p.1.befehl, p.2)) = some ((.movRR b dst src), suffix) := by
  cases b <;> cases dst <;> cases src <;> rfl

theorem roundtrip_mt_testRR (b : Breite) (lhs rhs : Register)
    (suffix : List Byte) (h : b ≠ .b64) :
    ((encodeMt (.testRR b lhs rhs)).bind
      (fun bs => decodeMovTest (bs ++ suffix))).map
      (fun p => (p.1.befehl, p.2)) = some ((.testRR b lhs rhs), suffix) := by
  cases b with
  | b64 => exact absurd rfl h
  | b8 => cases lhs <;> cases rhs <;> rfl
  | b16 => cases lhs <;> cases rhs <;> rfl
  | b32 => cases lhs <;> cases rhs <;> rfl

theorem roundtrip_mt_nopReg (r : Register) (suffix : List Byte) :
    ((encodeMt (.nopReg r)).bind
      (fun bs => decodeMovTest (bs ++ suffix))).map
      (fun p => (p.1.befehl, p.2)) = some ((.nopReg r), suffix) := by
  cases r <;> rfl

theorem roundtrip_mt_pushR (b : Breite) (r : Register) (suffix : List Byte)
    (h : b = .b16 ∨ b = .b64) :
    ((encodeMt (.pushR b r)).bind
      (fun bs => decodeMovTest (bs ++ suffix))).map
      (fun p => (p.1.befehl, p.2)) = some ((.pushR b r), suffix) := by
  cases b with
  | b16 => cases r <;> rfl
  | b64 => cases r <;> rfl
  | b8 => cases h with | inl h16 => cases h16 | inr h64 => cases h64
  | b32 => cases h with | inl h16 => cases h16 | inr h64 => cases h64

theorem roundtrip_mt_popR (b : Breite) (r : Register) (suffix : List Byte)
    (h : b = .b16 ∨ b = .b64) :
    ((encodeMt (.popR b r)).bind
      (fun bs => decodeMovTest (bs ++ suffix))).map
      (fun p => (p.1.befehl, p.2)) = some ((.popR b r), suffix) := by
  cases b with
  | b16 => cases r <;> rfl
  | b64 => cases r <;> rfl
  | b8 => cases h with | inl h16 => cases h16 | inr h64 => cases h64
  | b32 => cases h with | inl h16 => cases h16 | inr h64 => cases h64

theorem roundtrip_mt_endbr64 (suffix : List Byte) :
    ((encodeMt .endbr64).bind
      (fun bs => decodeMovTest (bs ++ suffix))).map
      (fun p => (p.1.befehl, p.2)) = some ((.endbr64), suffix) := by
  rfl

theorem roundtrip_mt_leave (suffix : List Byte) :
    ((encodeMt .leave).bind
      (fun bs => decodeMovTest (bs ++ suffix))).map
      (fun p => (p.1.befehl, p.2)) = some ((.leave), suffix) := by
  cases suffix <;> rfl

theorem roundtrip_mt_int3 (suffix : List Byte) :
    ((encodeMt .int3).bind
      (fun bs => decodeMovTest (bs ++ suffix))).map
      (fun p => (p.1.befehl, p.2)) = some ((.int3), suffix) := by
  cases suffix <;> rfl

theorem roundtrip_mt_ud2 (suffix : List Byte) :
    ((encodeMt .ud2).bind
      (fun bs => decodeMovTest (bs ++ suffix))).map
      (fun p => (p.1.befehl, p.2)) = some ((.ud2), suffix) := by
  rfl

/-- Excluded rows decode elsewhere: REX.W TEST-reg through the accepted
    core row, REX.W B8-imm64 through the pilot. -/
theorem pin_kap_fremd_nimmt :
    (kapDecode [natByte 72, natByte 133, natByte 192]).isSome = true ∧
    (kapDecode [natByte 72, natByte 184, natByte 1, natByte 0, natByte 0,
      natByte 0, natByte 0, natByte 0, natByte 0, natByte 0]).isSome =
      true := by
  decide

/-! ## 7. Register semantics on the accepted machine.

  The step reuses the accepted evaluators unchanged: `mergeRegNarrow`
  (architectural 8/16-merge, 32-zero-extend), `andW` (width-correct
  TEST snapshot, AF free), `adrEff` (effective addresses, truncated
  to 32 bits for bare LEA) and `schrittRegister`/`ripNach`. Memory
  MOV/TEST, stack words and traps step in the adapter (§9) or refuse:
  faults are outcomes, never successors. -/

/-- Family step on the canonical state; `none` is an explicit refusal
    (bad length, memory form, stack form, trap). -/
def mtSchritt (d : MtDecodiert) (s : Zustand) : Option Zustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    let nach := ripNach s.rip d.laenge
    match d.befehl with
    | .movRR b dst src =>
      some (schrittRegister s nach s.flags dst
        (mergeRegNarrow b (s.register dst) (s.register src)))
    | .movRI8 r v =>
      some (schrittRegister s nach s.flags r
        (mergeRegNarrow .b8 (s.register r) (BitVec.ofNat 64 v.toNat)))
    | .movRIB16 r v =>
      some (schrittRegister s nach s.flags r
        (mergeRegNarrow .b16 (s.register r) (BitVec.ofNat 64 v.toNat)))
    | .movRImm8 r v =>
      some (schrittRegister s nach s.flags r
        (mergeRegNarrow .b8 (s.register r) (BitVec.ofNat 64 v.toNat)))
    | .movRImm16 r v =>
      some (schrittRegister s nach s.flags r
        (mergeRegNarrow .b16 (s.register r) (BitVec.ofNat 64 v.toNat)))
    | .movRImm32 r v =>
      some (schrittRegister s nach s.flags r
        (mergeRegNarrow .b32 (s.register r) (BitVec.ofNat 64 v.toNat)))
    | .testRR b lhs rhs =>
      let r := andW b (s.register lhs) (s.register rhs)
      some ({ s with rip := nach, flags := r.2 })
    | .testAI8 r v =>
      let r := andW .b8 (s.register r) (BitVec.ofNat 64 v.toNat)
      some ({ s with rip := nach, flags := r.2 })
    | .testAI16 r v =>
      let r := andW .b16 (s.register r) (BitVec.ofNat 64 v.toNat)
      some ({ s with rip := nach, flags := r.2 })
    | .testAI32 r v =>
      let r := andW .b32 (s.register r) (BitVec.ofNat 64 v.toNat)
      some ({ s with rip := nach, flags := r.2 })
    | .testAI64 r v =>
      let r :=
        andW .b64 (s.register r) (sext .b32 (BitVec.ofNat 64 v.toNat))
      some ({ s with rip := nach, flags := r.2 })
    | .testRImm8 r v =>
      let r := andW .b8 (s.register r) (BitVec.ofNat 64 v.toNat)
      some ({ s with rip := nach, flags := r.2 })
    | .testRImm16 r v =>
      let r := andW .b16 (s.register r) (BitVec.ofNat 64 v.toNat)
      some ({ s with rip := nach, flags := r.2 })
    | .testRImm32 r v =>
      let r := andW .b32 (s.register r) (BitVec.ofNat 64 v.toNat)
      some ({ s with rip := nach, flags := r.2 })
    | .testRImm64 r v =>
      let r :=
        andW .b64 (s.register r) (sext .b32 (BitVec.ofNat 64 v.toNat))
      some ({ s with rip := nach, flags := r.2 })
    | .leaBare dst f =>
      some (schrittRegister s nach s.flags dst
        (mergeRegNarrow .b32 (s.register dst) (trunc .b32 (adrEff s nach f))))
    | .nopMem _ => some ({ s with rip := nach })
    | .nopReg _ => some ({ s with rip := nach })
    | .endbr64 => some ({ s with rip := nach })
    | _ => none

/-- A MOV step is the accepted narrow move with RIP advance. -/
theorem mtSchritt_movRR_ist_moveNarrow (b : Breite) (dst src : Register)
    (l : Nat) (s : Zustand) :
    mtSchritt ⟨.movRR b dst src, l⟩ s =
      match laengeOk l with
      | true =>
        some ({ moveNarrow s b dst src with rip := ripNach s.rip l })
      | false => none := by
  unfold mtSchritt moveNarrow schrittRegister
  cases h : laengeOk l <;> rfl

/-- A TEST step keeps the registers and installs the accepted AND
    flag snapshot. -/
theorem mtSchritt_testRR_flags (b : Breite) (lhs rhs : Register)
    (l : Nat) (s : Zustand) :
    mtSchritt ⟨.testRR b lhs rhs, l⟩ s =
      if laengeOk l then
        some ({ s with rip := ripNach s.rip l, flags := (andW b (s.register lhs) (s.register rhs)).2 })
      else none := by
  unfold mtSchritt
  cases h : laengeOk l with
  | false => rfl
  | true => rfl

/-- A MOV step preserves flags and memory and advances RIP. -/
theorem mtSchritt_movRR_rahmen (b : Breite) (dst src : Register)
    (l : Nat) (s s' : Zustand)
    (h : mtSchritt ⟨.movRR b dst src, l⟩ s = some s') :
    s'.flags = s.flags ∧ s'.speicher = s.speicher ∧
      s'.rip = ripNach s.rip l := by
  unfold mtSchritt schrittRegister at h
  cases hlen : laengeOk l with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases h
    exact ⟨rfl, rfl, rfl⟩

/-! ## 8. Extended chain: the old chain first, the family only where
  it refuses, so dispatch agrees with the old chain on every byte
  string the old chain decodes. A maintainer wires the family rows
  into `kapDecode` (HwKapsteinDecoder.lean) behind its last arm. -/

/-- One decoded row of the extended chain. -/
inductive MtKap where
  | kap : KapDekodiert → MtKap
  | mt : MtDecodiert → MtKap
  deriving DecidableEq, Repr

/-- The extended priority chain. -/
def kapDecodeMitMt : List Byte → Option (MtKap × List Byte) :=
  fun bs =>
    match kapDecode bs with
    | some (k, rest) => some (.kap k, rest)
    | none =>
      match decodeMovTest bs with
      | some (d, rest) => some (.mt d, rest)
      | none => none

/-- The extended chain agrees with the old chain wherever it accepts:
    no previously decoded form is shadowed. -/
theorem kapDecodeMitMt_kap (bs : List Byte) (k : KapDekodiert)
    (rest : List Byte) (h : kapDecode bs = some (k, rest)) :
    kapDecodeMitMt bs = some (.kap k, rest) := by
  unfold kapDecodeMitMt
  rw [h]

/-- Where the old chain refuses, a covered family row is taken. -/
theorem kapDecodeMitMt_mt (bs : List Byte) (d : MtDecodiert)
    (rest : List Byte) (h1 : kapDecode bs = none)
    (h2 : decodeMovTest bs = some (d, rest)) :
    kapDecodeMitMt bs = some (.mt d, rest) := by
  unfold kapDecodeMitMt
  rw [h1, h2]

/-- Where both chains refuse, the extended chain refuses. -/
theorem kapDecodeMitMt_nichts (bs : List Byte)
    (h1 : kapDecode bs = none) (h2 : decodeMovTest bs = none) :
    kapDecodeMitMt bs = none := by
  unfold kapDecodeMitMt
  rw [h1, h2]

/-! ## 9. Adapter plug on the coherent machine.

  Register steps lift `mtSchritt` over the acting core's projection;
  memory MOV/TEST delegate the accepted `hwAddrStore`/`hwAddrLoad`
  exactly; stack words issue/observe through the acting core's TSO
  buffer with owner-only forwarding; INT3/UD2 decode but admit no
  event (faults are outcomes, never successors). -/

/-- Family events on the coherent machine. -/
inductive MtEreignis where
  | reg (d : MtDecodiert)
  | store (b : Breite) (f : AdrForm) (ripNext : Adresse) (src : Register)
    (len : Nat)
  | load (b : Breite) (f : AdrForm) (ripNext : Adresse) (dst : Register)
    (len : Nat)
  | pushW (b : Breite) (v : Wort) (len : Nat)
  | popW (b : Breite) (dst : Register) (len : Nat)
  | leaveW (len : Nat)
  | retW (n : BitVec 16)
  | verweigert
  deriving DecidableEq, Repr

/-- Core-data update from a canonical successor: registers, flags and
    RIP move; XMM/FP context is kept. -/
def setKernVonZustandMt (m : HwMaschine) (c : Nat)
    (s' : Zustand) : HwMaschine :=
  setKernDaten m c
    ⟨s'.register, s'.flags, s'.rip, (m.kerne c).xmm, (m.kerne c).fp⟩

/-- Register event: the accepted family step on the acting core's
    projection, lifted back with kept XMM/FP context. -/
def mtAdapterReg (m : HwMaschine) (c : Nat)
    (d : MtDecodiert) : Option HwMaschine :=
  match mtSchritt d (projZustand m c) with
  | some s' => some (setKernVonZustandMt m c s')
  | none => none

/-- A register event preserves well-formedness (profiles untouched). -/
theorem mtAdapterReg_wf (m : HwMaschine) (c : Nat) (d : MtDecodiert)
    (m' : HwMaschine) (h : mtAdapterReg m c d = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold mtAdapterReg setKernVonZustandMt at h
  cases hs : mtSchritt d (projZustand m c) with
  | none => rw [hs] at h; cases h
  | some s' =>
    rw [hs] at h
    cases h
    exact setKernDaten_wf _ _ _ hwf

/-- Pushed core data: the stack pointer drops by the width, RIP
    advances past `len`; XMM/FP context is kept. -/
def mtPushKern (m : HwMaschine) (c : Nat) (b : Breite)
    (len : Nat) : HwKern :=
  ⟨regSet (m.kerne c).register .rsp
    ((m.kerne c).register .rsp - BitVec.ofNat 64 b.bytes),
    (m.kerne c).flags, ripNach (m.kerne c).rip len,
    (m.kerne c).xmm, (m.kerne c).fp⟩

/-- The pushed slot: one width below the top. -/
def mtPushOben (m : HwMaschine) (c : Nat) (b : Breite) : Adresse :=
  (m.kerne c).register .rsp - BitVec.ofNat 64 b.bytes

/-- Buffered push: the word issues into the acting core's buffer at
    the pushed slot, RIP advances past `len`. -/
def mtPushW (m : HwMaschine) (c : Nat) (b : Breite) (v : Wort)
    (len : Nat) : Option HwMaschine :=
  match laengeOk len with
  | false => none
  | true =>
    match concIssue (tsoAnsicht (setKernDaten m c (mtPushKern m c b len)))
        c b (mtPushOben m c b) v with
    | some s' => some (setTso (setKernDaten m c (mtPushKern m c b len)) s')
    | none => none

/-- A buffered push preserves well-formedness. -/
theorem mtPushW_wf (m : HwMaschine) (c : Nat) (b : Breite) (v : Wort)
    (len : Nat) (m' : HwMaschine) (h : mtPushW m c b v len = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold mtPushW at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hi : concIssue (tsoAnsicht (setKernDaten m c (mtPushKern m c b len)))
        c b (mtPushOben m c b) v with
    | none => simp [hi] at h
    | some s' =>
      simp [hi] at h
      cases h
      exact hwf

/-- Popped core data for an observed word: the stack pointer advances
    past the width, the destination merges at the width, RIP advances
    past `len`; flags and XMM/FP context are kept. -/
def mtPopKern (m : HwMaschine) (c : Nat) (b : Breite) (dst : Register)
    (len : Nat) (w : Wort) : HwKern :=
  ⟨regSet (regSet (m.kerne c).register .rsp
    ((m.kerne c).register .rsp + BitVec.ofNat 64 b.bytes)) dst
    (mergeRegNarrow b ((m.kerne c).register dst) w),
    (m.kerne c).flags, ripNach (m.kerne c).rip len,
    (m.kerne c).xmm, (m.kerne c).fp⟩

/-- Forwarded pop: the word at the top is observed with owner-only
    forwarding. -/
def mtPopW (m : HwMaschine) (c : Nat) (b : Breite) (dst : Register)
    (len : Nat) : Option HwMaschine :=
  match laengeOk len with
  | false => none
  | true =>
    match concLoad (tsoAnsicht m) c b ((m.kerne c).register .rsp) with
    | none => none
    | some w => some (setKernDaten m c (mtPopKern m c b dst len w))

/-- A forwarded pop preserves well-formedness (core data only). -/
theorem mtPopW_wf (m : HwMaschine) (c : Nat) (b : Breite) (dst : Register)
    (len : Nat) (m' : HwMaschine) (h : mtPopW m c b dst len = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold mtPopW at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hl : concLoad (tsoAnsicht m) c b ((m.kerne c).register .rsp) with
    | none => simp [hl] at h
    | some w =>
      simp [hl] at h
      cases h
      exact setKernDaten_wf _ _ _ hwf

/-- Left core data for an observed word: the stack pointer takes the
    frame pointer plus a word, the frame pointer takes the word, RIP
    advances past `len`. -/
def mtLeaveKern (m : HwMaschine) (c : Nat) (len : Nat)
    (w : Wort) : HwKern :=
  ⟨regSet (regSet (m.kerne c).register .rsp
    ((m.kerne c).register .rbp + BitVec.ofNat 64 8)) .rbp w,
    (m.kerne c).flags, ripNach (m.kerne c).rip len,
    (m.kerne c).xmm, (m.kerne c).fp⟩

/-- LEAVE: the stack pointer takes the frame pointer, the word there
    is observed into the frame pointer. -/
def mtLeaveW (m : HwMaschine) (c : Nat) (len : Nat) :
    Option HwMaschine :=
  match laengeOk len with
  | false => none
  | true =>
    match concLoad (tsoAnsicht m) c .b64 ((m.kerne c).register .rbp) with
    | none => none
    | some w => some (setKernDaten m c (mtLeaveKern m c len w))

/-- A LEAVE preserves well-formedness (core data only). -/
theorem mtLeaveW_wf (m : HwMaschine) (c : Nat) (len : Nat)
    (m' : HwMaschine) (h : mtLeaveW m c len = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold mtLeaveW at h
  cases hlen : laengeOk len with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hl : concLoad (tsoAnsicht m) c .b64
        ((m.kerne c).register .rbp) with
    | none => simp [hl] at h
    | some w =>
      simp [hl] at h
      cases h
      exact setKernDaten_wf _ _ _ hwf

/-- Returned core data for an observed target: the stack pointer
    advances past the word and the named count, RIP takes the word. -/
def mtRetKern (m : HwMaschine) (c : Nat) (n : BitVec 16)
    (ziel : Wort) : HwKern :=
  ⟨regSet (m.kerne c).register .rsp
    ((m.kerne c).register .rsp + BitVec.ofNat 64 (8 + n.toNat)),
    (m.kerne c).flags, ziel, (m.kerne c).xmm, (m.kerne c).fp⟩

/-- RET with pop count: the word at the top becomes RIP. -/
def mtRetW (m : HwMaschine) (c : Nat) (n : BitVec 16) :
    Option HwMaschine :=
  match concLoad (tsoAnsicht m) c .b64 ((m.kerne c).register .rsp) with
  | none => none
  | some ziel => some (setKernDaten m c (mtRetKern m c n ziel))

/-- A RET preserves well-formedness (core data only). -/
theorem mtRetW_wf (m : HwMaschine) (c : Nat) (n : BitVec 16)
    (m' : HwMaschine) (h : mtRetW m c n = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold mtRetW at h
  cases hl : concLoad (tsoAnsicht m) c .b64
      ((m.kerne c).register .rsp) with
  | none => simp [hl] at h
  | some ziel =>
    simp [hl] at h
    cases h
    exact setKernDaten_wf _ _ _ hwf

/-- The family adapter: one checked event step on the coherent
    machine, reusing the accepted evaluators. All event
    implementations are declared above, so dispatch is exact. -/
def adapterMt : HwAdapter MtEreignis :=
  ⟨fun m c e =>
    match e with
    | .reg d => mtAdapterReg m c d
    | .store b f ripNext src len => hwAddrStore m c b f ripNext src len
    | .load b f ripNext dst len => hwAddrLoad m c b f ripNext dst len
    | .pushW b v len => mtPushW m c b v len
    | .popW b dst len => mtPopW m c b dst len
    | .leaveW len => mtLeaveW m c len
    | .retW n => mtRetW m c n
    | .verweigert => none⟩

/-- An adapter store step is an addressed store step. -/
theorem adapterMt_store (m : HwMaschine) (c : Nat)
    (b : Breite) (f : AdrForm) (ripNext : Adresse) (src : Register)
    (len : Nat) :
    adapterMt.schritt m c (.store b f ripNext src len) =
      hwAddrStore m c b f ripNext src len := rfl

/-- An adapter load step is an addressed load step. -/
theorem adapterMt_load (m : HwMaschine) (c : Nat)
    (b : Breite) (f : AdrForm) (ripNext : Adresse) (dst : Register)
    (len : Nat) :
    adapterMt.schritt m c (.load b f ripNext dst len) =
      hwAddrLoad m c b f ripNext dst len := rfl

/-- The refused event admits nothing. -/
theorem adapterMt_verweigert (m : HwMaschine) (c : Nat) :
    adapterMt.schritt m c .verweigert = none := rfl

/-- Adapter dispatch on each event is the event implementation. -/
theorem adapterMt_reg (m : HwMaschine) (c : Nat) (d : MtDecodiert) :
    adapterMt.schritt m c (.reg d) = mtAdapterReg m c d := rfl

theorem adapterMt_pushW (m : HwMaschine) (c : Nat) (b : Breite)
    (v : Wort) (len : Nat) :
    adapterMt.schritt m c (.pushW b v len) = mtPushW m c b v len := rfl

theorem adapterMt_popW (m : HwMaschine) (c : Nat) (b : Breite)
    (dst : Register) (len : Nat) :
    adapterMt.schritt m c (.popW b dst len) = mtPopW m c b dst len := rfl

theorem adapterMt_leaveW (m : HwMaschine) (c : Nat) (len : Nat) :
    adapterMt.schritt m c (.leaveW len) = mtLeaveW m c len := rfl

theorem adapterMt_retW (m : HwMaschine) (c : Nat) (n : BitVec 16) :
    adapterMt.schritt m c (.retW n) = mtRetW m c n := rfl

/-- Every adapter step preserves well-formedness. -/
theorem adapterMt_wf (m : HwMaschine) (c : Nat) (e : MtEreignis)
    (m' : HwMaschine) (h : adapterMt.schritt m c e = some m')
    (hwf : HwWf m) : HwWf m' := by
  cases e with
  | reg d =>
    rw [adapterMt_reg] at h
    exact mtAdapterReg_wf m c d m' h hwf
  | store b f ripNext src len =>
    rw [adapterMt_store] at h
    exact hwAddrStore_wf m m' c b f ripNext src len h hwf
  | load b f ripNext dst len =>
    rw [adapterMt_load] at h
    exact hwAddrLoad_wf m m' c b f ripNext dst len h hwf
  | pushW b v len =>
    rw [adapterMt_pushW] at h
    exact mtPushW_wf m c b v len m' h hwf
  | popW b dst len =>
    rw [adapterMt_popW] at h
    exact mtPopW_wf m c b dst len m' h hwf
  | leaveW len =>
    rw [adapterMt_leaveW] at h
    exact mtLeaveW_wf m c len m' h hwf
  | retW n =>
    rw [adapterMt_retW] at h
    exact mtRetW_wf m c n m' h hwf
  | verweigert =>
    rw [adapterMt_verweigert] at h
    cases h

/-- Planted refusals: bad lengths refuse on every machine. -/
theorem mtPushW_laenge_verweigert (m : HwMaschine) (c : Nat) (b : Breite)
    (v : Wort) (len : Nat) (h : laengeOk len = false) :
    mtPushW m c b v len = none := by
  unfold mtPushW
  simp [h]

theorem mtPopW_laenge_verweigert (m : HwMaschine) (c : Nat) (b : Breite)
    (dst : Register) (len : Nat) (h : laengeOk len = false) :
    mtPopW m c b dst len = none := by
  unfold mtPopW
  simp [h]

theorem mtLeaveW_laenge_verweigert (m : HwMaschine) (c : Nat)
    (len : Nat) (h : laengeOk len = false) :
    mtLeaveW m c len = none := by
  unfold mtLeaveW
  simp [h]

theorem mtAdapterReg_laenge_verweigert (m : HwMaschine) (c : Nat)
    (f : MtForm) :
    mtAdapterReg m c ⟨f, 0⟩ = none := by
  unfold mtAdapterReg mtSchritt
  rfl

/-! ## 10. Reached witness: a two-core run with a memory-changing
  drain, owner-only forwarding, register MOV and TEST flags.

  Core 0 pushes a word (buffered, RIP advances), pops it back
  through owner-only forwarding, and drains it into shared memory
  (0 becomes the word, both cores observe). Core 1 observes the old
  value before the drain. All claims are closed decidable
  observations projecting to `Wort`/`Byte`/`Nat`, never whole states. -/

/-- Witness value (low byte `0x08`). -/
def mtWitV : Wort := BitVec.ofNat 64 0x0102030405060708

/-- Witness stack top: the pushed slot stays inside the accepted
    data window. -/
def mtWitTop : Adresse := BitVec.ofNat 64 8208

/-- Witness slot: one word below the top. -/
def mtWitSlot : Adresse := BitVec.ofNat 64 8200

/-- Witness core-0 registers: value, stack top, frame. -/
def mtWitReg0 : Register → Wort := fun q =>
  if q = .rax then mtWitV
  else if q = .rsp then mtWitTop
  else if q = .rbp then mtWitTop
  else BitVec.ofNat 64 0

/-- Witness cores: core 0 runs at 4096, core 1 idles on the data page. -/
def mtWitKern : Nat → HwKern
  | 0 => ⟨mtWitReg0, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 8192, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: accepted shared memory, two cores, empty
    buffers, full silicon. -/
def mtWitM0 : HwMaschine :=
  ⟨hwAddrWitMem, mtWitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed: full silicon admits all. -/
theorem mtWitM0_wf : HwWf mtWitM0 := by
  intro c f _
  cases f <;> rfl

/-- The machine after the adapter push of the witness word. -/
def mtWitM1 : Option HwMaschine :=
  adapterMt.schritt mtWitM0 0 (.pushW .b64 mtWitV 1)

/-- The machine after popping the word into `rbx` through forwarding. -/
def mtWitM2 : Option HwMaschine :=
  mtWitM1.bind (fun m => adapterMt.schritt m 0 (.popW .b64 .rbx 1))

/-- The shared TSO state after the push issue. -/
def mtWitT1 : Option TSOZustand := mtWitM1.map tsoAnsicht

/-- The push buffers exactly eight entries on core 0. -/
theorem mtWit_puffer8 :
    mtWitM1.map (fun m => (m.puffer 0).length) = some 8 := by
  decide

/-- The push drops the stack pointer to the slot. -/
theorem mtWit_rsp_slot :
    mtWitM1.map (fun m => (m.kerne 0).register .rsp) =
      some mtWitSlot := by
  decide

/-- The push advances RIP past its length. -/
theorem mtWit_rip_weitet :
    mtWitM1.map (fun m => (m.kerne 0).rip) =
      some (BitVec.ofNat 64 4097) := by
  decide

/-- The push leaves the shared slot byte at zero (buffer only). -/
theorem mtWit_mem_still :
    mtWitT1.map (fun s => s.mem.bytes mtWitSlot) =
      some (BitVec.ofNat 8 0) := by
  decide

/-- The forwarded pop observes the pushed word in `rbx`. -/
theorem mtWit_pop_wert :
    mtWitM2.map (fun m => (m.kerne 0).register .rbx) =
      some mtWitV := by
  decide

/-- The pop restores the stack pointer to the top. -/
theorem mtWit_pop_rsp :
    mtWitM2.map (fun m => (m.kerne 0).register .rsp) =
      some mtWitTop := by
  decide

/-- Core 0 drains its eight entries, one flush per state. -/
def mtWitF1 : Option TSOZustand :=
  mtWitT1.bind (fun s => flushKern s 0)

def mtWitF2 : Option TSOZustand :=
  mtWitF1.bind (fun s => flushKern s 0)

def mtWitF3 : Option TSOZustand :=
  mtWitF2.bind (fun s => flushKern s 0)

def mtWitF4 : Option TSOZustand :=
  mtWitF3.bind (fun s => flushKern s 0)

def mtWitF5 : Option TSOZustand :=
  mtWitF4.bind (fun s => flushKern s 0)

def mtWitF6 : Option TSOZustand :=
  mtWitF5.bind (fun s => flushKern s 0)

def mtWitF7 : Option TSOZustand :=
  mtWitF6.bind (fun s => flushKern s 0)

def mtWitF8 : Option TSOZustand :=
  mtWitF7.bind (fun s => flushKern s 0)

/-- Forwarding: core 0 reads its own unflushed word. -/
theorem mtWit_weiterleitung :
    mtWitT1.map (fun s => concLoad s 0 .b64 mtWitSlot) =
      some (some mtWitV) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem mtWit_fremd_alt :
    mtWitT1.map (fun s => concLoad s 1 .b64 mtWitSlot) =
      some (some (BitVec.ofNat 64 0)) := by
  decide

/-- The drain changes shared memory: the slot reads `0x08`. -/
theorem mtWit_spuelung :
    mtWitF8.map (fun s => s.mem.bytes mtWitSlot) =
      some (BitVec.ofNat 8 8) := by
  decide

/-- After the drain core 1 observes the new word. -/
theorem mtWit_fremd_neu :
    mtWitF8.map (fun s => concLoad s 1 .b64 mtWitSlot) =
      some (some mtWitV) := by
  decide

/-- Closed memory round trip: store through `[rbp + 5]`. -/
theorem roundtrip_mt_movRM_mem :
    (encodeMt (.movRM .b32 fMT .rax)).bind
      (fun bs => decodeMovTest bs) =
      some ((⟨.movRM .b32 fMT .rax, 3⟩, [])) := by
  decide

/-- Closed memory round trip: load through `[rbp + 5]`. -/
theorem roundtrip_mt_movMR_mem :
    (encodeMt (.movMR .b32 .rax fMT)).bind
      (fun bs => decodeMovTest bs) =
      some ((⟨.movMR .b32 .rax fMT, 3⟩, [])) := by
  decide

/-- Closed memory round trip: bare LEA through `[rbp + 5]`. -/
theorem roundtrip_mt_leaBare_mem :
    (encodeMt (.leaBare .rax fMT)).bind
      (fun bs => decodeMovTest bs) =
      some ((⟨.leaBare .rax fMT, 3⟩, [])) := by
  decide

/-- The witness MOV writes the zero-extended low half to `rcx`. -/
theorem mtWit_mov_wert :
    (mtSchritt ⟨.movRR .b32 .rcx .rax, 3⟩
      (projZustand mtWitM0 0)).map (fun s => s.register .rcx) =
      some (BitVec.ofNat 64 0x05060708) := by
  decide

/-- The witness TEST of zero sets ZF on the idle core. -/
theorem mtWit_test_zf :
    (mtSchritt ⟨.testRR .b64 .rax .rax, 3⟩
      (projZustand mtWitM0 1)).map (fun s => s.flags.zf) =
      some true := by
  decide

/-- The adapter register event moves the MOV into core data. -/
theorem mtWit_adapter_reg :
    (adapterMt.schritt mtWitM0 0
      (.reg ⟨.movRR .b32 .rcx .rax, 3⟩)).map
      (fun m => (m.kerne 0).register .rcx) =
      some (BitVec.ofNat 64 0x05060708) := by
  decide

/-- JOINT WITNESS: well-formedness, buffered push with stack-pointer
    drop and RIP advance, memory still at zero, forwarded pop with
    stack-pointer restore, owner-only forwarding, observable drain
    (0 becomes `0x08`, both cores observe), register MOV value, TEST
    zero flag, adapter register lift, beside the planted refusal. The
    run is reached (push then pop through the adapter, eight
    drain flushes) and non-degenerate (two cores, memory change). -/
theorem mt_zeuge :
    HwWf mtWitM0 ∧
    mtWitM1.map (fun m => (m.puffer 0).length) = some 8 ∧
    mtWitM1.map (fun m => (m.kerne 0).register .rsp) =
      some mtWitSlot ∧
    mtWitM1.map (fun m => (m.kerne 0).rip) =
      some (BitVec.ofNat 64 4097) ∧
    mtWitT1.map (fun s => s.mem.bytes mtWitSlot) =
      some (BitVec.ofNat 8 0) ∧
    mtWitM2.map (fun m => (m.kerne 0).register .rbx) =
      some mtWitV ∧
    mtWitM2.map (fun m => (m.kerne 0).register .rsp) =
      some mtWitTop ∧
    mtWitT1.map (fun s => concLoad s 0 .b64 mtWitSlot) =
      some (some mtWitV) ∧
    mtWitT1.map (fun s => concLoad s 1 .b64 mtWitSlot) =
      some (some (BitVec.ofNat 64 0)) ∧
    mtWitF8.map (fun s => s.mem.bytes mtWitSlot) =
      some (BitVec.ofNat 8 8) ∧
    mtWitF8.map (fun s => concLoad s 1 .b64 mtWitSlot) =
      some (some mtWitV) ∧
    (mtSchritt ⟨.movRR .b32 .rcx .rax, 3⟩
      (projZustand mtWitM0 0)).map (fun s => s.register .rcx) =
      some (BitVec.ofNat 64 0x05060708) ∧
    (mtSchritt ⟨.testRR .b64 .rax .rax, 3⟩
      (projZustand mtWitM0 1)).map (fun s => s.flags.zf) =
      some true ∧
    (adapterMt.schritt mtWitM0 0
      (.reg ⟨.movRR .b32 .rcx .rax, 3⟩)).map
      (fun m => (m.kerne 0).register .rcx) =
      some (BitVec.ofNat 64 0x05060708) ∧
    adapterMt.schritt mtWitM0 0 .verweigert = none := by
  exact ⟨mtWitM0_wf, mtWit_puffer8, mtWit_rsp_slot, mtWit_rip_weitet,
    mtWit_mem_still, mtWit_pop_wert, mtWit_pop_rsp, mtWit_weiterleitung,
    mtWit_fremd_alt, mtWit_spuelung, mtWit_fremd_neu, mtWit_mov_wert,
    mtWit_test_zf, mtWit_adapter_reg, adapterMt_verweigert _ _⟩

/- CUTS:
   Proved here, layering over (never editing) the accepted producers:
   - Family decoder `decodeMovTest` with ownership verdicts against
     `kapDecode`: bare/66/REX MOV 88/8A/8B (modrm), B0-B7, 66-B8,
  A8/A9 (REX.W A9 included), C6/C7 digit 0 (minus REX.W C7-reg),
      F6/F7 digits 0 and 1, 84/bare-85/66-85, bare 8D, 0F 1F NOP (bare/66),
     ENDBR64, 8F /0, FF /6, LEAVE, RET imm16, INT3, UD2.
     Rows owned elsewhere refuse here and stay with their owners:
     REX.W 85-reg (decodeCore/decodeIntHw), 90+r/86/87 (decodeSx),
     REX.W B8-imm64 and REX.W 89-reg (pilot), bare/REX B8-imm32 and
     REX.W C7-reg (decodeC), REX.W 89/8B memory (accepted memory
     rows), REX 89 mod 2/3 (decodeNarrow).
   - Canonical encoder `encodeMt` with befehl round trips (general,
     suffix-threaded, for the finite rows; closed instances for
     memory rows over `fMT`, including bare LEA).
   - Register semantics `mtSchritt` reusing `mergeRegNarrow`
     (8/16-merge, 32-zero-extend), `andW` (AF free), `adrEff`
     (truncated for bare LEA), `schrittRegister`; agreement with
     `moveNarrow`, the AND flag snapshot, frame preservation.
   - Extended chain `kapDecodeMitMt` (old chain first): exact
     agreement, take-where-refused, joint refusal.
   - Adapter `adapterMt` over `MtEreignis`: register lift,
     exact store/load delegation to `hwAddrStore`/`hwAddrLoad`,
     buffered push/pop/leave/return through `concIssue`/`concLoad`,
     `HwWf` preservation of every step, planted length refusals
     and the refused event. INT3/UD2 decode but admit no event.
   - Reached two-core witness `mt_zeuge`: push/pop through the
     adapter, eight-flush drain changing memory 0 to `0x08`,
     owner-only forwarding, MOV value, TEST zero flag.
   NOT proved here, and not claimed:
   - No silicon correspondence: encodings and width discipline
     follow the accepted canonical subsets with self-consistency
     only; Intel SDM extracts are provenance, not proofs.
   - No general memory round trip (needs a
     parseAdrTail∘encodeAdr inversion lemma); no per-access
     target-to-W/GX simulation; no LOCK/RMW path; no interrupts;
     no source/ABI/loader/entry/budget claim.
   - A maintainer wires the family rows into `kapDecode`
     (HwKapsteinDecoder.lean) behind its last arm; the extended
     chain above states the contract.
-/

#print axioms roundtrip_mt_movRR
#print axioms roundtrip_mt_testRR
#print axioms roundtrip_mt_nopReg
#print axioms roundtrip_mt_pushR
#print axioms roundtrip_mt_popR
#print axioms roundtrip_mt_endbr64
#print axioms roundtrip_mt_leave
#print axioms roundtrip_mt_int3
#print axioms roundtrip_mt_ud2
#print axioms roundtrip_mt_movRM_mem
#print axioms roundtrip_mt_movMR_mem
#print axioms roundtrip_mt_leaBare_mem
#print axioms mtSchritt_movRR_ist_moveNarrow
#print axioms mtSchritt_testRR_flags
#print axioms mtSchritt_movRR_rahmen
#print axioms kapDecodeMitMt_kap
#print axioms kapDecodeMitMt_mt
#print axioms kapDecodeMitMt_nichts
#print axioms adapterMt_store
#print axioms adapterMt_load
#print axioms adapterMt_verweigert
#print axioms adapterMt_reg
#print axioms adapterMt_pushW
#print axioms adapterMt_popW
#print axioms adapterMt_leaveW
#print axioms adapterMt_retW
#print axioms adapterMt_wf
#print axioms mtAdapterReg_wf
#print axioms mtPushW_wf
#print axioms mtPopW_wf
#print axioms mtLeaveW_wf
#print axioms mtRetW_wf
#print axioms mtWitM0_wf
#print axioms mtWit_puffer8
#print axioms mtWit_weiterleitung
#print axioms mtWit_fremd_alt
#print axioms mtWit_spuelung
#print axioms mtWit_fremd_neu
#print axioms mtWit_mov_wert
#print axioms mtWit_test_zf
#print axioms mtWit_adapter_reg
#print axioms mt_zeuge

end Gabbro.Grammatik.X86
