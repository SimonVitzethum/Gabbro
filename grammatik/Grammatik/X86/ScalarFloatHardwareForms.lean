/-
  File:      Grammatik/X86/ScalarFloatHardwareForms.lean
  Subject:   REX-aware canonical SSE2 binary64 byte rows over the accepted
    scalar evaluator.

  Lane 668 (hardware completion): SUBSD/MULSD/DIVSD/UCOMISD/CVTSI2SD/
  CVTTSD2SI/MOVSD register and memory forms with full xmm0-15 and
  r8-r15 reachability, reusing accepted `ScalarFloat.fpSchritt` and the
  IEEE kernel (`Gleitprofil`, `FloatExceptions`). No new evaluator and
  no new IEEE arithmetic: every execution fact is a `fpSchritt` equation
  or a kernel witness. Official provenance is the local snapshot
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`
  (Intel SDM 325462-093US, September 2026): ADDSD F2 0F 58 /r and
  SUBSD F2 0F 5C /r (Vol.2B 4-692f), MULSD F2 0F 59 /r (Vol.2B 4-147),
  DIVSD F2 0F 5E /r (Vol.2A 3-273), UCOMISD 66 0F 2E /r with the
  UNORDERED/GREATER/LESS/EQUAL flag table and OF/AF/SF := 0
  (Vol.2B 4-733f), CVTSI2SD F2 0F 2A /r (r32/m32) and F2 REX.W 0F 2A /r
  (r/m64) with DEST[63:0] := convert and DEST[MAXVL-1:64] unchanged
  (Vol.2A 3-236), CVTTSD2SI F2 0F 2C /r (r32) and F2 REX.W 0F 2C /r
  (r64) with truncation and the masked indefinite values 80000000H /
  80000000_00000000H (Vol.2A 3-253), MOVSD F2 0F 10 /r and F2 0F 11 /r
  with legacy DEST[63:0] := SRC and DEST[MAXVL-1:64] unmodified on the
  register form and DEST[127:64] := 0 on the load form (Vol.2B 4-104f,
  App.B Table B-26), REX Table 2-4 BITS 0100WRXB with the mandatory
  prefix BEFORE REX (Vol.2A 2-7f, CVTDQ2PD example), and the masked
  invalid/divide responses (Vol.1 App.D Tables D-1/D-13).
-/
import Grammatik.X86.ScalarFloat
import Grammatik.X86.ScalarFloatCodec
import Grammatik.X86.VectorCodec
import Grammatik.X86.FloatExceptions
import Grammatik.X86.FloatEntryState
import Grammatik.X86.FloatSourceObservations

namespace Gabbro.Grammatik.X86

/-- Canonical REX byte: 0100WRXB with X = 0 (no SIB index anywhere in
    this subset; a set X bit refuses, it has no `effAddr` execution). -/
def fpHwRex (w r b : Nat) : Byte := natByte (64 + w * 8 + r * 4 + b)

/-! ## 1. Canonical REX-aware byte encodings (stated from the SDM pages).

  Byte order is mandatory-prefix, REX, 0F escape, opcode, ModRM
  (Vol.2A 2-7f: the mandatory prefix comes BEFORE REX so REX
  immediately precedes the escape byte; CVTDQ2PD example). Opcodes:
  ADDSD F2 0F 58, SUBSD F2 0F 5C, MULSD F2 0F 59, DIVSD F2 0F 5E,
  UCOMISD 66 0F 2E, CVTSI2SD F2 0F 2A (REX.W = 1 for the r/m64 form),
  CVTTSD2SI F2 0F 2C (REX.W = 1 for the r64 form), MOVSD F2 0F 10
  (load and register copy) / F2 0F 11 (store). ModRM mod = 11 is
  register-direct (reg = destination, r/m = source, except CVTTSD2SI
  where reg = GPR destination and r/m = XMM source); mod = 10 is
  base-plus-disp32 with the pilot SIB rule (SIB 36 iff the low base
  code is 4). Conversions admit register sources only (see §2). -/

/-- Arithmetic opcode byte per model op. -/
def fpHwArithOpcode : Gabbro.Grammatik.GleitOp → Nat
  | .add => 88 | .sub => 92 | .mul => 89 | .div => 94

/-- Canonical REX for XMM-destination forms with an XMM r/m source. -/
def fpHwRexXX (dst src : XmmReg) : Byte :=
  fpHwRex 0 (xmmHigh dst) (xmmHigh src)

/-- Canonical REX for XMM-destination forms with a GPR base. -/
def fpHwRexXB (dst : XmmReg) (base : Register) : Byte :=
  fpHwRex 0 (xmmHigh dst) (regHigh base)

/-- Canonical arithmetic register bytes: F2 REX 0F op /r, mod = 11. -/
def fpHwEncodeArithRR (op : Gabbro.Grammatik.GleitOp)
    (dst src : XmmReg) : List Byte :=
  [natByte 242, fpHwRexXX dst src, natByte 15,
    natByte (fpHwArithOpcode op), modrmReg (xmmLow dst) (xmmLow src)]

/-- Canonical arithmetic memory bytes: F2 REX 0F op /r, mod = 10. -/
def fpHwEncodeArithRM (op : Gabbro.Grammatik.GleitOp)
    (dst : XmmReg) (base : Register) (d : BitVec 32) : List Byte :=
  let head := [natByte 242, fpHwRexXB dst base, natByte 15,
    natByte (fpHwArithOpcode op), modrmMem (xmmLow dst) (regLow base)]
  if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
  else head ++ leBytes32 d

/-- Canonical UCOMISD register bytes: 66 REX 0F 2E /r, mod = 11. -/
def fpHwEncodeUcomiRR (lhs rhs : XmmReg) : List Byte :=
  [natByte 102, fpHwRexXX lhs rhs, natByte 15, natByte 46,
    modrmReg (xmmLow lhs) (xmmLow rhs)]

/-- Canonical UCOMISD memory bytes: 66 REX 0F 2E /r, mod = 10. -/
def fpHwEncodeUcomiRM (lhs : XmmReg) (base : Register)
    (d : BitVec 32) : List Byte :=
  let head := [natByte 102, fpHwRexXB lhs base, natByte 15, natByte 46,
    modrmMem (xmmLow lhs) (regLow base)]
  if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
  else head ++ leBytes32 d

/-- Canonical CVTSI2SD register bytes: F2 REX.W 0F 2A /r, mod = 11.
    REX.W = 1 is REQUIRED: it selects the r64 source the accepted
    `cvtsi2sd` converts whole (Vol.2A 3-236); the W = 0 doubleword
    form is refused in §2. -/
def fpHwEncodeCvtsi (dst : XmmReg) (src : Register) : List Byte :=
  [natByte 242, fpHwRex 1 (xmmHigh dst) (regHigh src), natByte 15,
    natByte 42, modrmReg (xmmLow dst) (regLow src)]

/-- Canonical CVTTSD2SI register bytes: F2 REX.W 0F 2C /r, mod = 11.
    REX.W = 1 is REQUIRED: it selects the r64 destination the accepted
    `cvttsd2si` writes whole (Vol.2A 3-253); the W = 0 form is refused
    in §2. The GPR destination rides the reg field (REX.R), the XMM
    source the r/m field (REX.B). -/
def fpHwEncodeCvtt (dst : Register) (src : XmmReg) : List Byte :=
  [natByte 242, fpHwRex 1 (regHigh dst) (xmmHigh src), natByte 15,
    natByte 44, modrmReg (regLow dst) (xmmLow src)]

/-- Canonical MOVSD register-copy bytes: F2 REX 0F 10 /r, mod = 11. -/
def fpHwEncodeMovsdRR (dst src : XmmReg) : List Byte :=
  [natByte 242, fpHwRexXX dst src, natByte 15, natByte 16,
    modrmReg (xmmLow dst) (xmmLow src)]

/-- Canonical MOVSD load bytes: F2 REX 0F 10 /r, mod = 10. -/
def fpHwEncodeMovsdLade (dst : XmmReg) (base : Register)
    (d : BitVec 32) : List Byte :=
  let head := [natByte 242, fpHwRexXB dst base, natByte 15, natByte 16,
    modrmMem (xmmLow dst) (regLow base)]
  if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
  else head ++ leBytes32 d

/-- Canonical MOVSD store bytes: F2 REX 0F 11 /r, mod = 10. -/
def fpHwEncodeMovsdSpeichere (base : Register) (src : XmmReg)
    (d : BitVec 32) : List Byte :=
  let head := [natByte 242, fpHwRex 0 (xmmHigh src) (regHigh base),
    natByte 15, natByte 17, modrmMem (xmmLow src) (regLow base)]
  if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
  else head ++ leBytes32 d

/-- Every canonical REX register encoding is 5 bytes long. -/
theorem fpHwLen_rr (op : Gabbro.Grammatik.GleitOp) (dst src : XmmReg) :
    (fpHwEncodeArithRR op dst src).length = 5 := by
  cases op <;> rfl

/-- UCOMISD register encodings are 5 bytes long. -/
theorem fpHwLen_ucomiRR (lhs rhs : XmmReg) :
    (fpHwEncodeUcomiRR lhs rhs).length = 5 := rfl

/-- Conversion register encodings are 5 bytes long. -/
theorem fpHwLen_cvtsi (dst : XmmReg) (src : Register) :
    (fpHwEncodeCvtsi dst src).length = 5 := rfl

/-- Conversion register encodings are 5 bytes long. -/
theorem fpHwLen_cvtt (dst : Register) (src : XmmReg) :
    (fpHwEncodeCvtt dst src).length = 5 := rfl

/-- MOVSD register encodings are 5 bytes long. -/
theorem fpHwLen_movsdRR (dst src : XmmReg) :
    (fpHwEncodeMovsdRR dst src).length = 5 := rfl

/-- The 5-byte length passes the decode-length guard. -/
theorem fpHwLen5_ok (n : Nat) (h : n = 5) : laengeOk n = true := by
  rw [h]; decide

/-! ## 2. Independent REX decoder over actual bytes.

  The decoder reads mandatory prefix, REX, escape, opcode, ModRM and
  displacement from the byte list itself. A caller-supplied
  `FpDecodiert` never becomes fetched evidence. Only the §1 forms
  decode; a set REX.X bit, a conversion with the wrong REX.W, a
  memory-source conversion (no `FpBefehl` constructor exists for it),
  a register-form store, COMISD (NP 0F 2F), any other opcode or ModRM
  mode, and every truncation refuse with `none`. -/

/-- Opcode byte back to the model op (F2 arithmetic space only). -/
def fpHwArithVonOpcode : Nat → Option Gabbro.Grammatik.GleitOp
  | 88 => some .add | 92 => some .sub | 89 => some .mul | 94 => some .div
  | _ => none

/-- Opcode byte to the register arithmetic form. -/
def fpHwArithRR : Gabbro.Grammatik.GleitOp → XmmReg → XmmReg → FpBefehl
  | .add, dst, src => .addsdRR dst src
  | .sub, dst, src => .subsdRR dst src
  | .mul, dst, src => .mulsdRR dst src
  | .div, dst, src => .divsdRR dst src

/-- Opcode byte to the memory arithmetic form. -/
def fpHwArithRM : Gabbro.Grammatik.GleitOp → XmmReg → Register →
    BitVec 32 → FpBefehl
  | .add, dst, base, d => .addsdRM dst base d
  | .sub, dst, base, d => .subsdRM dst base d
  | .mul, dst, base, d => .mulsdRM dst base d
  | .div, dst, base, d => .divsdRM dst base d

/-- Register-direct row (ModRM mod = 11) after prefix/REX/escape/opcode.
    `reg`/`rm` are the raw 3-bit fields; REX.R/REX.B extend them to the
    full 4-bit code before the inverse check. -/
def fpHwDecodeReg (isF2 : Bool) (wBit rBit bBit op reg rm : Nat)
    (rest : List Byte) : Option (FpDecodiert × List Byte) :=
  match fpHwArithVonOpcode op with
  | some g =>
    match isF2, wBit, codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
    | true, 0, some dst, some src => some (⟨fpHwArithRR g dst src, 5⟩, rest)
    | _, _, _, _ => none
  | none =>
    match isF2, op, wBit with
    | true, 16, 0 =>
      match codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
      | some dst, some src => some (⟨.movsdRR dst src, 5⟩, rest)
      | _, _ => none
    | false, 46, 0 =>
      match codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
      | some lhs, some rhs => some (⟨.ucomisdRR lhs rhs, 5⟩, rest)
      | _, _ => none
    | true, 42, 1 =>
      match codeXmm (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
      | some dst, some src => some (⟨.cvtsi2sd dst src, 5⟩, rest)
      | _, _ => none
    | true, 44, 1 =>
      match codeReg (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
      | some dst, some src => some (⟨.cvttsd2si dst src, 5⟩, rest)
      | _, _ => none
    | _, _, _ => none

/-- Memory row (ModRM mod = 10) with resolved base, displacement and
    consumed length. Conversions have no memory row: the accepted
    executor converts register sources only, so those bytes refuse. -/
def fpHwDecodeMemForm (isF2 : Bool) (wBit dstCode : Nat)
    (base : Register) (d : BitVec 32) (len op : Nat)
    (rest : List Byte) : Option (FpDecodiert × List Byte) :=
  match fpHwArithVonOpcode op with
  | some g =>
    match isF2, wBit, codeXmm dstCode with
    | true, 0, some dst => some (⟨fpHwArithRM g dst base d, len⟩, rest)
    | _, _, _ => none
  | none =>
    match isF2, op, wBit with
    | true, 16, 0 =>
      match codeXmm dstCode with
      | some dst => some (⟨.movsdLade dst base d, len⟩, rest)
      | none => none
    | true, 17, 0 =>
      match codeXmm dstCode with
      | some src => some (⟨.movsdSpeichere base src d, len⟩, rest)
      | none => none
    | false, 46, 0 =>
      match codeXmm dstCode with
      | some lhs => some (⟨.ucomisdRM lhs base d, len⟩, rest)
      | none => none
    | _, _, _ => none

/-- Decode ModRM and the optional disp32 after prefix/REX/escape/opcode.
    Length 5 for register forms, 9/10 for memory forms; truncated
    inputs refuse. -/
def fpHwDecodeRest (isF2 : Bool) (wBit rBit bBit op : Nat) :
    List Byte → Option (FpDecodiert × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    match byteNat m / 64 with
    | 3 => fpHwDecodeReg isF2 wBit rBit bBit op reg rm rest
    | 2 =>
      if rm == 4 then
        match rest with
        | [] => none
        | sib :: rest2 =>
          if byteNat sib == 36 then
            match parseLe32 rest2, codeReg (bBit * 8 + 4) with
            | some (d, rest3), some base =>
              fpHwDecodeMemForm isF2 wBit (rBit * 8 + reg) base d 10 op rest3
            | _, _ => none
          else none
      else
        match parseLe32 rest, codeReg (bBit * 8 + rm) with
        | some (d, rest3), some base =>
          fpHwDecodeMemForm isF2 wBit (rBit * 8 + reg) base d 9 op rest3
        | _, _ => none
    | _ => none

/-- REX extension bits from a canonical REX byte value: W, R, B.
    Only X = 0 values are admitted (64, 65, 68, 69 with W = 0 and
    72, 73, 76, 77 with W = 1); every other byte -- including the
    X = 1 values, which would address through a SIB index the accepted
    `effAddr` cannot execute -- refuses with `none`. -/
def fpHwRexBits : Nat → Option (Nat × Nat × Nat)
  | 64 => some (0, 0, 0)
  | 65 => some (0, 0, 1)
  | 68 => some (0, 1, 0)
  | 69 => some (0, 1, 1)
  | 72 => some (1, 0, 0)
  | 73 => some (1, 0, 1)
  | 76 => some (1, 1, 0)
  | 77 => some (1, 1, 1)
  | _ => none

/-- After prefix and REX: the 0F escape, opcode, then ModRM. -/
def fpHwNach0F (isF2 : Bool) (wBit rBit bBit : Nat) :
    List Byte → Option (FpDecodiert × List Byte)
  | e :: op :: rest2 =>
    if byteNat e == 15 then
      fpHwDecodeRest isF2 wBit rBit bBit (byteNat op) rest2
    else none
  | _ => none

/-- Top-level REX decoder: mandatory prefix (F2 or 66), then a
    canonical REX byte, then 0F escape, opcode, ModRM. A REX byte
    BEFORE the mandatory prefix refuses (Vol.2A 2-7f: prefix-first
    order is canonical); only prefix-first order decodes. -/
def fpHwDecode : List Byte → Option (FpDecodiert × List Byte)
  | p :: r :: rest =>
    match byteNat p with
    | 242 =>
      match fpHwRexBits (byteNat r) with
      | some (w, rB, bB) => fpHwNach0F true w rB bB rest
      | none => none
    | 102 =>
      match fpHwRexBits (byteNat r) with
      | some (w, rB, bB) => fpHwNach0F false w rB bB rest
      | none => none
    | _ => none
  | _ => none

/-! ## 3. Encode/decode round trips over the full register file.

  Decoding inverts encoding on ALL sixteen XMM registers and all
  sixteen GPRs over any suffix; the decoded length is the consumed
  prefix length. No `< 8` side condition remains: REX.R/REX.B carry
  the high bit through `codeXmm`/`codeReg`. -/

/-- Encode/decode round trip for arithmetic register forms. -/
theorem fpHwRoundtrip_arithRR (op : Gabbro.Grammatik.GleitOp)
    (dst src : XmmReg) (suffix : List Byte) :
    fpHwDecode (fpHwEncodeArithRR op dst src ++ suffix) =
      some (⟨fpHwArithRR op dst src, (fpHwEncodeArithRR op dst src).length⟩,
        suffix) := by
  cases op <;> cases dst <;> cases src <;> rfl

/-- Encode/decode round trip for UCOMISD register form. -/
theorem fpHwRoundtrip_ucomiRR (lhs rhs : XmmReg) (suffix : List Byte) :
    fpHwDecode (fpHwEncodeUcomiRR lhs rhs ++ suffix) =
      some (⟨.ucomisdRR lhs rhs, (fpHwEncodeUcomiRR lhs rhs).length⟩,
        suffix) := by
  cases lhs <;> cases rhs <;> rfl

/-- Encode/decode round trip for CVTSI2SD (REX.W = 1) register form. -/
theorem fpHwRoundtrip_cvtsi (dst : XmmReg) (src : Register)
    (suffix : List Byte) :
    fpHwDecode (fpHwEncodeCvtsi dst src ++ suffix) =
      some (⟨.cvtsi2sd dst src, (fpHwEncodeCvtsi dst src).length⟩,
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Encode/decode round trip for CVTTSD2SI (REX.W = 1) register form. -/
theorem fpHwRoundtrip_cvtt (dst : Register) (src : XmmReg)
    (suffix : List Byte) :
    fpHwDecode (fpHwEncodeCvtt dst src ++ suffix) =
      some (⟨.cvttsd2si dst src, (fpHwEncodeCvtt dst src).length⟩,
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Encode/decode round trip for the MOVSD register copy. -/
theorem fpHwRoundtrip_movsdRR (dst src : XmmReg) (suffix : List Byte) :
    fpHwDecode (fpHwEncodeMovsdRR dst src ++ suffix) =
      some (⟨.movsdRR dst src, (fpHwEncodeMovsdRR dst src).length⟩,
        suffix) := by
  cases dst <;> cases src <;> rfl

set_option maxHeartbeats 4000000 in
/-- Encode/decode round trip for ADDSD memory form, both SIB shapes. -/
theorem fpHwRoundtrip_addsdRM (dst : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    fpHwDecode (fpHwEncodeArithRM .add dst base d ++ suffix) =
      some (⟨.addsdRM dst base d,
        (fpHwEncodeArithRM .add dst base d).length⟩, suffix) := by
  cases dst <;> cases base <;>
    simp [fpHwEncodeArithRM, fpHwDecode, fpHwNach0F, fpHwDecodeRest,
      fpHwRexXB, fpHwRexXX, fpHwArithOpcode,
      fpHwDecodeMemForm, fpHwArithVonOpcode, fpHwArithRM,
      codeXmm, xmmCode, xmmHigh, xmmLow, codeReg, regCode, regHigh, regLow,
      fpHwRex, fpHwRexBits, modrmMem, leBytes32, parseLe32_cons]

set_option maxHeartbeats 4000000 in
/-- Encode/decode round trip for SUBSD memory form, both SIB shapes. -/
theorem fpHwRoundtrip_subsdRM (dst : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    fpHwDecode (fpHwEncodeArithRM .sub dst base d ++ suffix) =
      some (⟨.subsdRM dst base d,
        (fpHwEncodeArithRM .sub dst base d).length⟩, suffix) := by
  cases dst <;> cases base <;>
    simp [fpHwEncodeArithRM, fpHwDecode, fpHwNach0F, fpHwDecodeRest,
      fpHwRexXB, fpHwRexXX, fpHwArithOpcode,
      fpHwDecodeMemForm, fpHwArithVonOpcode, fpHwArithRM,
      codeXmm, xmmCode, xmmHigh, xmmLow, codeReg, regCode, regHigh, regLow,
      fpHwRex, fpHwRexBits, modrmMem, leBytes32, parseLe32_cons]

set_option maxHeartbeats 4000000 in
/-- Encode/decode round trip for MULSD memory form, both SIB shapes. -/
theorem fpHwRoundtrip_mulsdRM (dst : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    fpHwDecode (fpHwEncodeArithRM .mul dst base d ++ suffix) =
      some (⟨.mulsdRM dst base d,
        (fpHwEncodeArithRM .mul dst base d).length⟩, suffix) := by
  cases dst <;> cases base <;>
    simp [fpHwEncodeArithRM, fpHwDecode, fpHwNach0F, fpHwDecodeRest,
      fpHwRexXB, fpHwRexXX, fpHwArithOpcode,
      fpHwDecodeMemForm, fpHwArithVonOpcode, fpHwArithRM,
      codeXmm, xmmCode, xmmHigh, xmmLow, codeReg, regCode, regHigh, regLow,
      fpHwRex, fpHwRexBits, modrmMem, leBytes32, parseLe32_cons]

set_option maxHeartbeats 4000000 in
/-- Encode/decode round trip for DIVSD memory form, both SIB shapes. -/
theorem fpHwRoundtrip_divsdRM (dst : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    fpHwDecode (fpHwEncodeArithRM .div dst base d ++ suffix) =
      some (⟨.divsdRM dst base d,
        (fpHwEncodeArithRM .div dst base d).length⟩, suffix) := by
  cases dst <;> cases base <;>
    simp [fpHwEncodeArithRM, fpHwDecode, fpHwNach0F, fpHwDecodeRest,
      fpHwRexXB, fpHwRexXX, fpHwArithOpcode,
      fpHwDecodeMemForm, fpHwArithVonOpcode, fpHwArithRM,
      codeXmm, xmmCode, xmmHigh, xmmLow, codeReg, regCode, regHigh, regLow,
      fpHwRex, fpHwRexBits, modrmMem, leBytes32, parseLe32_cons]

set_option maxHeartbeats 4000000 in
/-- Encode/decode round trip for UCOMISD memory form. -/
theorem fpHwRoundtrip_ucomiRM (lhs : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    fpHwDecode (fpHwEncodeUcomiRM lhs base d ++ suffix) =
      some (⟨.ucomisdRM lhs base d,
        (fpHwEncodeUcomiRM lhs base d).length⟩, suffix) := by
  cases lhs <;> cases base <;>
    simp [fpHwEncodeUcomiRM, fpHwDecode, fpHwNach0F, fpHwDecodeRest,
      fpHwRexXB, fpHwRexXX,
      fpHwDecodeMemForm, fpHwDecodeReg, fpHwArithVonOpcode,
      codeXmm, xmmCode, xmmHigh, xmmLow, codeReg, regCode, regHigh, regLow,
      fpHwRex, fpHwRexBits, modrmMem, leBytes32, parseLe32_cons]

set_option maxHeartbeats 4000000 in
/-- Encode/decode round trip for the MOVSD load, both SIB shapes. -/
theorem fpHwRoundtrip_movsdLade (dst : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    fpHwDecode (fpHwEncodeMovsdLade dst base d ++ suffix) =
      some (⟨.movsdLade dst base d,
        (fpHwEncodeMovsdLade dst base d).length⟩, suffix) := by
  cases dst <;> cases base <;>
    simp [fpHwEncodeMovsdLade, fpHwDecode, fpHwNach0F, fpHwDecodeRest,
      fpHwRexXB, fpHwRexXX,
      fpHwDecodeMemForm, fpHwDecodeReg, fpHwArithVonOpcode,
      codeXmm, xmmCode, xmmHigh, xmmLow, codeReg, regCode, regHigh, regLow,
      fpHwRex, fpHwRexBits, modrmMem, leBytes32, parseLe32_cons]

set_option maxHeartbeats 4000000 in
/-- Encode/decode round trip for the MOVSD store, both SIB shapes. -/
theorem fpHwRoundtrip_movsdSpeichere (base : Register) (src : XmmReg)
    (d : BitVec 32) (suffix : List Byte) :
    fpHwDecode (fpHwEncodeMovsdSpeichere base src d ++ suffix) =
      some (⟨.movsdSpeichere base src d,
        (fpHwEncodeMovsdSpeichere base src d).length⟩, suffix) := by
  cases base <;> cases src <;>
    simp [fpHwEncodeMovsdSpeichere, fpHwDecode, fpHwNach0F, fpHwDecodeRest,
      fpHwRexXB, fpHwRexXX,
      fpHwDecodeMemForm, fpHwDecodeReg, fpHwArithVonOpcode,
      codeXmm, xmmCode, xmmHigh, xmmLow, codeReg, regCode, regHigh, regLow,
      fpHwRex, fpHwRexBits, modrmMem, leBytes32, parseLe32_cons]

/- CUTS: skeleton plus encoders; decoder, execution and witnesses open.
-/

#print axioms fpHwRex

end Gabbro.Grammatik.X86
