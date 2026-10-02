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
      fpHwRexXB, fpHwArithOpcode,
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
      fpHwRexXB, fpHwArithOpcode,
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
      fpHwRexXB, fpHwArithOpcode,
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
      fpHwRexXB, fpHwArithOpcode,
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
      fpHwRexXB,
      fpHwDecodeMemForm, fpHwArithVonOpcode,
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
      fpHwRexXB,
      fpHwDecodeMemForm, fpHwArithVonOpcode,
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
      fpHwDecodeMemForm, fpHwArithVonOpcode,
      codeXmm, xmmCode, xmmHigh, xmmLow, codeReg, regCode, regHigh, regLow,
      fpHwRex, fpHwRexBits, modrmMem, leBytes32, parseLe32_cons]

/-! ## 4. Explicit refusals: order, prefixes, widths, shapes.

  A REX byte before the mandatory prefix, an F3 prefix, a non-REX
  byte after the prefix, a set REX.X bit, a conversion with the wrong
  REX.W, a memory-source conversion (no accepted execution exists),
  a register-form store, COMISD (NP 0F 2F: no row -- the accepted
  `ucomiFlags` never traps on quiet NaNs, so only UCOMISD is modelled),
  a swapped mandatory prefix, a non-36 SIB, a non-canonical ModRM mode
  and every truncation refuse with `none`. -/

/-- A REX byte before the mandatory prefix refuses: only prefix-first
    order decodes (Vol.2A 2-7f). -/
theorem fpHwDecode_rexZuerst_verweigert (suffix : List Byte) :
    fpHwDecode (natByte 64 :: natByte 242 :: natByte 15 :: natByte 92 ::
      modrmReg 0 0 :: suffix) = none := by
  rfl

/-- An F3 prefix refuses: scalar DOUBLE rows need F2 (or 66). -/
theorem fpHwDecode_f3_verweigert (suffix : List Byte) :
    fpHwDecode (natByte 243 :: natByte 64 :: natByte 15 :: natByte 92 ::
      modrmReg 0 0 :: suffix) = none := by
  rfl

/-- A non-REX byte after the prefix refuses. -/
theorem fpHwDecode_keinRex_verweigert (suffix : List Byte) :
    fpHwDecode (natByte 242 :: natByte 80 :: natByte 15 :: natByte 92 ::
      modrmReg 0 0 :: suffix) = none := by
  rfl

/-- A lone F2 prefix refuses. -/
theorem fpHwDecode_abgeschnitten_praefix :
    fpHwDecode [natByte 242] = none := by
  rfl

/-- F2 plus REX without escape refuses. -/
theorem fpHwDecode_abgeschnitten_rex :
    fpHwDecode [natByte 242, natByte 64] = none := by
  rfl

/-- F2 REX 0F without opcode and ModRM refuses. -/
theorem fpHwDecode_abgeschnitten_opcode :
    fpHwDecode [natByte 242, natByte 64, natByte 15] = none := by
  rfl

/-- F2 REX 0F opcode without ModRM refuses. -/
theorem fpHwDecode_abgeschnitten_modrm :
    fpHwDecode [natByte 242, natByte 64, natByte 15, natByte 92] = none := by
  rfl

/-- ModRM mod = 01 refuses: only mod = 11 and mod = 10 are canonical. -/
theorem fpHwDecode_modEins_verweigert (suffix : List Byte) :
    fpHwDecode (natByte 242 :: natByte 64 :: natByte 15 :: natByte 92 ::
      natByte 64 :: suffix) = none := by
  rfl

/-- ModRM mod = 00 refuses. -/
theorem fpHwDecode_modNull_verweigert (suffix : List Byte) :
    fpHwDecode (natByte 242 :: natByte 64 :: natByte 15 :: natByte 92 ::
      natByte 0 :: suffix) = none := by
  rfl

/-- Opcode 11 with a register ModRM (non-canonical register store)
    refuses. -/
theorem fpHwDecode_speichereRegister_verweigert (suffix : List Byte) :
    fpHwDecode (natByte 242 :: natByte 64 :: natByte 15 :: natByte 17 ::
      modrmReg 0 1 :: suffix) = none := by
  rfl

/-- CVTSI2SD with REX.W = 0 refuses: W = 0 selects the doubleword
    source (Vol.2A 3-236) while the accepted `cvtsi2sd` converts the
    whole 64-bit register. -/
theorem fpHwDecode_cvtsiW0_verweigert (suffix : List Byte) :
    fpHwDecode (natByte 242 :: natByte 64 :: natByte 15 :: natByte 42 ::
      modrmReg 0 1 :: suffix) = none := by
  rfl

/-- CVTTSD2SI with REX.W = 0 refuses: W = 0 writes a 32-bit
    destination with 32-bit saturation (Vol.2A 3-253) while the
    accepted `cvttsd2si` writes the whole 64-bit register. -/
theorem fpHwDecode_cvttW0_verweigert (suffix : List Byte) :
    fpHwDecode (natByte 242 :: natByte 64 :: natByte 15 :: natByte 44 ::
      modrmReg 0 1 :: suffix) = none := by
  rfl

/-- Arithmetic with REX.W = 1 refuses in this subset: silicon ignores
    REX.W on these forms, but the subset pins W = 0 (see CUTS). -/
theorem fpHwDecode_arithW1_verweigert (suffix : List Byte) :
    fpHwDecode (natByte 242 :: natByte 72 :: natByte 15 :: natByte 92 ::
      modrmReg 0 1 :: suffix) = none := by
  rfl

/-- A set REX.X bit refuses: no SIB-index execution exists. -/
theorem fpHwDecode_rexX_verweigert (suffix : List Byte) :
    fpHwDecode (natByte 242 :: natByte 66 :: natByte 15 :: natByte 92 ::
      modrmReg 0 1 :: suffix) = none := by
  rfl

/-- Memory-source CVTSI2SD refuses: the accepted executor converts
    register sources only (no `FpBefehl` constructor, no second
    evaluator). -/
theorem fpHwDecode_cvtsiSpeicher_verweigert (d : BitVec 32)
    (suffix : List Byte) :
    fpHwDecode (natByte 242 :: natByte 72 :: natByte 15 :: natByte 42 ::
      modrmMem 0 0 :: leBytes32 d ++ suffix) = none := by
  simp [fpHwDecode, fpHwNach0F, fpHwDecodeRest, fpHwDecodeMemForm,
    fpHwArithVonOpcode, fpHwRexBits, codeReg, modrmMem, leBytes32,
    parseLe32_cons]

/-- Memory-source CVTTSD2SI refuses: the accepted executor converts
    from an XMM register only. -/
theorem fpHwDecode_cvttSpeicher_verweigert (d : BitVec 32)
    (suffix : List Byte) :
    fpHwDecode (natByte 242 :: natByte 72 :: natByte 15 :: natByte 44 ::
      modrmMem 0 0 :: leBytes32 d ++ suffix) = none := by
  simp [fpHwDecode, fpHwNach0F, fpHwDecodeRest, fpHwDecodeMemForm,
    fpHwArithVonOpcode, fpHwRexBits, codeReg, modrmMem, leBytes32,
    parseLe32_cons]

/-- COMISD (no mandatory prefix, 0F 2F) refuses: only the unordered
    form is modelled, since the accepted compare never traps on quiet
    NaNs (Vol.2B 4-733: COMISD signals #I on QNaN or SNaN, UCOMISD
    only on SNaN). -/
theorem fpHwDecode_comisd_verweigert (suffix : List Byte) :
    fpHwDecode (natByte 15 :: natByte 47 :: modrmReg 0 1 :: suffix) =
      none := by
  rfl

/-- Opcode 2E under F2 refuses: UCOMISD needs the 66 prefix. -/
theorem fpHwDecode_ucomiF2_verweigert (suffix : List Byte) :
    fpHwDecode (natByte 242 :: natByte 64 :: natByte 15 :: natByte 46 ::
      modrmReg 0 1 :: suffix) = none := by
  rfl

/-- Arithmetic under 66 refuses: scalar DOUBLE arithmetic needs F2. -/
theorem fpHwDecode_arith66_verweigert (suffix : List Byte) :
    fpHwDecode (natByte 102 :: natByte 64 :: natByte 15 :: natByte 88 ::
      modrmReg 0 1 :: suffix) = none := by
  rfl

/-- A non-36 SIB refuses: only the no-index SIB executes. -/
theorem fpHwDecode_sibFremd_verweigert (d : BitVec 32)
    (suffix : List Byte) :
    fpHwDecode (natByte 242 :: natByte 64 :: natByte 15 :: natByte 17 ::
      modrmMem 0 4 :: natByte 37 :: leBytes32 d ++ suffix) = none := by
  rfl

/-- A truncated displacement refuses: the first eight of nine MOVSD
    store bytes decode to nothing. -/
theorem fpHwDecode_abgeschnitten_disp :
    fpHwDecode ((fpHwEncodeMovsdSpeichere .rax .xmm0 0).take 8) = none := by
  decide

/-! ## Pilot disjointness: the accepted pilot refuses the new rows.

  Each pin evaluates the pilot decoder on closed REX-row bytes: the
  unified dispatcher (lane 575 shape) keeps every pilot form, and the
  scalar rows below extend it only where it refuses. Evidence for the
  FP-validator consumer (lane 658) and the source bridge (lane 660). -/

/-- The pilot refuses the high-register SUBSD row. -/
theorem fpHwPilot_weist_subsdRR_zurueck :
    decode (fpHwEncodeArithRR .sub .xmm15 .xmm8) = none := by
  decide

/-- The pilot refuses the MULSD memory row. -/
theorem fpHwPilot_weist_mulsdRM_zurueck :
    decode (fpHwEncodeArithRM .mul .xmm9 .r13 7) = none := by
  decide

/-- The pilot refuses the DIVSD register row. -/
theorem fpHwPilot_weist_divsdRR_zurueck :
    decode (fpHwEncodeArithRR .div .xmm0 .xmm1) = none := by
  decide

/-- The pilot refuses the UCOMISD register row. -/
theorem fpHwPilot_weist_ucomiRR_zurueck :
    decode (fpHwEncodeUcomiRR .xmm0 .xmm1) = none := by
  decide

/-- The pilot refuses the CVTSI2SD row. -/
theorem fpHwPilot_weist_cvtsi_zurueck :
    decode (fpHwEncodeCvtsi .xmm0 .rax) = none := by
  decide

/-- The pilot refuses the CVTTSD2SI row. -/
theorem fpHwPilot_weist_cvtt_zurueck :
    decode (fpHwEncodeCvtt .rax .xmm0) = none := by
  decide

/-- The pilot refuses the MOVSD store row. -/
theorem fpHwPilot_weist_movsdSpeichere_zurueck :
    decode (fpHwEncodeMovsdSpeichere .rax .xmm0 0) = none := by
  decide

/-! ## 5. Conversion domain adapter: where silicon and model agree.

  Silicon CVTTSD2SI on an invalid or out-of-range input returns the
  indefinite integer (80000000H / 80000000_00000000H, Vol.2A 3-253)
  while the accepted `cvttPaket` returns 0 or a saturated value
  (`cvttPaket_gleicht_gleitRoh`). The byte row therefore admits the
  form ONLY on the agreeing domain -- finite inputs whose truncation
  fits int64 -- and refuses outside it. The predicate reuses the
  accepted class/exact-value projections with the accepted truncation
  expression, never a second arithmetic. -/

/-- Truncation toward zero, when the class admits one. -/
def cvttTruncOf (w : Wort) : Option Int :=
  match Gleitkomma.klasse Gleitkomma.f64 (bites64 w) with
  | .nan => none
  | .unendlich => none
  | _ =>
    match Gleitkomma.wertExakt Gleitkomma.f64 (bites64 w) with
    | none => none
    | some v =>
      some (if 0 ≤ v.zweierExp then
        v.zaehler * ((2 ^ v.zweierExp.toNat : Nat) : Int)
        else v.zaehler.tdiv ((2 ^ (-v.zweierExp).toNat : Nat) : Int))

/-- The silicon-agreeing domain: a truncation exists and fits int64. -/
def cvttHwGueltig (w : Wort) : Bool :=
  match cvttTruncOf w with
  | none => false
  | some t => decide (-(2 ^ 63 : Int) ≤ t ∧ t ≤ 2 ^ 63 - 1)

/-- On the admitted domain the accepted wrapper IS the truncation
    with no saturation taken: every premise is used. -/
theorem cvttAdapter_gueltig (w : Wort) (t : Int)
    (ht : cvttTruncOf w = some t)
    (hlo : -(2 ^ 63 : Int) ≤ t) (hhi : t ≤ 2 ^ 63 - 1) :
    cvttPaket w = t := by
  cases hk : Gleitkomma.klasse Gleitkomma.f64 (bites64 w) with
  | nan =>
    have hnone : cvttTruncOf w = none := by
      unfold cvttTruncOf
      rw [hk]
    rw [hnone] at ht
    simp at ht
  | unendlich =>
    have hnone : cvttTruncOf w = none := by
      unfold cvttTruncOf
      rw [hk]
    rw [hnone] at ht
    simp at ht
  | null =>
    have hv0 : Gleitkomma.wertExakt Gleitkomma.f64 (bites64 w)
        = some ⟨0, 0⟩ := by
      unfold Gleitkomma.wertExakt
      rw [hk]
    obtain ⟨v, hv⟩ :
        ∃ v, Gleitkomma.wertExakt Gleitkomma.f64 (bites64 w) = some v :=
      ⟨_, hv0⟩
    have hE : (if 0 ≤ v.zweierExp then
        v.zaehler * ((2 ^ v.zweierExp.toNat : Nat) : Int)
        else v.zaehler.tdiv ((2 ^ (-v.zweierExp).toNat : Nat) : Int))
        = t := by
      have h2 := ht
      unfold cvttTruncOf at h2
      simp only [hk, hv] at h2
      exact Option.some_inj.mp h2
    unfold cvttPaket
    simp only [hk, hv, hE]
    have h1 : ¬ (t < -9223372036854775808) := by omega
    have h2 : ¬ (9223372036854775807 < t) := by omega
    simp [h1, h2]
  | subnormal =>
    obtain ⟨v, hv⟩ :
        ∃ v, Gleitkomma.wertExakt Gleitkomma.f64 (bites64 w) = some v := by
      unfold Gleitkomma.wertExakt
      rw [hk]
      exact ⟨_, rfl⟩
    have hE : (if 0 ≤ v.zweierExp then
        v.zaehler * ((2 ^ v.zweierExp.toNat : Nat) : Int)
        else v.zaehler.tdiv ((2 ^ (-v.zweierExp).toNat : Nat) : Int))
        = t := by
      have h2 := ht
      unfold cvttTruncOf at h2
      simp only [hk, hv] at h2
      exact Option.some_inj.mp h2
    unfold cvttPaket
    simp only [hk, hv, hE]
    have h1 : ¬ (t < -9223372036854775808) := by omega
    have h2 : ¬ (9223372036854775807 < t) := by omega
    simp [h1, h2]
  | normal =>
    obtain ⟨v, hv⟩ :
        ∃ v, Gleitkomma.wertExakt Gleitkomma.f64 (bites64 w) = some v := by
      unfold Gleitkomma.wertExakt
      rw [hk]
      exact ⟨_, rfl⟩
    have hE : (if 0 ≤ v.zweierExp then
        v.zaehler * ((2 ^ v.zweierExp.toNat : Nat) : Int)
        else v.zaehler.tdiv ((2 ^ (-v.zweierExp).toNat : Nat) : Int))
        = t := by
      have h2 := ht
      unfold cvttTruncOf at h2
      simp only [hk, hv] at h2
      exact Option.some_inj.mp h2
    unfold cvttPaket
    simp only [hk, hv, hE]
    have h1 : ¬ (t < -9223372036854775808) := by omega
    have h2 : ¬ (9223372036854775807 < t) := by omega
    simp [h1, h2]

/-- The domain predicate on a known-absent truncation is `false`. -/
theorem cvttHwGueltig_none (w : Wort)
    (htr : cvttTruncOf w = none) : cvttHwGueltig w = false := by
  unfold cvttHwGueltig
  rw [htr]

/-- The domain predicate on a known-present truncation is the range
    check. -/
theorem cvttHwGueltig_some (w : Wort) (t : Int)
    (htr : cvttTruncOf w = some t) :
    cvttHwGueltig w =
      decide (-(2 ^ 63 : Int) ≤ t ∧ t ≤ 2 ^ 63 - 1) := by
  unfold cvttHwGueltig
  rw [htr]

/-- From a positive domain check: truncation, wrapper value and range
    hold TOGETHER. -/
theorem cvttHwGueltig_erfolg (w : Wort)
    (h : cvttHwGueltig w = true) :
    ∃ t : Int, cvttTruncOf w = some t ∧ cvttPaket w = t ∧
      -(2 ^ 63 : Int) ≤ t ∧ t ≤ 2 ^ 63 - 1 := by
  cases htr : cvttTruncOf w with
  | none =>
    rw [cvttHwGueltig_none w htr] at h
    simp at h
  | some t =>
    rw [cvttHwGueltig_some w t htr] at h
    obtain ⟨hlo, hhi⟩ := of_decide_eq_true h
    exact ⟨t, rfl, cvttAdapter_gueltig w t htr hlo hhi, hlo, hhi⟩

/-- Infinity is outside the domain. -/
theorem cvttHwGueltig_unendlich :
    cvttHwGueltig 0x7FF0000000000000 = false := by
  decide

/-- A NaN payload is outside the domain. -/
theorem cvttHwGueltig_nan :
    cvttHwGueltig 0x7FF0000000000001 = false := by
  decide

/-- `42.0` is inside the domain. -/
theorem cvttHwGueltig_42 :
    cvttHwGueltig 0x4045000000000000 = true := by
  decide

/-! ## 6. Fetch from actual executable memory and the gated byte step.

  Fetch reads the bytes at the core RIP from the state's ACTUAL memory
  (executable prefix only, capped at 15) and decodes them with the
  independent §2 decoder, then checks consumed-length/remaining-suffix
  consistency, decode-length validity and execute permission. The byte
  step reuses the accepted `fpSchritt` through `FpByteAusgang`, with
  one adapter gate: CVTTSD2SI executes only on the §5 domain, since
  outside it the accepted wrapper and silicon disagree. -/

/-- The fetched window of an extended state. -/
def fpHwGeholt (t : FpZustand) : List Byte := geholt t.kern

/-- Fetch and decode with the independent REX decoder, gated by
    length consistency, decode-length validity and execute
    permission of the consumed prefix. -/
def fpHwFetchDekodiert (t : FpZustand) :
    Option (FpDecodiert × List Byte) :=
  match fpHwDecode (fpHwGeholt t) with
  | none => none
  | some (d, rest) =>
    if d.laenge + rest.length == (fpHwGeholt t).length &&
        laengeOk d.laenge && ausfuehrbarN t.kern.speicher t.kern.rip d.laenge
    then some (d, rest)
    else none

/-- Conversion admission at the byte row: CVTTSD2SI runs only on the
    silicon-agreeing domain; every other form is admitted. -/
def fpHwCvttZugelassen (b : FpBefehl) (t : FpZustand) : Bool :=
  match b with
  | .cvttsd2si _ src => cvttHwGueltig (xmmTief t.xmm src)
  | _ => true

/-- One REX byte step from actual memory: fetch, decode, gate, then
    the accepted `fpSchritt`. Takes ONLY the state. -/
def fpHwByteschritt (t : FpZustand) : FpByteAusgang :=
  match fpHwFetchDekodiert t with
  | none => .verweigert
  | some (d, _) =>
    if fpHwCvttZugelassen d.befehl t then
      match fpSchritt d t with
      | none => .verweigert
      | some t' => .weiter t'
    else .verweigert

/-- Fetch success pins the decoder equation and every guard. -/
theorem fpHwFetchDekodiert_erfolg (t : FpZustand) (d : FpDecodiert)
    (rest : List Byte) (h : fpHwFetchDekodiert t = some (d, rest)) :
    fpHwDecode (fpHwGeholt t) = some (d, rest) ∧
      d.laenge + rest.length = (fpHwGeholt t).length ∧
      laengeOk d.laenge = true ∧
      ausfuehrbarN t.kern.speicher t.kern.rip d.laenge = true := by
  unfold fpHwFetchDekodiert at h
  cases hd : fpHwDecode (fpHwGeholt t) with
  | none =>
    rw [hd] at h
    simp at h
  | some q =>
    obtain ⟨d', rest'⟩ := q
    rw [hd] at h
    simp only at h
    by_cases hc : (d'.laenge + rest'.length == (fpHwGeholt t).length &&
        laengeOk d'.laenge && ausfuehrbarN t.kern.speicher t.kern.rip d'.laenge)
    · rw [if_pos hc] at h
      obtain ⟨rfl, rfl⟩ := Option.some_inj.mp h
      rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨rfl, hc.1.1, hc.1.2, hc.2⟩
    · rw [if_neg hc] at h
      simp at h

/-- A successful gated byte-step runs the accepted `fpSchritt` on the
    fetched form. -/
theorem fpHwByteschritt_schritt (t t' : FpZustand) (d : FpDecodiert)
    (rest : List Byte)
    (hf : fpHwFetchDekodiert t = some (d, rest))
    (hgate : fpHwCvttZugelassen d.befehl t = true)
    (hout : fpHwByteschritt t = .weiter t') :
    fpSchritt d t = some t' := by
  unfold fpHwByteschritt at hout
  rw [hf] at hout
  simp only at hout
  rw [hgate] at hout
  simp only at hout
  cases hs : fpSchritt d t with
  | none => simp [hs] at hout
  | some u =>
    simp [hs] at hout
    rw [hout]

/-- A refused conversion domain refuses the byte step, whatever the
    accepted wrapper would compute. -/
theorem fpHwByteschritt_cvttVerweigert (t : FpZustand) (d : FpDecodiert)
    (rest : List Byte)
    (hf : fpHwFetchDekodiert t = some (d, rest))
    (hgate : fpHwCvttZugelassen d.befehl t = false) :
    fpHwByteschritt t = .verweigert := by
  unfold fpHwByteschritt
  rw [hf]
  simp [hgate]

/-- A refused MXCSR word refuses the byte step on every state. -/
theorem fpHwByteschritt_profil_verweigert (t : FpZustand)
    (h : fpEintritt t.fp = false) :
    fpHwByteschritt t = .verweigert := by
  unfold fpHwByteschritt
  cases hf : fpHwFetchDekodiert t with
  | none => rfl
  | some q =>
    obtain ⟨d, rest⟩ := q
    have hok := (fpHwFetchDekodiert_erfolg t d rest hf).2.2.1
    have hstep : fpSchritt d t = none :=
      fpSchritt_profil_verweigert d t hok h
    by_cases hgate : fpHwCvttZugelassen d.befehl t = true
    · simp [hgate, hstep]
    · have hgate' : fpHwCvttZugelassen d.befehl t = false := by
        cases hg : fpHwCvttZugelassen d.befehl t with
        | true => simp [hg] at hgate
        | false => rfl
      simp [hgate']

/-! ## 7. Byte-level IEEE observations: direction, lanes, classes.

  Operand direction is decoder-established (§3 round trips: the
  destination rides ModRM.reg, except CVTTSD2SI whose GPR destination
  rides reg and whose XMM source rides r/m). What is derived here
  from the accepted evaluator and kernel, never restated: the fetched
  low-half result IS the model op (all four), hence agrees at class
  level (NaN payloads never concluded); the UCOMISD unordered and
  equal rows with reserved flags; two distinct NaN payloads taking
  the unordered row (payload ignored, class decides); and the
  signed-zero subtraction. -/

/-- A fetched arithmetic byte-step computes the model op into the
    low half (all four ops, high and low registers alike). -/
theorem fpHwByteschritt_arithRR_rechnet (t t' : FpZustand)
    (d : FpDecodiert) (op : Gabbro.Grammatik.GleitOp)
    (dst src : XmmReg) (rest : List Byte)
    (hf : fpHwFetchDekodiert t = some (d, rest))
    (hform : d.befehl = fpHwArithRR op dst src)
    (hfp : fpEintritt t.fp = true)
    (hgate : fpHwCvttZugelassen d.befehl t = true)
    (hout : fpHwByteschritt t = .weiter t') :
    xmmTief t'.xmm dst =
      fpRechne op (xmmTief t.xmm dst) (xmmTief t.xmm src) := by
  have hok := (fpHwFetchDekodiert_erfolg t d rest hf).2.2.1
  have hstep := fpHwByteschritt_schritt t t' d rest hf hgate hout
  cases op with
  | add =>
    have hform' : d.befehl = .addsdRR dst src := hform
    have heq := fpSchritt_addsdRR d t dst src hok hfp hform'
    rw [hstep] at heq
    obtain rfl := Option.some_inj.mp heq
    exact xmmSchreibeTief_tief _ _ _
  | sub =>
    have hform' : d.befehl = .subsdRR dst src := hform
    have heq := fpSchritt_subsdRR d t dst src hok hfp hform'
    rw [hstep] at heq
    obtain rfl := Option.some_inj.mp heq
    exact xmmSchreibeTief_tief _ _ _
  | mul =>
    have hform' : d.befehl = .mulsdRR dst src := hform
    have heq := fpSchritt_mulsdRR d t dst src hok hfp hform'
    rw [hstep] at heq
    obtain rfl := Option.some_inj.mp heq
    exact xmmSchreibeTief_tief _ _ _
  | div =>
    have hform' : d.befehl = .divsdRR dst src := hform
    have heq := fpSchritt_divsdRR d t dst src hok hfp hform'
    rw [hstep] at heq
    obtain rfl := Option.some_inj.mp heq
    exact xmmSchreibeTief_tief _ _ _

/-- A fetched arithmetic byte-step agrees with the source model op at
    the class level: NaN payload equality is never concluded (the
    preserved cut of `Gleitprofil` §7 and `ScalarFloat` §4/§6). -/
theorem fpHwByteschritt_arithRR_klasse (t t' : FpZustand)
    (d : FpDecodiert) (op : Gabbro.Grammatik.GleitOp)
    (dst src : XmmReg) (rest : List Byte)
    (hf : fpHwFetchDekodiert t = some (d, rest))
    (hform : d.befehl = fpHwArithRR op dst src)
    (hfp : fpEintritt t.fp = true)
    (hgate : fpHwCvttZugelassen d.befehl t = true)
    (hout : fpHwByteschritt t = .weiter t') :
    Gleitkomma.klasse Gleitkomma.f64 (bites64 (xmmTief t'.xmm dst)) =
      Gleitkomma.klasse Gleitkomma.f64
        (Gabbro.Grammatik.gleitRechne op
          (bites64 (xmmTief t.xmm dst)) (bites64 (xmmTief t.xmm src))) := by
  have hrech := fpHwByteschritt_arithRR_rechnet t t' d op dst src rest
    hf hform hfp hgate hout
  rw [hrech]
  exact fpRechne_klasse op _ _

/-- A fetched arithmetic byte-step keeps the destination upper half
    (legacy SSE preserve semantics, Vol.2B 4-692f). -/
theorem fpHwByteschritt_arithRR_hoch (t t' : FpZustand)
    (d : FpDecodiert) (op : Gabbro.Grammatik.GleitOp)
    (dst src : XmmReg) (rest : List Byte)
    (hf : fpHwFetchDekodiert t = some (d, rest))
    (hform : d.befehl = fpHwArithRR op dst src)
    (hfp : fpEintritt t.fp = true)
    (hgate : fpHwCvttZugelassen d.befehl t = true)
    (hout : fpHwByteschritt t = .weiter t') :
    xmmHoch t'.xmm dst = xmmHoch t.xmm dst := by
  have hok := (fpHwFetchDekodiert_erfolg t d rest hf).2.2.1
  have hstep := fpHwByteschritt_schritt t t' d rest hf hgate hout
  cases op with
  | add =>
    have hform' : d.befehl = .addsdRR dst src := hform
    exact fpSchritt_addsdRR_hoch d t t' dst src hok hfp hform' hstep
  | sub =>
    have hform' : d.befehl = .subsdRR dst src := hform
    exact fpSchritt_subsdRR_hoch d t t' dst src hok hfp hform' hstep
  | mul =>
    have hform' : d.befehl = .mulsdRR dst src := hform
    exact fpSchritt_mulsdRR_hoch d t t' dst src hok hfp hform' hstep
  | div =>
    have hform' : d.befehl = .divsdRR dst src := hform
    exact fpSchritt_divsdRR_hoch d t t' dst src hok hfp hform' hstep

/-- UCOMISD unordered row at step level: a NaN-class left operand
    forces ZF, PF, CF with reserved flags (Vol.2B 4-733f). -/
theorem fpHwSchritt_ucomisdRR_ungeordnet (d : FpDecodiert)
    (t : FpZustand) (lhs rhs : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .ucomisdRR lhs rhs)
    (hna : Gleitkomma.klasse Gleitkomma.f64
      (bites64 (xmmTief t.xmm lhs)) = .nan) :
    fpSchritt d t = some { t with kern := { t.kern with
      rip := ripNach t.kern.rip d.laenge,
      flags := ⟨true, true, some false, true, false, false⟩ } } := by
  rw [fpSchritt_ucomisdRR d t lhs rhs hok hfp h,
    ucomiFlags_ungeordnet_links _ _ hna]

/-- UCOMISD equal row at step level: no strict comparison either way
    sets only ZF, with reserved flags. -/
theorem fpHwSchritt_ucomisdRR_gleich (d : FpDecodiert)
    (t : FpZustand) (lhs rhs : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .ucomisdRR lhs rhs)
    (h1 : Gleitkomma.flt Gleitkomma.f64
      (bites64 (xmmTief t.xmm lhs)) (bites64 (xmmTief t.xmm rhs)) = false)
    (h2 : Gleitkomma.flt Gleitkomma.f64
      (bites64 (xmmTief t.xmm rhs)) (bites64 (xmmTief t.xmm lhs)) = false)
    (ha : Gleitkomma.klasse Gleitkomma.f64
      (bites64 (xmmTief t.xmm lhs)) ≠ .nan)
    (hb : Gleitkomma.klasse Gleitkomma.f64
      (bites64 (xmmTief t.xmm rhs)) ≠ .nan) :
    fpSchritt d t = some { t with kern := { t.kern with
      rip := ripNach t.kern.rip d.laenge,
      flags := ⟨false, false, some false, true, false, false⟩ } } := by
  rw [fpSchritt_ucomisdRR d t lhs rhs hok hfp h,
    ucomiFlags_gleich _ _ h1 h2 ha hb]

/-- Two distinct NaN payloads both classify as NaN: classification
    pins no payload (binary64, decided at word level). -/
theorem fpHwNan_nutzlast_klasse :
    Gleitkomma.klasse Gleitkomma.f64
        (bites64 0x7FF0000000000001) = .nan ∧
      Gleitkomma.klasse Gleitkomma.f64
        (bites64 0x7FF0000000000002) = .nan ∧
      (0x7FF0000000000001 : Wort) ≠ 0x7FF0000000000002 := by
  refine ⟨by decide, by decide, by decide⟩

/-- Two distinct NaN payloads take the unordered row: the payload is
    ignored, the class decides. -/
theorem fpHwNan_ungeordnet :
    ucomiFlags (bites64 0x7FF0000000000001)
      (bites64 0x7FF0000000000002) =
      ⟨true, true, some false, true, false, false⟩ := by
  decide

/-- Signed-zero subtraction: `+0.0 - +0.0` is `+0.0`. -/
theorem fpHwSub_plusnull : fpRechne .sub 0 0 = 0 := by
  decide

/-! ## 8. Joint witnesses: fetched runs that change memory.

  W1 runs a fetched REX DIVSD special case (`1.0 / +0.0 = +∞`,
  `div_eins_durch_null`) into a fetched REX MOVSD store: two reached
  byte-steps from actual executable bytes, one real memory change,
  the word reading back, under the admitted profile throughout. -/

/-- Witness image: REX DIVSD (5 bytes) then REX MOVSD store (9). -/
def fpHwW1Bild : List Byte :=
  fpHwEncodeArithRR .div .xmm0 .xmm1 ++
    fpHwEncodeMovsdSpeichere .rax .xmm0 0

/-- The DIVSD prefix is five bytes long. -/
theorem fpHwW1Div_laenge :
    (fpHwEncodeArithRR .div .xmm0 .xmm1).length = 5 := by
  rfl

/-- The store suffix is nine bytes long. -/
theorem fpHwW1Store_laenge :
    (fpHwEncodeMovsdSpeichere .rax .xmm0 0).length = 9 := by
  rfl

/-- Witness memory: zeroed bytes with the image at 4096 and execute
    permission exactly on those fourteen bytes; data access stays
    fully open. -/
def fpHwW1Speicher : Speicher :=
  { zeugenSpeicher with
    bytes := fun a =>
      if a.toNat - 4096 < fpHwW1Bild.length then
        fpHwW1Bild.getD (a.toNat - 4096) 0
      else zeugenSpeicher.bytes a
    ausfuehrbar := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4110) }

/-- Witness XMM file: `xmm0` holds `1.0`, every other register `+0.0`. -/
def fpHwW1Xmm : XmmDatei :=
  fun q => if q = XmmReg.xmm0 then vecJoin 0x3FF0000000000000 0
    else vecJoin 0 0

/-- Witness core: `rax` points at 8192, RIP at the image. -/
def fpHwW1Kern : Zustand :=
  { register := fun q => if q = Register.rax then BitVec.ofNat 64 8192
      else BitVec.ofNat 64 0
    flags := ⟨false, true, some false, false, false, false⟩
    rip := BitVec.ofNat 64 4096
    speicher := fpHwW1Speicher }

/-- Witness extended state: reset FP control word (admitted profile). -/
def fpHwW1T : FpZustand := ⟨fpHwW1Kern, fpHwW1Xmm, kontextReset⟩

/-- The witness `xmm0` holds `1.0`. -/
theorem fpHwW1Tief0 :
    xmmTief fpHwW1T.xmm XmmReg.xmm0 = 0x3FF0000000000000 := by
  decide

/-- The witness `xmm1` holds `+0.0`. -/
theorem fpHwW1Tief1 : xmmTief fpHwW1T.xmm XmmReg.xmm1 = 0 := by
  decide

/-- The witness store address: `rax + 0` is 8192. -/
theorem fpHwW1EffAddr :
    effAddr fpHwW1T.kern Register.rax 0 = BitVec.ofNat 64 8192 := by
  decide

/-- Admitted profile on the witness state. -/
theorem fpHwW1Fp : fpEintritt fpHwW1T.fp = true := by
  decide

/-- Five-byte decode lengths are checked data. -/
theorem fpHwW1Laenge5 : laengeOk 5 = true := by
  decide

/-- Nine-byte decode lengths are checked data. -/
theorem fpHwW1Laenge9 : laengeOk 9 = true := by
  decide

/-- The fetch window holds exactly the image. -/
theorem fpHwW1Geholt : fpHwGeholt fpHwW1T = fpHwW1Bild := by
  decide

/-- The five DIVSD bytes carry execute permission. -/
theorem fpHwW1Perm5 :
    ausfuehrbarN fpHwW1T.kern.speicher fpHwW1T.kern.rip 5 = true := by
  decide

/-- The image is fourteen bytes long. -/
theorem fpHwW1Bild_laenge : fpHwW1Bild.length = 14 := by
  decide

/-- Fetch from the actual image yields the DIVSD form with the store
    bytes as suffix. -/
theorem fpHwW1_fetch1 :
    fpHwFetchDekodiert fpHwW1T =
      some (⟨.divsdRR .xmm0 .xmm1, 5⟩,
        fpHwEncodeMovsdSpeichere .rax .xmm0 0) := by
  have hbytes : fpHwGeholt fpHwW1T =
      fpHwEncodeArithRR .div .xmm0 .xmm1 ++
        fpHwEncodeMovsdSpeichere .rax .xmm0 0 := by
    simp only [fpHwW1Geholt, fpHwW1Bild]
  have hrt := fpHwRoundtrip_arithRR .div .xmm0 .xmm1
    (fpHwEncodeMovsdSpeichere .rax .xmm0 0)
  have hred : fpHwArithRR .div .xmm0 .xmm1 = .divsdRR .xmm0 .xmm1 := rfl
  have hlen : (fpHwEncodeArithRR .div .xmm0 .xmm1).length = 5 :=
    fpHwW1Div_laenge
  rw [hlen, hred] at hrt
  have hdec : fpHwDecode (fpHwGeholt fpHwW1T) =
      some (⟨.divsdRR .xmm0 .xmm1, 5⟩,
        fpHwEncodeMovsdSpeichere .rax .xmm0 0) := by
    rw [hbytes]
    exact hrt
  have hlenBild : (fpHwGeholt fpHwW1T).length = 14 := by
    rw [fpHwW1Geholt, fpHwW1Bild_laenge]
  have hstore : (fpHwEncodeMovsdSpeichere .rax .xmm0 0).length = 9 :=
    fpHwW1Store_laenge
  unfold fpHwFetchDekodiert
  rw [hdec]
  simp only
  rw [hlenBild, hstore, fpHwW1Laenge5, fpHwW1Perm5]
  decide

/-- The conversion gate is open on the DIVSD form. -/
theorem fpHwW1Gate1 :
    fpHwCvttZugelassen (.divsdRR .xmm0 .xmm1) fpHwW1T = true := by
  rfl

/-- Witness state after the divide: `xmm0` holds `+∞`. -/
def fpHwW1T1 : FpZustand :=
  { fpHwW1T with kern := { fpHwW1T.kern with rip := ripNach fpHwW1T.kern.rip 5 }, xmm := xmmSchreibeTief fpHwW1T.xmm XmmReg.xmm0 0x7FF0000000000000 }

/-- Witness memory after the store: `+∞` at 8192. -/
def fpHwW1SpeicherNach : Speicher :=
  { fpHwW1Speicher with bytes := writeBytes fpHwW1Speicher (BitVec.ofNat 64 8192) 0x7FF0000000000000 }

/-- Witness state after the store. -/
def fpHwW1T2 : FpZustand :=
  { fpHwW1T1 with kern := { fpHwW1T1.kern with speicher := fpHwW1SpeicherNach, rip := ripNach fpHwW1T1.kern.rip 9 } }

/-- First reached byte-step: actual DIVSD bytes compute `+∞`. -/
theorem fpHwW1_schritt1 :
    fpHwByteschritt fpHwW1T = .weiter fpHwW1T1 := by
  unfold fpHwByteschritt
  rw [fpHwW1_fetch1]
  simp only
  rw [fpHwW1Gate1]
  simp only
  have hs := fpSchritt_divsdRR ⟨.divsdRR .xmm0 .xmm1, 5⟩ fpHwW1T
    .xmm0 .xmm1 fpHwW1Laenge5 fpHwW1Fp rfl
  rw [fpHwW1Tief0, fpHwW1Tief1, div_eins_durch_null] at hs
  simp only [hs, fpHwW1T1, if_true]

/-- After the divide, `xmm0` holds `+∞`. -/
theorem fpHwW1T1_tief0 :
    xmmTief fpHwW1T1.xmm XmmReg.xmm0 = 0x7FF0000000000000 := by
  decide

/-- The second fetch window holds exactly the store bytes. -/
theorem fpHwW1Geholt2 :
    fpHwGeholt fpHwW1T1 = fpHwEncodeMovsdSpeichere .rax .xmm0 0 := by
  decide

/-- The nine store bytes carry execute permission. -/
theorem fpHwW1Perm9 :
    ausfuehrbarN fpHwW1T1.kern.speicher fpHwW1T1.kern.rip 9 = true := by
  decide

/-- Fetch of the second step yields the store form. -/
theorem fpHwW1_fetch2 :
    fpHwFetchDekodiert fpHwW1T1 =
      some (⟨.movsdSpeichere .rax .xmm0 0, 9⟩, []) := by
  have hrt := fpHwRoundtrip_movsdSpeichere .rax .xmm0 0 []
  rw [fpHwW1Store_laenge] at hrt
  have hdec : fpHwDecode (fpHwGeholt fpHwW1T1) =
      some (⟨.movsdSpeichere .rax .xmm0 0, 9⟩, []) := by
    rw [fpHwW1Geholt2]
    simp only [List.append_nil] at hrt ⊢
    exact hrt
  have hlen : (fpHwGeholt fpHwW1T1).length = 9 := by
    rw [fpHwW1Geholt2, fpHwW1Store_laenge]
  unfold fpHwFetchDekodiert
  rw [hdec]
  simp only
  rw [hlen, fpHwW1Laenge9, fpHwW1Perm9]
  decide

/-- The store address is still 8192 after the divide. -/
theorem fpHwW1T1_effAddr :
    effAddr fpHwW1T1.kern Register.rax 0 = BitVec.ofNat 64 8192 := by
  decide

/-- The store goes through: `+∞` lands at 8192. -/
theorem fpHwW1_schreib :
    write64 fpHwW1T1.kern.speicher (effAddr fpHwW1T1.kern Register.rax 0)
      (xmmTief fpHwW1T1.xmm XmmReg.xmm0) = some fpHwW1SpeicherNach := by
  rw [fpHwW1T1_effAddr, fpHwW1T1_tief0]
  have hc : schreibbar8 fpHwW1Speicher (BitVec.ofNat 64 8192) = true := by
    decide
  have hmem : fpHwW1T1.kern.speicher = fpHwW1Speicher := rfl
  rw [hmem]
  unfold write64
  rw [if_pos hc, fpHwW1SpeicherNach]

/-- The conversion gate is open on the store form. -/
theorem fpHwW1Gate2 :
    fpHwCvttZugelassen (.movsdSpeichere .rax .xmm0 0) fpHwW1T1 = true := by
  rfl

/-- Second reached byte-step: actual store bytes write `xmm0`. -/
theorem fpHwW1_schritt2 :
    fpHwByteschritt fpHwW1T1 = .weiter fpHwW1T2 := by
  unfold fpHwByteschritt
  rw [fpHwW1_fetch2]
  simp only
  rw [fpHwW1Gate2]
  simp only
  have hs := fpSchritt_movsdSpeichere_erfolg
    ⟨.movsdSpeichere .rax .xmm0 0, 9⟩ fpHwW1T1
    .rax .xmm0 0 fpHwW1SpeicherNach
    fpHwW1Laenge9 fpHwW1Fp rfl fpHwW1_schreib
  simp only [hs, fpHwW1T2, if_true]

/-- The stored word reads back: `+∞` at 8192. -/
theorem fpHwW1_liest :
    read64 fpHwW1T2.kern.speicher (BitVec.ofNat 64 8192) =
      some 0x7FF0000000000000 := by
  have hrd : lesbar8 fpHwW1Speicher (BitVec.ofNat 64 8192) = true := by
    decide
  have hmem : fpHwW1T2.kern.speicher = fpHwW1SpeicherNach := rfl
  rw [hmem]
  exact read64_nach_write64 _ _ _ _ fpHwW1_schreib hrd

/-- The run observably changed memory (top footprint byte). -/
theorem fpHwW1_aendert :
    fpHwW1T.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ≠
      fpHwW1T2.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) := by
  decide

/-- Joint witness W1: two fetched REX byte-steps compute the DIVSD
    special case and store it, with a real memory change -- reached,
    read back, under the admitted profile. -/
theorem fpHwW1_div_speichert :
    ∃ (t' t'' : FpZustand),
      fpHwByteschritt fpHwW1T = .weiter t' ∧
      fpHwByteschritt t' = .weiter t'' ∧
      read64 t''.kern.speicher (BitVec.ofNat 64 8192) =
        some 0x7FF0000000000000 ∧
      fpHwW1T.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ≠
        t''.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ∧
      fpEintritt fpHwW1T.fp = true := by
  exact ⟨fpHwW1T1, fpHwW1T2, fpHwW1_schritt1, fpHwW1_schritt2,
    fpHwW1_liest, fpHwW1_aendert, fpHwW1Fp⟩

/-! ## 9. Joint witness W2: fetched conversion to store.

  A fetched REX.W CVTSI2SD (`rax = 42` to `42.0`, `cvtsiErg_42`) into
  a fetched REX MOVSD store: the 64-bit integer source the REX.W row
  selects is exactly what the accepted wrapper converts whole. -/

/-- Witness image: REX.W CVTSI2SD (5 bytes) then REX MOVSD store. -/
def fpHwW2Bild : List Byte :=
  fpHwEncodeCvtsi .xmm0 .rax ++ fpHwEncodeMovsdSpeichere .rbx .xmm0 0

/-- Witness memory: the image at 4096 with execute permission exactly
    on those fourteen bytes; data access stays fully open. -/
def fpHwW2Speicher : Speicher :=
  { zeugenSpeicher with bytes := fun a => if a.toNat - 4096 < fpHwW2Bild.length then fpHwW2Bild.getD (a.toNat - 4096) 0 else zeugenSpeicher.bytes a, ausfuehrbar := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4110) }

/-- Witness XMM file: all `+0.0` (the conversion overwrites `xmm0`). -/
def fpHwW2Xmm : XmmDatei := fun _ => vecJoin 0 0

/-- Witness core: `rax` holds 42, `rbx` points at 8192. -/
def fpHwW2Kern : Zustand :=
  { register := fun q => if q = Register.rax then BitVec.ofNat 64 42 else if q = Register.rbx then BitVec.ofNat 64 8192 else BitVec.ofNat 64 0, flags := ⟨false, true, some false, false, false, false⟩, rip := BitVec.ofNat 64 4096, speicher := fpHwW2Speicher }

/-- Witness extended state: reset FP control word. -/
def fpHwW2T : FpZustand := ⟨fpHwW2Kern, fpHwW2Xmm, kontextReset⟩

/-- The witness `rax` holds 42. -/
theorem fpHwW2Rax : fpHwW2T.kern.register .rax = 42 := by
  decide

/-- The witness store address: `rbx + 0` is 8192. -/
theorem fpHwW2EffAddr :
    effAddr fpHwW2T.kern Register.rbx 0 = BitVec.ofNat 64 8192 := by
  decide

/-- Admitted profile on the witness state. -/
theorem fpHwW2Fp : fpEintritt fpHwW2T.fp = true := by
  decide

/-- The fetch window holds exactly the image. -/
theorem fpHwW2Geholt : fpHwGeholt fpHwW2T = fpHwW2Bild := by
  decide

/-- The five conversion bytes carry execute permission. -/
theorem fpHwW2Perm5 :
    ausfuehrbarN fpHwW2T.kern.speicher fpHwW2T.kern.rip 5 = true := by
  decide

/-- The image is fourteen bytes long. -/
theorem fpHwW2Bild_laenge : fpHwW2Bild.length = 14 := by
  decide

/-- Fetch from the actual image yields the conversion form. -/
theorem fpHwW2_fetch1 :
    fpHwFetchDekodiert fpHwW2T =
      some (⟨.cvtsi2sd .xmm0 .rax, 5⟩,
        fpHwEncodeMovsdSpeichere .rbx .xmm0 0) := by
  have hbytes : fpHwGeholt fpHwW2T =
      fpHwEncodeCvtsi .xmm0 .rax ++
        fpHwEncodeMovsdSpeichere .rbx .xmm0 0 := by
    simp only [fpHwW2Geholt, fpHwW2Bild]
  have hrt := fpHwRoundtrip_cvtsi .xmm0 .rax
    (fpHwEncodeMovsdSpeichere .rbx .xmm0 0)
  have hlen : (fpHwEncodeCvtsi .xmm0 .rax).length = 5 :=
    fpHwLen_cvtsi _ _
  rw [hlen] at hrt
  have hdec : fpHwDecode (fpHwGeholt fpHwW2T) =
      some (⟨.cvtsi2sd .xmm0 .rax, 5⟩,
        fpHwEncodeMovsdSpeichere .rbx .xmm0 0) := by
    rw [hbytes]
    exact hrt
  have hlenBild : (fpHwGeholt fpHwW2T).length = 14 := by
    rw [fpHwW2Geholt, fpHwW2Bild_laenge]
  have hstore : (fpHwEncodeMovsdSpeichere .rbx .xmm0 0).length = 9 := by
    rfl
  have h5 : laengeOk 5 = true := by decide
  unfold fpHwFetchDekodiert
  rw [hdec]
  simp only
  rw [hlenBild, hstore, h5, fpHwW2Perm5]
  decide

/-- The conversion gate is open on the CVTSI2SD form. -/
theorem fpHwW2Gate1 :
    fpHwCvttZugelassen (.cvtsi2sd .xmm0 .rax) fpHwW2T = true := by
  rfl

/-- Witness state after the conversion: `xmm0` holds `42.0`. -/
def fpHwW2T1 : FpZustand :=
  { fpHwW2T with kern := { fpHwW2T.kern with rip := ripNach fpHwW2T.kern.rip 5 }, xmm := xmmSchreibeTief fpHwW2T.xmm XmmReg.xmm0 0x4045000000000000 }

/-- Witness memory after the store: `42.0` at 8192. -/
def fpHwW2SpeicherNach : Speicher :=
  { fpHwW2Speicher with bytes := writeBytes fpHwW2Speicher (BitVec.ofNat 64 8192) 0x4045000000000000 }

/-- Witness state after the store. -/
def fpHwW2T2 : FpZustand :=
  { fpHwW2T1 with kern := { fpHwW2T1.kern with speicher := fpHwW2SpeicherNach, rip := ripNach fpHwW2T1.kern.rip 9 } }

/-- First reached byte-step: actual conversion bytes compute `42.0`. -/
theorem fpHwW2_schritt1 :
    fpHwByteschritt fpHwW2T = .weiter fpHwW2T1 := by
  unfold fpHwByteschritt
  rw [fpHwW2_fetch1]
  simp only
  rw [fpHwW2Gate1]
  simp only
  have h5 : laengeOk 5 = true := by decide
  have hs := fpSchritt_cvtsi2sd ⟨.cvtsi2sd .xmm0 .rax, 5⟩ fpHwW2T
    .xmm0 .rax h5 fpHwW2Fp rfl
  rw [fpHwW2Rax, cvtsiErg_42] at hs
  simp only [hs, fpHwW2T1, if_true]

/-- After the conversion, `xmm0` holds `42.0`. -/
theorem fpHwW2T1_tief0 :
    xmmTief fpHwW2T1.xmm XmmReg.xmm0 = 0x4045000000000000 := by
  decide

/-- The second fetch window holds exactly the store bytes. -/
theorem fpHwW2Geholt2 :
    fpHwGeholt fpHwW2T1 = fpHwEncodeMovsdSpeichere .rbx .xmm0 0 := by
  decide

/-- The nine store bytes carry execute permission. -/
theorem fpHwW2Perm9 :
    ausfuehrbarN fpHwW2T1.kern.speicher fpHwW2T1.kern.rip 9 = true := by
  decide

/-- Fetch of the second step yields the store form. -/
theorem fpHwW2_fetch2 :
    fpHwFetchDekodiert fpHwW2T1 =
      some (⟨.movsdSpeichere .rbx .xmm0 0, 9⟩, []) := by
  have hrt := fpHwRoundtrip_movsdSpeichere .rbx .xmm0 0 []
  have hstore : (fpHwEncodeMovsdSpeichere .rbx .xmm0 0).length = 9 := by
    rfl
  rw [hstore] at hrt
  have hdec : fpHwDecode (fpHwGeholt fpHwW2T1) =
      some (⟨.movsdSpeichere .rbx .xmm0 0, 9⟩, []) := by
    rw [fpHwW2Geholt2]
    simp only [List.append_nil] at hrt ⊢
    exact hrt
  have hlen : (fpHwGeholt fpHwW2T1).length = 9 := by
    rw [fpHwW2Geholt2, hstore]
  have h9 : laengeOk 9 = true := by decide
  unfold fpHwFetchDekodiert
  rw [hdec]
  simp only
  rw [hlen, h9, fpHwW2Perm9]
  decide

/-- The store address is still 8192 after the conversion. -/
theorem fpHwW2T1_effAddr :
    effAddr fpHwW2T1.kern Register.rbx 0 = BitVec.ofNat 64 8192 := by
  decide

/-- The store goes through: `42.0` lands at 8192. -/
theorem fpHwW2_schreib :
    write64 fpHwW2T1.kern.speicher (effAddr fpHwW2T1.kern Register.rbx 0)
      (xmmTief fpHwW2T1.xmm XmmReg.xmm0) = some fpHwW2SpeicherNach := by
  rw [fpHwW2T1_effAddr, fpHwW2T1_tief0]
  have hc : schreibbar8 fpHwW2Speicher (BitVec.ofNat 64 8192) = true := by
    decide
  have hmem : fpHwW2T1.kern.speicher = fpHwW2Speicher := rfl
  rw [hmem]
  unfold write64
  rw [if_pos hc, fpHwW2SpeicherNach]

/-- The conversion gate is open on the store form. -/
theorem fpHwW2Gate2 :
    fpHwCvttZugelassen (.movsdSpeichere .rbx .xmm0 0) fpHwW2T1 = true := by
  rfl

/-- Second reached byte-step: actual store bytes write `xmm0`. -/
theorem fpHwW2_schritt2 :
    fpHwByteschritt fpHwW2T1 = .weiter fpHwW2T2 := by
  unfold fpHwByteschritt
  rw [fpHwW2_fetch2]
  simp only
  rw [fpHwW2Gate2]
  simp only
  have h9 : laengeOk 9 = true := by decide
  have hs := fpSchritt_movsdSpeichere_erfolg
    ⟨.movsdSpeichere .rbx .xmm0 0, 9⟩ fpHwW2T1
    .rbx .xmm0 0 fpHwW2SpeicherNach
    h9 fpHwW2Fp rfl fpHwW2_schreib
  simp only [hs, fpHwW2T2, if_true]

/-- The stored word reads back: `42.0` at 8192. -/
theorem fpHwW2_liest :
    read64 fpHwW2T2.kern.speicher (BitVec.ofNat 64 8192) =
      some 0x4045000000000000 := by
  have hrd : lesbar8 fpHwW2Speicher (BitVec.ofNat 64 8192) = true := by
    decide
  have hmem : fpHwW2T2.kern.speicher = fpHwW2SpeicherNach := rfl
  rw [hmem]
  exact read64_nach_write64 _ _ _ _ fpHwW2_schreib hrd

/-- The run observably changed memory (top footprint byte). -/
theorem fpHwW2_aendert :
    fpHwW2T.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ≠
      fpHwW2T2.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) := by
  decide

/-- Joint witness W2: fetched REX.W conversion then store -- reached,
    read back, with a real memory change. -/
theorem fpHwW2_cvtsi_speichert :
    ∃ (t' t'' : FpZustand),
      fpHwByteschritt fpHwW2T = .weiter t' ∧
      fpHwByteschritt t' = .weiter t'' ∧
      read64 t''.kern.speicher (BitVec.ofNat 64 8192) =
        some 0x4045000000000000 ∧
      fpHwW2T.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ≠
        t''.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ∧
      fpEintritt fpHwW2T.fp = true := by
  exact ⟨fpHwW2T1, fpHwW2T2, fpHwW2_schritt1, fpHwW2_schritt2,
    fpHwW2_liest, fpHwW2_aendert, fpHwW2Fp⟩

/-! ## 10. Joint witness W3: truncation on the domain, refusal off it.

  `42.0` converts to `42` in `rax` through fetched REX.W bytes; the
  same bytes with `+∞` in the source refuse at the §5 gate, since
  outside the domain the accepted wrapper and silicon disagree
  (0 versus the indefinite integer, Vol.2A 3-253). -/

/-- Witness image: REX.W CVTTSD2SI (5 bytes). -/
def fpHwW3Bild : List Byte := fpHwEncodeCvtt .rax .xmm0

/-- Witness memory: the image at 4096 with execute permission exactly
    on those five bytes. -/
def fpHwW3Speicher : Speicher :=
  { zeugenSpeicher with bytes := fun a => if a.toNat - 4096 < fpHwW3Bild.length then fpHwW3Bild.getD (a.toNat - 4096) 0 else zeugenSpeicher.bytes a, ausfuehrbar := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4101) }

/-- Witness XMM file: `xmm0` holds `42.0`. -/
def fpHwW3Xmm : XmmDatei :=
  fun q => if q = XmmReg.xmm0 then vecJoin 0x4045000000000000 0
    else vecJoin 0 0

/-- Witness core: RIP at the image. -/
def fpHwW3Kern : Zustand :=
  { register := fun _ => BitVec.ofNat 64 0, flags := ⟨false, true, some false, false, false, false⟩, rip := BitVec.ofNat 64 4096, speicher := fpHwW3Speicher }

/-- Witness extended state: reset FP control word. -/
def fpHwW3T : FpZustand := ⟨fpHwW3Kern, fpHwW3Xmm, kontextReset⟩

/-- The witness `xmm0` holds `42.0`. -/
theorem fpHwW3Tief0 :
    xmmTief fpHwW3T.xmm XmmReg.xmm0 = 0x4045000000000000 := by
  decide

/-- Admitted profile on the witness state. -/
theorem fpHwW3Fp : fpEintritt fpHwW3T.fp = true := by
  decide

/-- The fetch window holds exactly the image. -/
theorem fpHwW3Geholt : fpHwGeholt fpHwW3T = fpHwW3Bild := by
  decide

/-- The five conversion bytes carry execute permission. -/
theorem fpHwW3Perm5 :
    ausfuehrbarN fpHwW3T.kern.speicher fpHwW3T.kern.rip 5 = true := by
  decide

/-- Fetch yields the truncation form. -/
theorem fpHwW3_fetch :
    fpHwFetchDekodiert fpHwW3T =
      some (⟨.cvttsd2si .rax .xmm0, 5⟩, []) := by
  have hbytes : fpHwGeholt fpHwW3T = fpHwEncodeCvtt .rax .xmm0 ++ [] := by
    simp only [fpHwW3Geholt, fpHwW3Bild, List.append_nil]
  have hrt := fpHwRoundtrip_cvtt .rax .xmm0 []
  have hlen : (fpHwEncodeCvtt .rax .xmm0).length = 5 :=
    fpHwLen_cvtt _ _
  rw [hlen] at hrt
  have hdec : fpHwDecode (fpHwGeholt fpHwW3T) =
      some (⟨.cvttsd2si .rax .xmm0, 5⟩, []) := by
    rw [hbytes]
    exact hrt
  have hlenBild : (fpHwGeholt fpHwW3T).length = 5 := by
    rw [fpHwW3Geholt]
    have hb : fpHwW3Bild.length = 5 := by decide
    exact hb
  have h5 : laengeOk 5 = true := by decide
  unfold fpHwFetchDekodiert
  rw [hdec]
  simp only
  rw [hlenBild, h5, fpHwW3Perm5]
  decide

/-- The conversion gate is open on `42.0`. -/
theorem fpHwW3Gate :
    fpHwCvttZugelassen (.cvttsd2si .rax .xmm0) fpHwW3T = true := by
  have h0 := fpHwW3Tief0
  simp only [fpHwCvttZugelassen] at h0 ⊢
  rw [h0, cvttHwGueltig_42]

/-- The wrapper truncates `42.0` to `42`. -/
theorem fpHwW3_paket : cvttPaket 0x4045000000000000 = 42 := by
  decide

/-- Wrapping `42` as a word is the identity. -/
theorem fpHwW3_wort42 : intWort 42 = BitVec.ofNat 64 42 := by
  decide

/-- Witness state after the truncation: `rax` holds `42`. -/
def fpHwW3T1 : FpZustand :=
  { fpHwW3T with kern := { fpHwW3T.kern with register := regSet fpHwW3T.kern.register .rax (BitVec.ofNat 64 42), rip := ripNach fpHwW3T.kern.rip 5 } }

/-- Reached byte-step: actual truncation bytes write `42` to `rax`. -/
theorem fpHwW3_schritt :
    fpHwByteschritt fpHwW3T = .weiter fpHwW3T1 := by
  unfold fpHwByteschritt
  rw [fpHwW3_fetch]
  simp only
  rw [fpHwW3Gate]
  simp only
  have h5 : laengeOk 5 = true := by decide
  have hs := fpSchritt_cvttsd2si ⟨.cvttsd2si .rax .xmm0, 5⟩ fpHwW3T
    .rax .xmm0 h5 fpHwW3Fp rfl
  rw [fpHwW3Tief0, fpHwW3_paket, fpHwW3_wort42] at hs
  simp only [hs, fpHwW3T1, if_true]

/-- After the truncation, `rax` holds `42`. -/
theorem fpHwW3T1_rax : fpHwW3T1.kern.register .rax = BitVec.ofNat 64 42 := by
  have h : (regSet fpHwW3T.kern.register .rax (BitVec.ofNat 64 42)) .rax =
      BitVec.ofNat 64 42 :=
    regSet_gleich _ _ _
  have heq : fpHwW3T1.kern.register =
      regSet fpHwW3T.kern.register .rax (BitVec.ofNat 64 42) := rfl
  rw [heq]
  exact h

/-- Joint witness W3 (valid side): fetched truncation runs on the
    domain and lands `42` in `rax`. -/
theorem fpHwW3_cvtt_gueltig :
    ∃ (t' : FpZustand),
      fpHwByteschritt fpHwW3T = .weiter t' ∧
      t'.kern.register .rax = BitVec.ofNat 64 42 ∧
      fpEintritt fpHwW3T.fp = true := by
  exact ⟨fpHwW3T1, fpHwW3_schritt, fpHwW3T1_rax, fpHwW3Fp⟩

/-- Refused XMM file: `xmm0` holds `+∞`. -/
def fpHwW3BadXmm : XmmDatei :=
  fun q => if q = XmmReg.xmm0 then vecJoin 0x7FF0000000000000 0
    else vecJoin 0 0

/-- Refused state: same image, out-of-domain source. -/
def fpHwW3BadT : FpZustand := ⟨fpHwW3Kern, fpHwW3BadXmm, kontextReset⟩

/-- The refused `xmm0` holds `+∞`. -/
theorem fpHwW3BadTief0 :
    xmmTief fpHwW3BadT.xmm XmmReg.xmm0 = 0x7FF0000000000000 := by
  decide

/-- Fetch succeeds on the refused state: the bytes are fine, the
    domain is not. -/
theorem fpHwW3Bad_fetch :
    fpHwFetchDekodiert fpHwW3BadT =
      some (⟨.cvttsd2si .rax .xmm0, 5⟩, []) := by
  have hbytes : fpHwGeholt fpHwW3BadT = fpHwEncodeCvtt .rax .xmm0 ++ [] := by
    have hg : fpHwGeholt fpHwW3BadT = fpHwW3Bild := by decide
    simp only [hg, fpHwW3Bild, List.append_nil]
  have hrt := fpHwRoundtrip_cvtt .rax .xmm0 []
  have hlen : (fpHwEncodeCvtt .rax .xmm0).length = 5 :=
    fpHwLen_cvtt _ _
  rw [hlen] at hrt
  have hdec : fpHwDecode (fpHwGeholt fpHwW3BadT) =
      some (⟨.cvttsd2si .rax .xmm0, 5⟩, []) := by
    rw [hbytes]
    exact hrt
  have hlenBild : (fpHwGeholt fpHwW3BadT).length = 5 := by
    have hg : fpHwGeholt fpHwW3BadT = fpHwW3Bild := by decide
    have hb : fpHwW3Bild.length = 5 := by decide
    rw [hg, hb]
  have h5 : laengeOk 5 = true := by decide
  have hperm : ausfuehrbarN fpHwW3BadT.kern.speicher fpHwW3BadT.kern.rip 5 =
      true := by
    decide
  unfold fpHwFetchDekodiert
  rw [hdec]
  simp only
  rw [hlenBild, h5, hperm]
  decide

/-- The conversion gate is closed on `+∞`. -/
theorem fpHwW3BadGate :
    fpHwCvttZugelassen (.cvttsd2si .rax .xmm0) fpHwW3BadT = false := by
  have h0 := fpHwW3BadTief0
  simp only [fpHwCvttZugelassen] at h0 ⊢
  rw [h0, cvttHwGueltig_unendlich]

/-- Joint witness W3 (refused side): the same fetched bytes refuse
    off the domain -- fetch succeeds, the byte step refuses. -/
theorem fpHwW3_cvtt_verweigert :
    (∃ (d : FpDecodiert) (rest : List Byte),
      fpHwFetchDekodiert fpHwW3BadT = some (d, rest)) ∧
    fpHwByteschritt fpHwW3BadT = .verweigert := by
  refine ⟨⟨⟨.cvttsd2si .rax .xmm0, 5⟩, [], fpHwW3Bad_fetch⟩, ?_⟩
  exact fpHwByteschritt_cvttVerweigert _ _ _ fpHwW3Bad_fetch fpHwW3BadGate

/-! ## 11. Joint witness W4: unordered compare from bytes.

  A fetched REX UCOMISD on `1.0` against `1.0` sets the equal row
  (only ZF, OF/SF/AF cleared, Vol.2B 4-733f) -- the comparison
  channel for F-EQ: source float equality does not exist
  (`FloatSourceObservations`: `Expr.eq` takes only `.int`), flags do. -/

/-- Witness image: REX UCOMISD (5 bytes). -/
def fpHwW4Bild : List Byte := fpHwEncodeUcomiRR .xmm0 .xmm1

/-- Witness memory: the image at 4096 with execute permission exactly
    on those five bytes. -/
def fpHwW4Speicher : Speicher :=
  { zeugenSpeicher with bytes := fun a => if a.toNat - 4096 < fpHwW4Bild.length then fpHwW4Bild.getD (a.toNat - 4096) 0 else zeugenSpeicher.bytes a, ausfuehrbar := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4101) }

/-- Witness XMM file: `xmm0` and `xmm1` hold `1.0`. -/
def fpHwW4Xmm : XmmDatei :=
  fun q => if q = XmmReg.xmm0 ∨ q = XmmReg.xmm1 then vecJoin 0x3FF0000000000000 0
    else vecJoin 0 0

/-- Witness core: RIP at the image. -/
def fpHwW4Kern : Zustand :=
  { register := fun _ => BitVec.ofNat 64 0, flags := ⟨false, false, some false, false, false, false⟩, rip := BitVec.ofNat 64 4096, speicher := fpHwW4Speicher }

/-- Witness extended state: reset FP control word. -/
def fpHwW4T : FpZustand := ⟨fpHwW4Kern, fpHwW4Xmm, kontextReset⟩

/-- Both compared words are `1.0`. -/
theorem fpHwW4Tief :
    xmmTief fpHwW4T.xmm XmmReg.xmm0 = 0x3FF0000000000000 ∧
      xmmTief fpHwW4T.xmm XmmReg.xmm1 = 0x3FF0000000000000 := by
  decide

/-- `1.0` is not less than `1.0`, either way. -/
theorem fpHwW4Flt :
    Gleitkomma.flt Gleitkomma.f64 (bites64 0x3FF0000000000000)
        (bites64 0x3FF0000000000000) = false := by
  decide

/-- `1.0` classifies away from NaN. -/
theorem fpHwW4Klasse :
    Gleitkomma.klasse Gleitkomma.f64
      (bites64 0x3FF0000000000000) ≠ .nan := by
  decide

/-- Admitted profile on the witness state. -/
theorem fpHwW4Fp : fpEintritt fpHwW4T.fp = true := by
  decide

/-- Fetch yields the unordered-compare form. -/
theorem fpHwW4_fetch :
    fpHwFetchDekodiert fpHwW4T =
      some (⟨.ucomisdRR .xmm0 .xmm1, 5⟩, []) := by
  have hbytes : fpHwGeholt fpHwW4T = fpHwEncodeUcomiRR .xmm0 .xmm1 ++ [] := by
    have hg : fpHwGeholt fpHwW4T = fpHwW4Bild := by decide
    simp only [hg, fpHwW4Bild, List.append_nil]
  have hrt := fpHwRoundtrip_ucomiRR .xmm0 .xmm1 []
  have hlen : (fpHwEncodeUcomiRR .xmm0 .xmm1).length = 5 :=
    fpHwLen_ucomiRR _ _
  rw [hlen] at hrt
  have hdec : fpHwDecode (fpHwGeholt fpHwW4T) =
      some (⟨.ucomisdRR .xmm0 .xmm1, 5⟩, []) := by
    rw [hbytes]
    exact hrt
  have hlenBild : (fpHwGeholt fpHwW4T).length = 5 := by
    have hg : fpHwGeholt fpHwW4T = fpHwW4Bild := by decide
    have hb : fpHwW4Bild.length = 5 := by decide
    rw [hg, hb]
  have h5 : laengeOk 5 = true := by decide
  have hperm : ausfuehrbarN fpHwW4T.kern.speicher fpHwW4T.kern.rip 5 =
      true := by
    decide
  unfold fpHwFetchDekodiert
  rw [hdec]
  simp only
  rw [hlenBild, h5, hperm]
  decide

/-- The conversion gate is open on the compare form. -/
theorem fpHwW4Gate :
    fpHwCvttZugelassen (.ucomisdRR .xmm0 .xmm1) fpHwW4T = true := by
  rfl

/-- Witness state after the compare: equal row, RIP advanced. -/
def fpHwW4T1 : FpZustand :=
  { fpHwW4T with kern := { fpHwW4T.kern with rip := ripNach fpHwW4T.kern.rip 5, flags := ⟨false, false, some false, true, false, false⟩ } }

/-- Reached byte-step: actual compare bytes set the equal row. -/
theorem fpHwW4_schritt :
    fpHwByteschritt fpHwW4T = .weiter fpHwW4T1 := by
  unfold fpHwByteschritt
  rw [fpHwW4_fetch]
  simp only
  rw [fpHwW4Gate]
  simp only
  have h5 : laengeOk 5 = true := by decide
  have hs := fpHwSchritt_ucomisdRR_gleich ⟨.ucomisdRR .xmm0 .xmm1, 5⟩
    fpHwW4T .xmm0 .xmm1 h5 fpHwW4Fp rfl
  rw [fpHwW4Tief.1, fpHwW4Tief.2] at hs
  have hs2 := hs fpHwW4Flt fpHwW4Flt fpHwW4Klasse fpHwW4Klasse
  simp only [hs2, fpHwW4T1, if_true]

/-- Joint witness W4: the fetched compare observes equality through
    flags -- ZF set, OF/SF cleared, AF defined zero -- with no XMM or
    memory change. -/
theorem fpHwW4_ucomi_gleich :
    ∃ (t' : FpZustand),
      fpHwByteschritt fpHwW4T = .weiter t' ∧
      t'.kern.flags = ⟨false, false, some false, true, false, false⟩ ∧
      t'.xmm XmmReg.xmm0 = fpHwW4T.xmm XmmReg.xmm0 ∧
      t'.kern.speicher = fpHwW4T.kern.speicher := by
  refine ⟨fpHwW4T1, fpHwW4_schritt, ?_, ?_, ?_⟩ <;> rfl

/-! ## 12. Joint witness W5: memory fault refusal.

  The fetched REX MOVSD load addresses unreadable memory: fetch
  succeeds (execute permission is present), the accepted `read64`
  fails, and the byte step refuses explicitly -- a fault is never a
  silent value. -/

/-- Witness image: REX MOVSD load (9 bytes). -/
def fpHwW5Bild : List Byte := fpHwEncodeMovsdLade .xmm0 .rax 0

/-- Witness memory: the image at 4096 executable, nothing readable
    or writable anywhere. -/
def fpHwW5Speicher : Speicher :=
  { bytes := fun a => if a.toNat - 4096 < fpHwW5Bild.length then fpHwW5Bild.getD (a.toNat - 4096) 0 else BitVec.ofNat 8 0, lesbar := fun _ => false, schreibbar := fun _ => false, ausfuehrbar := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4105) }

/-- Witness core: `rax` points at 8192, RIP at the image. -/
def fpHwW5Kern : Zustand :=
  { register := fun q => if q = Register.rax then BitVec.ofNat 64 8192 else BitVec.ofNat 64 0, flags := ⟨false, true, some false, false, false, false⟩, rip := BitVec.ofNat 64 4096, speicher := fpHwW5Speicher }

/-- Witness extended state: reset FP control word. -/
def fpHwW5T : FpZustand := ⟨fpHwW5Kern, fpHwW2Xmm, kontextReset⟩

/-- Admitted profile on the witness state. -/
theorem fpHwW5Fp : fpEintritt fpHwW5T.fp = true := by
  decide

/-- Fetch yields the load form: execute access is present. -/
theorem fpHwW5_fetch :
    fpHwFetchDekodiert fpHwW5T =
      some (⟨.movsdLade .xmm0 .rax 0, 9⟩, []) := by
  have hbytes : fpHwGeholt fpHwW5T = fpHwEncodeMovsdLade .xmm0 .rax 0 ++ [] := by
    have hg : fpHwGeholt fpHwW5T = fpHwW5Bild := by decide
    simp only [hg, fpHwW5Bild, List.append_nil]
  have hrt := fpHwRoundtrip_movsdLade .xmm0 .rax 0 []
  have hlen : (fpHwEncodeMovsdLade .xmm0 .rax 0).length = 9 := by rfl
  rw [hlen] at hrt
  have hdec : fpHwDecode (fpHwGeholt fpHwW5T) =
      some (⟨.movsdLade .xmm0 .rax 0, 9⟩, []) := by
    rw [hbytes]
    exact hrt
  have hlenBild : (fpHwGeholt fpHwW5T).length = 9 := by
    have hg : fpHwGeholt fpHwW5T = fpHwW5Bild := by decide
    have hb : fpHwW5Bild.length = 9 := by decide
    rw [hg, hb]
  have h9 : laengeOk 9 = true := by decide
  have hperm : ausfuehrbarN fpHwW5T.kern.speicher fpHwW5T.kern.rip 9 =
      true := by
    decide
  unfold fpHwFetchDekodiert
  rw [hdec]
  simp only
  rw [hlenBild, h9, hperm]
  decide

/-- The data read fails: nothing is readable. -/
theorem fpHwW5_liest_nichts :
    read64 fpHwW5T.kern.speicher
      (effAddr fpHwW5T.kern Register.rax 0) = none := by
  decide

/-- The conversion gate is open on the load form. -/
theorem fpHwW5Gate :
    fpHwCvttZugelassen (.movsdLade .xmm0 .rax 0) fpHwW5T = true := by
  rfl

/-- Joint witness W5: fetch succeeds yet the byte step refuses -- the
    fault is explicit, never a silent value. -/
theorem fpHwW5_lade_verweigert :
    (∃ (d : FpDecodiert) (rest : List Byte),
      fpHwFetchDekodiert fpHwW5T = some (d, rest)) ∧
    fpHwByteschritt fpHwW5T = .verweigert := by
  refine ⟨⟨⟨.movsdLade .xmm0 .rax 0, 9⟩, [], fpHwW5_fetch⟩, ?_⟩
  have h9 : laengeOk 9 = true := by decide
  have hstep : fpSchritt ⟨.movsdLade .xmm0 .rax 0, 9⟩ fpHwW5T = none :=
    fpSchritt_movsdLade_verweigert _ _ _ _ _ h9 fpHwW5Fp rfl
      fpHwW5_liest_nichts
  have hstep2 : fpSchritt ⟨.movsdLade .xmm0 .rax 0#32, 9⟩ fpHwW5T = none :=
    hstep
  unfold fpHwByteschritt
  rw [fpHwW5_fetch]
  simp only
  rw [fpHwW5Gate]
  simp [hstep2]

/-! ## 13. Remaining witnesses: control state, high registers, boundary.

  W6 mutates the MXCSR word (flush-to-zero set): the same fetched
  DIVSD bytes that run under the reset word refuse -- profile
  admission is per-context data, rechecked at every step, never a
  one-time establishment. W7 executes a fetched high-register MOVSD
  copy (`xmm15 <- xmm8`, REX.R and REX.B both set): the low half
  moves and the destination upper half is preserved. W8 overlaps the
  code image with non-executable memory: the truncated window
  decodes to nothing, so the byte step refuses at fetch. -/

/-- Mutated control state: flush-to-zero set (Vol.1 11.4: FTZ off is
    part of the admitted profile). -/
def fpHwW6T : FpZustand := { fpHwW1T with fp := ⟨0x9F80⟩ }

/-- The mutated word is refused. -/
theorem fpHwW6Fp : fpEintritt fpHwW6T.fp = false := by
  decide

/-- Joint witness W6: identical bytes, mutated control word -- the
    byte step refuses. -/
theorem fpHwW6_profil_verweigert :
    fpHwByteschritt fpHwW6T = .verweigert :=
  fpHwByteschritt_profil_verweigert _ fpHwW6Fp

/-- Witness image W7: high-register MOVSD copy (5 bytes). -/
def fpHwW7Bild : List Byte := fpHwEncodeMovsdRR .xmm15 .xmm8

/-- Witness memory W7: the image at 4096 with execute permission
    exactly on those five bytes. -/
def fpHwW7Speicher : Speicher :=
  { zeugenSpeicher with bytes := fun a => if a.toNat - 4096 < fpHwW7Bild.length then fpHwW7Bild.getD (a.toNat - 4096) 0 else zeugenSpeicher.bytes a, ausfuehrbar := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4101) }

/-- Witness XMM file W7: `xmm8` low holds `42.0`, `xmm15` high holds
    a nonzero marker. -/
def fpHwW7Xmm : XmmDatei :=
  fun q => if q = XmmReg.xmm8 then vecJoin 0x4045000000000000 0
    else if q = XmmReg.xmm15 then vecJoin 0 0xDEADBEEFDEADBEEF
    else vecJoin 0 0

/-- Witness core W7: RIP at the image. -/
def fpHwW7Kern : Zustand :=
  { register := fun _ => BitVec.ofNat 64 0, flags := ⟨false, true, some false, false, false, false⟩, rip := BitVec.ofNat 64 4096, speicher := fpHwW7Speicher }

/-- Witness extended state W7: reset FP control word. -/
def fpHwW7T : FpZustand := ⟨fpHwW7Kern, fpHwW7Xmm, kontextReset⟩

/-- The source low half holds `42.0`. -/
theorem fpHwW7Tief8 :
    xmmTief fpHwW7T.xmm XmmReg.xmm8 = 0x4045000000000000 := by
  decide

/-- The destination upper half holds the marker. -/
theorem fpHwW7Hoch15 :
    xmmHoch fpHwW7T.xmm XmmReg.xmm15 = 0xDEADBEEFDEADBEEF := by
  decide

/-- Admitted profile on the witness state. -/
theorem fpHwW7Fp : fpEintritt fpHwW7T.fp = true := by
  decide

/-- Fetch yields the high-register copy form. -/
theorem fpHwW7_fetch :
    fpHwFetchDekodiert fpHwW7T =
      some (⟨.movsdRR .xmm15 .xmm8, 5⟩, []) := by
  have hbytes : fpHwGeholt fpHwW7T = fpHwEncodeMovsdRR .xmm15 .xmm8 ++ [] := by
    have hg : fpHwGeholt fpHwW7T = fpHwW7Bild := by decide
    simp only [hg, fpHwW7Bild, List.append_nil]
  have hrt := fpHwRoundtrip_movsdRR .xmm15 .xmm8 []
  have hlen : (fpHwEncodeMovsdRR .xmm15 .xmm8).length = 5 :=
    fpHwLen_movsdRR _ _
  rw [hlen] at hrt
  have hdec : fpHwDecode (fpHwGeholt fpHwW7T) =
      some (⟨.movsdRR .xmm15 .xmm8, 5⟩, []) := by
    rw [hbytes]
    exact hrt
  have hlenBild : (fpHwGeholt fpHwW7T).length = 5 := by
    have hg : fpHwGeholt fpHwW7T = fpHwW7Bild := by decide
    have hb : fpHwW7Bild.length = 5 := by decide
    rw [hg, hb]
  have h5 : laengeOk 5 = true := by decide
  have hperm : ausfuehrbarN fpHwW7T.kern.speicher fpHwW7T.kern.rip 5 =
      true := by
    decide
  unfold fpHwFetchDekodiert
  rw [hdec]
  simp only
  rw [hlenBild, h5, hperm]
  decide

/-- The conversion gate is open on the copy form. -/
theorem fpHwW7Gate :
    fpHwCvttZugelassen (.movsdRR .xmm15 .xmm8) fpHwW7T = true := by
  rfl

/-- Witness state after the copy. -/
def fpHwW7T1 : FpZustand :=
  { fpHwW7T with kern := { fpHwW7T.kern with rip := ripNach fpHwW7T.kern.rip 5 }, xmm := xmmSchreibeTief fpHwW7T.xmm XmmReg.xmm15 0x4045000000000000 }

/-- Reached byte-step: actual high-register copy bytes move the low
    half. -/
theorem fpHwW7_schritt :
    fpHwByteschritt fpHwW7T = .weiter fpHwW7T1 := by
  unfold fpHwByteschritt
  rw [fpHwW7_fetch]
  simp only
  rw [fpHwW7Gate]
  simp only
  have h5 : laengeOk 5 = true := by decide
  have hs := fpSchritt_movsdRR ⟨.movsdRR .xmm15 .xmm8, 5⟩ fpHwW7T
    .xmm15 .xmm8 h5 fpHwW7Fp rfl
  rw [fpHwW7Tief8] at hs
  simp only [hs, fpHwW7T1, if_true]

/-- Joint witness W7: the fetched high-register copy moves the low
    half and preserves the destination upper half. -/
theorem fpHwW7_hoch_ok :
    ∃ (t' : FpZustand),
      fpHwByteschritt fpHwW7T = .weiter t' ∧
      xmmTief t'.xmm XmmReg.xmm15 = 0x4045000000000000 ∧
      xmmHoch t'.xmm XmmReg.xmm15 = 0xDEADBEEFDEADBEEF := by
  refine ⟨fpHwW7T1, fpHwW7_schritt, ?_, ?_⟩
  · have h : xmmTief (xmmSchreibeTief fpHwW7T.xmm XmmReg.xmm15
        0x4045000000000000) XmmReg.xmm15 = 0x4045000000000000 :=
      xmmSchreibeTief_tief _ _ _
    have heq : fpHwW7T1.xmm = xmmSchreibeTief fpHwW7T.xmm XmmReg.xmm15
        0x4045000000000000 := rfl
    rw [heq]
    exact h
  · have h : xmmHoch (xmmSchreibeTief fpHwW7T.xmm XmmReg.xmm15
        0x4045000000000000) XmmReg.xmm15 =
        xmmHoch fpHwW7T.xmm XmmReg.xmm15 :=
      xmmSchreibeTief_hoch _ _ _
    have heq : fpHwW7T1.xmm = xmmSchreibeTief fpHwW7T.xmm XmmReg.xmm15
        0x4045000000000000 := rfl
    rw [heq, h, fpHwW7Hoch15]

/-- Witness image W8: a 9-byte store whose window truncates after
    the ModRM byte. -/
def fpHwW8Bild : List Byte := fpHwEncodeMovsdSpeichere .rax .xmm0 0

/-- Witness memory W8: the store image at 4096 with execute permission
    on only the first five bytes -- the window truncates mid-form. -/
def fpHwW8Speicher : Speicher :=
  { zeugenSpeicher with bytes := fun a => if a.toNat - 4096 < fpHwW8Bild.length then fpHwW8Bild.getD (a.toNat - 4096) 0 else zeugenSpeicher.bytes a, ausfuehrbar := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4101) }

/-- Witness core W8: RIP at the truncated image. -/
def fpHwW8Kern : Zustand :=
  { register := fun q => if q = Register.rax then BitVec.ofNat 64 8192 else BitVec.ofNat 64 0, flags := ⟨false, true, some false, false, false, false⟩, rip := BitVec.ofNat 64 4096, speicher := fpHwW8Speicher }

/-- Witness extended state W8: reset FP control word. -/
def fpHwW8T : FpZustand := ⟨fpHwW8Kern, fpHwW1Xmm, kontextReset⟩

/-- Joint witness W8: the window truncates inside the store form, so
    fetch -- hence the byte step -- refuses at the executable
    boundary. -/
theorem fpHwW8_grenze_verweigert :
    fpHwFetchDekodiert fpHwW8T = none ∧
      fpHwByteschritt fpHwW8T = .verweigert := by
  have hf : fpHwFetchDekodiert fpHwW8T = none := by decide
  refine ⟨hf, ?_⟩
  unfold fpHwByteschritt
  rw [hf]

/- CUTS: what is proved here and what is not.

   Proved: REX-aware canonical byte rows for SUBSD/MULSD/DIVSD
   (register and memory), UCOMISD (register and memory), CVTSI2SD and
   CVTTSD2SI (REX.W = 1 register forms), MOVSD (register, load,
   store) and ADDSD memory (register was lane 565), over all sixteen
   XMM registers and all sixteen GPRs, with an independent decoder
   over actual bytes, explicit refusals, the CVTTSD2SI
   silicon-agreement domain adapter, the gated byte step from actual
   executable memory, and the joint witnesses W1-W8 (two fetched
   arithmetic/conversion-to-store runs with real memory change,
   truncation on-domain, four refusal witnesses, high-register
   execution, boundary truncation).
   NOT proved, and not claimed:
   - No silicon correspondence: byte shapes (mandatory prefix before
     REX per Vol.2A 2-7f, 0F escape, opcodes 58/5C/59/5E/2E/2A/2C/
     10/11, ModRM mod = 11/10 with the pilot SIB rule) are STATED
     from the Intel SDM opcode pages as an implementation contract
     in the BYTE-PILOT.md style, never verified against hardware.
     Encoder round-trip consistency is not hardware correspondence.
   - NaN relation is class-level only: payload equality of computed
     results is never concluded (inherited gap of
     `Gleitprofil` §7 and `ScalarFloat` §6). SNaN has no model form
     (`Klasse` carries a single `.nan`): quieting/trapping and the
     masked QNaN-indefinite response (Vol.1 App.D Table D-1) are
     unmodelled; the UCOMISD rows hold under the admitted
     all-masks-set profile, where even SNaN yields the unordered
     flags with no trap.
   - Sticky MXCSR flags (bits 0-5) are unchecked and unmodelled:
     accumulation, clearing and reads have no definitions
     (inherited gap of `Gleitprofil` §2); `guard_sticky_offen`
     shows they do not close the slot.
   - Deliberate subset refusals (validator incompleteness, never
     wrong execution): arithmetic with REX.W = 1 (silicon ignores
     REX.W there); REX.W = 0 and memory-source conversions (the
     32-bit widths and memory sources have no accepted execution);
     COMISD (traps on quiet NaN, unmodelled); VEX/EVEX, packed
     lanes beyond lane 597, x87, FMA contraction, fast-math and
     short/displaced ModRM modes: syntactically absent, refused.
   - No source, checker, emitter or goal claim: the model-op link
     (`fpRechne` IS `gleitRechne`) is consumed from `ScalarFloat`
     §4, never restated; F-EQ stays excluded at the source
     (`FloatSourceObservations`: `Expr.eq` takes only `.int`, no
     source `Gleit` value is NaN); flags are the only comparison
     channel and NaN payloads never cross it.
   - No TSO/concurrency, cost/timing, ABI/loader/entry/budget or
     whole-image claim: everything is sequential over one
     `Speicher`; the unified dispatcher integration is owned by
     its consumer lanes (660/658), whose exact API (encoders,
     `fpHwDecode`, `fpHwByteschritt`, gate and adapter lemmas,
     pilot-disjointness pins) this file provides.
   - Rule 13 (inhabitation): no theorem here quantifies over the
     listed source-syntax types (`Vertrag`, `Stmt`, `Endblock`,
     `ErgExpr`, `Expr`, `Args`); `FpBefehl` is target syntax and
     `GleitOp` ranges over the model op. The joint non-degenerate
     evidence is W1 (`fpHwW1_div_speichert`) and W2
     (`fpHwW2_cvtsi_speichert`): reached fetched runs with real
     memory change, plus the planted refusal witnesses W3-bad, W5,
     W6 and W8.
-/

#print axioms fpHwRex
#print axioms fpHwRoundtrip_arithRR
#print axioms fpHwRoundtrip_ucomiRR
#print axioms fpHwRoundtrip_cvtsi
#print axioms fpHwRoundtrip_cvtt
#print axioms fpHwRoundtrip_movsdRR
#print axioms fpHwRoundtrip_addsdRM
#print axioms fpHwRoundtrip_subsdRM
#print axioms fpHwRoundtrip_mulsdRM
#print axioms fpHwRoundtrip_divsdRM
#print axioms fpHwRoundtrip_ucomiRM
#print axioms fpHwRoundtrip_movsdLade
#print axioms fpHwRoundtrip_movsdSpeichere
#print axioms fpHwDecode_rexZuerst_verweigert
#print axioms fpHwDecode_cvtsiW0_verweigert
#print axioms fpHwDecode_cvttW0_verweigert
#print axioms fpHwDecode_cvtsiSpeicher_verweigert
#print axioms fpHwDecode_cvttSpeicher_verweigert
#print axioms fpHwDecode_comisd_verweigert
#print axioms fpHwPilot_weist_subsdRR_zurueck
#print axioms fpHwPilot_weist_mulsdRM_zurueck
#print axioms fpHwPilot_weist_ucomiRR_zurueck
#print axioms fpHwPilot_weist_cvtsi_zurueck
#print axioms fpHwPilot_weist_cvtt_zurueck
#print axioms cvttAdapter_gueltig
#print axioms cvttHwGueltig_erfolg
#print axioms cvttHwGueltig_unendlich
#print axioms cvttHwGueltig_nan
#print axioms cvttHwGueltig_42
#print axioms fpHwFetchDekodiert_erfolg
#print axioms fpHwByteschritt_schritt
#print axioms fpHwByteschritt_cvttVerweigert
#print axioms fpHwByteschritt_profil_verweigert
#print axioms fpHwByteschritt_arithRR_rechnet
#print axioms fpHwByteschritt_arithRR_klasse
#print axioms fpHwByteschritt_arithRR_hoch
#print axioms fpHwSchritt_ucomisdRR_ungeordnet
#print axioms fpHwSchritt_ucomisdRR_gleich
#print axioms fpHwNan_nutzlast_klasse
#print axioms fpHwNan_ungeordnet
#print axioms fpHwSub_plusnull
#print axioms fpHwW1_div_speichert
#print axioms fpHwW2_cvtsi_speichert
#print axioms fpHwW3_cvtt_gueltig
#print axioms fpHwW3_cvtt_verweigert
#print axioms fpHwW4_ucomi_gleich
#print axioms fpHwW5_lade_verweigert
#print axioms fpHwW6_profil_verweigert
#print axioms fpHwW7_hoch_ok
#print axioms fpHwW8_grenze_verweigert

end Gabbro.Grammatik.X86
