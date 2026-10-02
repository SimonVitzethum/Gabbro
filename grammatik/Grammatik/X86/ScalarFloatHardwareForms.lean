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

/- CUTS: skeleton plus encoders; decoder, execution and witnesses open.
-/

#print axioms fpHwRex

end Gabbro.Grammatik.X86
