/-
  File:      Grammatik/X86/VectorIntegerHardwareForms.lean
  Subject:   Selected SSE2 packed-integer and 128-bit memory byte forms.

  Lane 686 (hardware completion): closes the selected packed-integer
  tier -- PADDB/W/D/Q, PAND/POR/PXOR, packed PSLLQ/PSRLQ (register
  count and imm8), MOVDQA/MOVDQU 128-bit load/store -- as canonical
  byte decode plus fetched execution on the shared XMM state. All
  lane arithmetic reuses the accepted `Vektor` functions; admission
  refines the accepted `VectorHardwareProfile` gate to the legacy
  SSE2 controls (no unconditional XCR0 prerequisite).

  Manual provenance (checked 2026-10-02, local
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
  Intel SDM 325462-093US September 2026, REFERENCES.json):
  opcode tables, saturating shift counts, #GP alignment, Type 1/4
  exception classes and per-entry flags are cited at each section.
-/
import Grammatik.X86.VectorCodec
import Grammatik.X86.VectorFootprints
import Grammatik.X86.ScalarFloat
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.AddressEncoding
import Grammatik.X86.VectorHardwareProfile

namespace Gabbro.Grammatik.X86

/-- Selected packed-integer and vector-memory rows: register
    arithmetic/logical (all four PADD widths, all three logicals),
    packed quadword shifts (register count and imm8), and the four
    128-bit load/store shapes. -/
inductive IntVecOp where
  | paddbRR (dst src : XmmReg)
  | paddwRR (dst src : XmmReg)
  | padddRR (dst src : XmmReg)
  | paddqRR (dst src : XmmReg)
  | pandRR (dst src : XmmReg)
  | porRR (dst src : XmmReg)
  | pxorRR (dst src : XmmReg)
  | psllqRR (dst cnt : XmmReg)
  | psrlqRR (dst cnt : XmmReg)
  | psllqImm (dst : XmmReg) (imm : Nat)
  | psrlqImm (dst : XmmReg) (imm : Nat)
  | movdqaLd (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | movdqaSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  | movdquLd (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | movdquSt (base : Register) (src : XmmReg) (disp : BitVec 32)
  deriving DecidableEq, Repr

/-- Canonical REX byte for one selected form (W=0, X=0, like the
    accepted `vectorRex`). -/
def intVecRexByte (rB bB : Nat) : Byte := natByte (64 + 4 * rB + bB)

/-! ## 1. Canonical byte encodings (stated from the Intel SDM opcode
  map, Vol. 2B: PADDB/W/D/Q `66 0F FC/FD/FE/D4 /r`, PAND `66 0F DB`,
  POR `66 0F EB`, PXOR `66 0F EF`, PSLLQ-reg `66 0F F3 /r`,
  PSRLQ-reg `66 0F D3 /r`, shift-imm8 `66 0F 73 /6|/2 ib`,
  MOVDQA `66 0F 6F/7F /r`, MOVDQU `F3 0F 6F/7F /r`, all CPUID SSE2;
  the memory rows use ModRM mod=10 base+disp32 with the pilot SIB
  rule, exactly like the accepted `fpEncodeMovsdLade`). -/

/-- Legacy mandatory prefix: `66` (102) for every selected row except
    the MOVDQU pair, which uses `F3` (243). -/
def intVecPrefix : IntVecOp → Nat
  | .movdquLd _ _ _ => 243
  | .movdquSt _ _ _ => 243
  | _ => 102

/-- Second opcode byte after the `0F` escape (`0F 73` group shares
    byte 115; the `/6` vs `/2` extension lives in ModRM). -/
def intVecSecond : IntVecOp → Nat
  | .paddbRR _ _ => 252
  | .paddwRR _ _ => 253
  | .padddRR _ _ => 254
  | .paddqRR _ _ => 212
  | .pandRR _ _ => 219
  | .porRR _ _ => 235
  | .pxorRR _ _ => 239
  | .psllqRR _ _ => 243
  | .psrlqRR _ _ => 211
  | .psllqImm _ _ => 115
  | .psrlqImm _ _ => 115
  | .movdqaLd _ _ _ => 111
  | .movdqaSt _ _ _ => 127
  | .movdquLd _ _ _ => 111
  | .movdquSt _ _ _ => 127

/-- Canonical byte encoding of one selected row (always with a
    canonical REX prefix, like the accepted `encodeVector`). -/
def encodeIntVec : IntVecOp → List Byte
  | op@(.paddbRR dst src) =>
    [intVecRexByte (xmmHigh dst) (xmmHigh src), natByte (intVecPrefix op),
      natByte 15, natByte (intVecSecond op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.paddwRR dst src) =>
    [intVecRexByte (xmmHigh dst) (xmmHigh src), natByte (intVecPrefix op),
      natByte 15, natByte (intVecSecond op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.padddRR dst src) =>
    [intVecRexByte (xmmHigh dst) (xmmHigh src), natByte (intVecPrefix op),
      natByte 15, natByte (intVecSecond op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.paddqRR dst src) =>
    [intVecRexByte (xmmHigh dst) (xmmHigh src), natByte (intVecPrefix op),
      natByte 15, natByte (intVecSecond op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.pandRR dst src) =>
    [intVecRexByte (xmmHigh dst) (xmmHigh src), natByte (intVecPrefix op),
      natByte 15, natByte (intVecSecond op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.porRR dst src) =>
    [intVecRexByte (xmmHigh dst) (xmmHigh src), natByte (intVecPrefix op),
      natByte 15, natByte (intVecSecond op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.pxorRR dst src) =>
    [intVecRexByte (xmmHigh dst) (xmmHigh src), natByte (intVecPrefix op),
      natByte 15, natByte (intVecSecond op), modrmReg (xmmLow dst) (xmmLow src)]
  | op@(.psllqRR dst cnt) =>
    [intVecRexByte (xmmHigh dst) (xmmHigh cnt), natByte (intVecPrefix op),
      natByte 15, natByte (intVecSecond op), modrmReg (xmmLow dst) (xmmLow cnt)]
  | op@(.psrlqRR dst cnt) =>
    [intVecRexByte (xmmHigh dst) (xmmHigh cnt), natByte (intVecPrefix op),
      natByte 15, natByte (intVecSecond op), modrmReg (xmmLow dst) (xmmLow cnt)]
  | op@(.psllqImm dst imm) =>
    [intVecRexByte 0 (xmmHigh dst), natByte (intVecPrefix op),
      natByte 15, natByte (intVecSecond op),
      modrmReg 6 (xmmLow dst), natByte (imm % 256)]
  | op@(.psrlqImm dst imm) =>
    [intVecRexByte 0 (xmmHigh dst), natByte (intVecPrefix op),
      natByte 15, natByte (intVecSecond op),
      modrmReg 2 (xmmLow dst), natByte (imm % 256)]
  | op@(.movdqaLd dst base d) =>
    let head := [intVecRexByte (xmmHigh dst) (regHigh base),
      natByte (intVecPrefix op), natByte 15, natByte (intVecSecond op),
      modrmMem (xmmLow dst) (regLow base)]
    if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
    else head ++ leBytes32 d
  | op@(.movdqaSt base src d) =>
    let head := [intVecRexByte (xmmHigh src) (regHigh base),
      natByte (intVecPrefix op), natByte 15, natByte (intVecSecond op),
      modrmMem (xmmLow src) (regLow base)]
    if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
    else head ++ leBytes32 d
  | op@(.movdquLd dst base d) =>
    let head := [intVecRexByte (xmmHigh dst) (regHigh base),
      natByte (intVecPrefix op), natByte 15, natByte (intVecSecond op),
      modrmMem (xmmLow dst) (regLow base)]
    if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
    else head ++ leBytes32 d
  | op@(.movdquSt base src d) =>
    let head := [intVecRexByte (xmmHigh src) (regHigh base),
      natByte (intVecPrefix op), natByte 15, natByte (intVecSecond op),
      modrmMem (xmmLow src) (regLow base)]
    if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
    else head ++ leBytes32 d

/-! ## 2. Packed quadword shift lanes with saturating counts.

  `PSLLQ`/`PSRLQ` (128-bit legacy SSE version, Vol. 2B 4-445/446 and
  4-469/470): `COUNT := COUNT_SRC[63:0]` -- only the low 64 bits of a
  128-bit count register are checked -- and `IF (COUNT > 63)` the
  whole 128-bit destination is zeroed, else each 64-bit lane shifts
  independently with zero fill. A count past the width SATURATES to
  zero; it is never masked (`COUNT mod 64`). Both lanes reuse the
  accepted `laneNat`/`vecMk` vocabulary; no scalar masked-count
  semantics is substituted. -/

/-- Packed quadword shift left: each 64-bit lane shifts by `c`, or the
    whole word is zero when `63 < c` (saturating, per the SDM). -/
def vecShlQ (v : Vektor) (c : Nat) : Vektor :=
  if 63 < c then 0
  else vecMk .b64 (fun i => laneNat .b64 v i * 2 ^ c)

/-- Packed quadword shift right: each 64-bit lane shifts by `c`, or the
    whole word is zero when `63 < c` (saturating, per the SDM). -/
def vecShrQ (v : Vektor) (c : Nat) : Vektor :=
  if 63 < c then 0
  else vecMk .b64 (fun i => laneNat .b64 v i / 2 ^ c)

/-- A saturated shift left is the zero word. -/
theorem vecShlQ_satt_null (v : Vektor) (c : Nat) (hc : 63 < c) :
    vecShlQ v c = 0 := by
  unfold vecShlQ
  rw [if_pos hc]

/-- A saturated shift left is all zero in every 64-bit lane
    (unconditionally: saturation zeroes the whole word). -/
theorem laneNat_shlQ_satt (v : Vektor) (c i : Nat) (hc : 63 < c) :
    laneNat .b64 (vecShlQ v c) i = 0 := by
  rw [vecShlQ_satt_null v c hc]
  unfold laneNat
  simp

/-- An admitted shift left is the modular lane shift. -/
theorem laneNat_shlQ (v : Vektor) (c : Nat) (i : Nat)
    (hc : ¬ 63 < c) (hi : i < laneCount .b64) :
    laneNat .b64 (vecShlQ v c) i =
      (laneNat .b64 v i * 2 ^ c) % 2 ^ 64 := by
  unfold vecShlQ
  rw [if_neg hc]
  have h64 : Breite.bits .b64 = 64 := rfl
  have h := laneGet_mk .b64 (fun i => laneNat .b64 v i * 2 ^ c) i hi
  rwa [h64] at h

/-- A saturated shift right is the zero word. -/
theorem vecShrQ_satt_null (v : Vektor) (c : Nat) (hc : 63 < c) :
    vecShrQ v c = 0 := by
  unfold vecShrQ
  rw [if_pos hc]

/-- A saturated shift right is all zero in every 64-bit lane
    (unconditionally: saturation zeroes the whole word). -/
theorem laneNat_shrQ_satt (v : Vektor) (c i : Nat) (hc : 63 < c) :
    laneNat .b64 (vecShrQ v c) i = 0 := by
  rw [vecShrQ_satt_null v c hc]
  unfold laneNat
  simp

/-- An admitted shift right is the lane quotient. -/
theorem laneNat_shrQ (v : Vektor) (c : Nat) (i : Nat)
    (hc : ¬ 63 < c) (hi : i < laneCount .b64) :
    laneNat .b64 (vecShrQ v c) i =
      (laneNat .b64 v i / 2 ^ c) % 2 ^ 64 := by
  unfold vecShrQ
  rw [if_neg hc]
  have h64 : Breite.bits .b64 = 64 := rfl
  have h := laneGet_mk .b64 (fun i => laneNat .b64 v i / 2 ^ c) i hi
  rwa [h64] at h

/-- SATURATE, NOT MASK: count 64 zeroes a nonzero word, where masked
    semantics (64 mod 64 = 0) would leave it unchanged. -/
theorem vecShlQ_satt_vs_maske :
    vecShlQ (BitVec.ofNat 128 0xFF) 64 = 0 ∧
      vecShrQ (BitVec.ofNat 128 0xFF00) 64 = 0 := by
  decide

/-- Boundary witness: shift left by one doubles each 64-bit lane. -/
theorem vecShlQ_eins :
    laneNat .b64 (vecShlQ (BitVec.ofNat 128 0x00000000000000010000000000000001) 1) 0 = 2 ∧
      laneNat .b64 (vecShlQ (BitVec.ofNat 128 0x00000000000000010000000000000001) 1) 1 = 2 := by
  decide

/-! ## 3. Canonical decoder over actual bytes.

  The decoder parses bytes, never encode-equality. Only the canonical
  REX prefix (`64 + 4*R + B`: W=0, X=0), then the legacy prefix (`66`
  or `F3`), the `0F` escape, the opcode byte and a ModRM: mod=3 for
  the register rows (reg=dst, r/m=src; for the `0F 73` group the reg
  field is the `/6` vs `/2` extension and r/m is the destination) and
  mod=2 base+disp32 with the pilot SIB rule for the load/store rows.
  Anything else refuses with `none`. -/

/-- A decoded selected instruction: the form plus its decode length
    (checked `1..15` data, exactly as the pilot `Decodiert`). -/
structure IntVecDec where
  op : IntVecOp
  laenge : Nat
  deriving DecidableEq, Repr

/-- REX extension bits of a canonical REX byte (W=0, X=0 only;
    every other first byte refuses). -/
def intVecRex (r : Nat) : Option (Nat × Nat) :=
  match r with
  | 64 => some (0, 0)
  | 65 => some (0, 1)
  | 68 => some (1, 0)
  | 69 => some (1, 1)
  | _ => none

/-- Decode one register-direct ModRM byte: mod must be 3, the reg
    field names the destination (REX.R extension), the r/m field the
    source (REX.B extension). -/
def decodeIntVecReg (rBit bBit opByte : Nat) :
    List Byte → Option (IntVecOp × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if byteNat m / 64 == 3 then
      match codeXmm (rBit * 8 + reg), codeXmm (bBit * 8 + rm) with
      | some dst, some src =>
        match opByte with
        | 252 => some ((.paddbRR dst src), rest)
        | 253 => some ((.paddwRR dst src), rest)
        | 254 => some ((.padddRR dst src), rest)
        | 212 => some ((.paddqRR dst src), rest)
        | 219 => some ((.pandRR dst src), rest)
        | 235 => some ((.porRR dst src), rest)
        | 239 => some ((.pxorRR dst src), rest)
        | 243 => some ((.psllqRR dst src), rest)
        | 211 => some ((.psrlqRR dst src), rest)
        | _ => none
      | _, _ => none
    else none

/-- Decode the `0F 73` immediate group: mod must be 3, the reg
    field is the `/6` (PSLLQ) vs `/2` (PSRLQ) extension with a zero
    REX.R bit, r/m is the destination (REX.B extension), then one
    imm8 byte follows. -/
def decodeIntVecImm (rBit bBit : Nat) :
    List Byte → Option (IntVecOp × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if byteNat m / 64 == 3 && rBit == 0 then
      match codeXmm (bBit * 8 + rm) with
      | none => none
      | some dst =>
        match rest with
        | [] => none
        | ib :: rest2 =>
          match reg with
          | 6 => some ((.psllqImm dst (byteNat ib)), rest2)
          | 2 => some ((.psrlqImm dst (byteNat ib)), rest2)
          | _ => none
    else none

/-- Decode a memory operand after the opcode: mod must be 2
    (base+disp32 with the pilot SIB rule); mod=3 (the
    register-register move) is refused by absence since only the
    load/store rows are selected. `al` selects the aligned
    (MOVDQA) vs unaligned (MOVDQU) shape; the opcode byte selects
    load (`6F`) vs store (`7F`). -/
def decodeIntVecMem (rBit bBit : Nat) (al : Bool) (opByte : Nat) :
    List Byte → Option (IntVecDec × List Byte)
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
            | some (d, rest3) =>
              match codeXmm (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
              | some xx, some base =>
                match opByte, al with
                | 111, true => some ((⟨.movdqaLd xx base d, 10⟩ : IntVecDec), rest3)
                | 127, true => some ((⟨.movdqaSt base xx d, 10⟩ : IntVecDec), rest3)
                | 111, false => some ((⟨.movdquLd xx base d, 10⟩ : IntVecDec), rest3)
                | 127, false => some ((⟨.movdquSt base xx d, 10⟩ : IntVecDec), rest3)
                | _, _ => none
              | _, _ => none
          else none
      else
        match parseLe32 rest with
        | none => none
        | some (d, rest3) =>
          match codeXmm (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
          | some xx, some base =>
            match opByte, al with
            | 111, true => some ((⟨.movdqaLd xx base d, 9⟩ : IntVecDec), rest3)
            | 127, true => some ((⟨.movdqaSt base xx d, 9⟩ : IntVecDec), rest3)
            | 111, false => some ((⟨.movdquLd xx base d, 9⟩ : IntVecDec), rest3)
            | 127, false => some ((⟨.movdquSt base xx d, 9⟩ : IntVecDec), rest3)
            | _, _ => none
          | _, _ => none
    else none

/-- Decode after the canonical REX prefix: the legacy prefix,
    then the `0F` escape, then the opcode byte, then ModRM. -/
def decodeIntVecNach (rBit bBit : Nat) :
    List Byte → Option (IntVecDec × List Byte)
  | [] => none
  | p1 :: rest =>
    if byteNat p1 == 102 then
      match rest with
      | [] => none
      | p2 :: rest2 =>
        if byteNat p2 == 15 then
          match rest2 with
          | [] => none
          | op :: rest3 =>
            match byteNat op with
            | 252 => match decodeIntVecReg rBit bBit 252 rest3 with
              | some (o, r) => some ((⟨o, 5⟩ : IntVecDec), r)
              | none => none
            | 253 => match decodeIntVecReg rBit bBit 253 rest3 with
              | some (o, r) => some ((⟨o, 5⟩ : IntVecDec), r)
              | none => none
            | 254 => match decodeIntVecReg rBit bBit 254 rest3 with
              | some (o, r) => some ((⟨o, 5⟩ : IntVecDec), r)
              | none => none
            | 212 => match decodeIntVecReg rBit bBit 212 rest3 with
              | some (o, r) => some ((⟨o, 5⟩ : IntVecDec), r)
              | none => none
            | 219 => match decodeIntVecReg rBit bBit 219 rest3 with
              | some (o, r) => some ((⟨o, 5⟩ : IntVecDec), r)
              | none => none
            | 235 => match decodeIntVecReg rBit bBit 235 rest3 with
              | some (o, r) => some ((⟨o, 5⟩ : IntVecDec), r)
              | none => none
            | 239 => match decodeIntVecReg rBit bBit 239 rest3 with
              | some (o, r) => some ((⟨o, 5⟩ : IntVecDec), r)
              | none => none
            | 243 => match decodeIntVecReg rBit bBit 243 rest3 with
              | some (o, r) => some ((⟨o, 5⟩ : IntVecDec), r)
              | none => none
            | 211 => match decodeIntVecReg rBit bBit 211 rest3 with
              | some (o, r) => some ((⟨o, 5⟩ : IntVecDec), r)
              | none => none
            | 115 => match decodeIntVecImm rBit bBit rest3 with
              | some (o, r) => some ((⟨o, 6⟩ : IntVecDec), r)
              | none => none
            | 111 => decodeIntVecMem rBit bBit true 111 rest3
            | 127 => decodeIntVecMem rBit bBit true 127 rest3
            | _ => none
        else none
    else if byteNat p1 == 243 then
      match rest with
      | [] => none
      | p2 :: rest2 =>
        if byteNat p2 == 15 then
          match rest2 with
          | [] => none
          | op :: rest3 =>
            match byteNat op with
            | 111 => decodeIntVecMem rBit bBit false 111 rest3
            | 127 => decodeIntVecMem rBit bBit false 127 rest3
            | _ => none
        else none
    else none

/-- Top-level selected decode: the REX prefix selects the extension
    bits; anything without a canonical REX refuses. -/
def decodeIntVec : List Byte → Option (IntVecDec × List Byte)
  | [] => none
  | r :: tail =>
    match intVecRex (byteNat r) with
    | none => none
    | some (rBit, bBit) => decodeIntVecNach rBit bBit tail

/-! ## 4. Encode/decode round trips over every selected row.

  Decoding inverts encoding on every row over any suffix; the
  decoded length is the consumed prefix length. -/

/-- Round trip for PADDB, over any suffix. -/
theorem roundtrip_paddb (dst src : XmmReg) (suffix : List Byte) :
    decodeIntVec (encodeIntVec (.paddbRR dst src) ++ suffix) =
      some ((⟨.paddbRR dst src, 5⟩ : IntVecDec), suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PADDW, over any suffix. -/
theorem roundtrip_paddw (dst src : XmmReg) (suffix : List Byte) :
    decodeIntVec (encodeIntVec (.paddwRR dst src) ++ suffix) =
      some ((⟨.paddwRR dst src, 5⟩ : IntVecDec), suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PADDD, over any suffix. -/
theorem roundtrip_paddd (dst src : XmmReg) (suffix : List Byte) :
    decodeIntVec (encodeIntVec (.padddRR dst src) ++ suffix) =
      some ((⟨.padddRR dst src, 5⟩ : IntVecDec), suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PADDQ, over any suffix. -/
theorem roundtrip_paddq128 (dst src : XmmReg) (suffix : List Byte) :
    decodeIntVec (encodeIntVec (.paddqRR dst src) ++ suffix) =
      some ((⟨.paddqRR dst src, 5⟩ : IntVecDec), suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PAND, over any suffix. -/
theorem roundtrip_pand (dst src : XmmReg) (suffix : List Byte) :
    decodeIntVec (encodeIntVec (.pandRR dst src) ++ suffix) =
      some ((⟨.pandRR dst src, 5⟩ : IntVecDec), suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for POR, over any suffix. -/
theorem roundtrip_por (dst src : XmmReg) (suffix : List Byte) :
    decodeIntVec (encodeIntVec (.porRR dst src) ++ suffix) =
      some ((⟨.porRR dst src, 5⟩ : IntVecDec), suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PXOR, over any suffix. -/
theorem roundtrip_pxor128 (dst src : XmmReg) (suffix : List Byte) :
    decodeIntVec (encodeIntVec (.pxorRR dst src) ++ suffix) =
      some ((⟨.pxorRR dst src, 5⟩ : IntVecDec), suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for PSLLQ with a register count, over any suffix. -/
theorem roundtrip_psllqRR (dst cnt : XmmReg) (suffix : List Byte) :
    decodeIntVec (encodeIntVec (.psllqRR dst cnt) ++ suffix) =
      some ((⟨.psllqRR dst cnt, 5⟩ : IntVecDec), suffix) := by
  cases dst <;> cases cnt <;> rfl

/-- Round trip for PSRLQ with a register count, over any suffix. -/
theorem roundtrip_psrlqRR (dst cnt : XmmReg) (suffix : List Byte) :
    decodeIntVec (encodeIntVec (.psrlqRR dst cnt) ++ suffix) =
      some ((⟨.psrlqRR dst cnt, 5⟩ : IntVecDec), suffix) := by
  cases dst <;> cases cnt <;> rfl

/-- Round trip for PSLLQ with an imm8 count, over any suffix:
    the decoded immediate is the low byte of the given count. -/
theorem roundtrip_psllqImm (dst : XmmReg) (imm : Nat)
    (suffix : List Byte) :
    decodeIntVec (encodeIntVec (.psllqImm dst imm) ++ suffix) =
      some ((⟨.psllqImm dst (imm % 256), 6⟩ : IntVecDec), suffix) := by
  cases dst <;>
    simp [encodeIntVec, decodeIntVec, decodeIntVecNach, decodeIntVecImm,
      intVecRex, intVecRexByte, intVecPrefix, intVecSecond, codeXmm,
      xmmCode, xmmHigh, xmmLow, modrmReg, natByte, byteNat]

/-- Round trip for PSRLQ with an imm8 count, over any suffix. -/
theorem roundtrip_psrlqImm (dst : XmmReg) (imm : Nat)
    (suffix : List Byte) :
    decodeIntVec (encodeIntVec (.psrlqImm dst imm) ++ suffix) =
      some ((⟨.psrlqImm dst (imm % 256), 6⟩ : IntVecDec), suffix) := by
  cases dst <;>
    simp [encodeIntVec, decodeIntVec, decodeIntVecNach, decodeIntVecImm,
      intVecRex, intVecRexByte, intVecPrefix, intVecSecond, codeXmm,
      xmmCode, xmmHigh, xmmLow, modrmReg, natByte, byteNat]

set_option maxHeartbeats 4000000 in
/-- Round trip for the MOVDQA load, both SIB shapes. -/
theorem roundtrip_movdqaLd (dst : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeIntVec (encodeIntVec (.movdqaLd dst base d) ++ suffix) =
      some ((⟨.movdqaLd dst base d,
        (encodeIntVec (.movdqaLd dst base d)).length⟩ : IntVecDec),
        suffix) := by
  cases dst <;> cases base <;>
    simp_all [encodeIntVec, decodeIntVec, decodeIntVecNach,
      decodeIntVecMem, intVecRex, intVecRexByte, intVecPrefix,
      intVecSecond, codeXmm, codeReg, xmmCode, xmmHigh, xmmLow,
      regCode, regHigh, regLow, modrmMem, parseLe32_leBytes32,
      length_leBytes32, natByte, byteNat]

set_option maxHeartbeats 4000000 in
/-- Round trip for the MOVDQA store, both SIB shapes. -/
theorem roundtrip_movdqaSt (base : Register) (src : XmmReg)
    (d : BitVec 32) (suffix : List Byte) :
    decodeIntVec (encodeIntVec (.movdqaSt base src d) ++ suffix) =
      some ((⟨.movdqaSt base src d,
        (encodeIntVec (.movdqaSt base src d)).length⟩ : IntVecDec),
        suffix) := by
  cases base <;> cases src <;>
    simp_all [encodeIntVec, decodeIntVec, decodeIntVecNach,
      decodeIntVecMem, intVecRex, intVecRexByte, intVecPrefix,
      intVecSecond, codeXmm, codeReg, xmmCode, xmmHigh, xmmLow,
      regCode, regHigh, regLow, modrmMem, parseLe32_leBytes32,
      length_leBytes32, natByte, byteNat]

set_option maxHeartbeats 4000000 in
/-- Round trip for the MOVDQU load, both SIB shapes. -/
theorem roundtrip_movdquLd (dst : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decodeIntVec (encodeIntVec (.movdquLd dst base d) ++ suffix) =
      some ((⟨.movdquLd dst base d,
        (encodeIntVec (.movdquLd dst base d)).length⟩ : IntVecDec),
        suffix) := by
  cases dst <;> cases base <;>
    simp_all [encodeIntVec, decodeIntVec, decodeIntVecNach,
      decodeIntVecMem, intVecRex, intVecRexByte, intVecPrefix,
      intVecSecond, codeXmm, codeReg, xmmCode, xmmHigh, xmmLow,
      regCode, regHigh, regLow, modrmMem, parseLe32_leBytes32,
      length_leBytes32, natByte, byteNat]

set_option maxHeartbeats 4000000 in
/-- Round trip for the MOVDQU store, both SIB shapes. -/
theorem roundtrip_movdquSt (base : Register) (src : XmmReg)
    (d : BitVec 32) (suffix : List Byte) :
    decodeIntVec (encodeIntVec (.movdquSt base src d) ++ suffix) =
      some ((⟨.movdquSt base src d,
        (encodeIntVec (.movdquSt base src d)).length⟩ : IntVecDec),
        suffix) := by
  cases base <;> cases src <;>
    simp_all [encodeIntVec, decodeIntVec, decodeIntVecNach,
      decodeIntVecMem, intVecRex, intVecRexByte, intVecPrefix,
      intVecSecond, codeXmm, codeReg, xmmCode, xmmHigh, xmmLow,
      regCode, regHigh, regLow, modrmMem, parseLe32_leBytes32,
      length_leBytes32, natByte, byteNat]

/-! ## 5. Decoder refusals and producer agreement.

  Every non-selected shape refuses explicitly: missing or
  non-canonical REX, unknown opcodes, truncated inputs, a memory
  ModRM where only register rows are selected (and vice versa), a
  memory count operand for the shifts (only register counts and
  imm8 are covered), a set REX.R bit on the `0F 73` group, VEX
  prefixes and bare escapes. The two rows shared with the accepted
  `decodeVector` (PXOR, PADDQ) decode identically. -/

/-- No REX prefix, no decode. -/
theorem intVec_nichts_ohneRex :
    decodeIntVec [natByte 102, natByte 15, natByte 252,
      natByte 192] = none := rfl

/-- A REX.W prefix is outside the canonical subset and refuses. -/
theorem intVec_nichts_rexW :
    decodeIntVec [natByte 72, natByte 102, natByte 15, natByte 252,
      natByte 192] = none := rfl

/-- An unknown opcode byte refuses. -/
theorem intVec_nichts_opcode :
    decodeIntVec [natByte 64, natByte 102, natByte 15, natByte 0,
      natByte 192] = none := rfl

/-- A lone REX prefix refuses. -/
theorem intVec_nichts_nurRex :
    decodeIntVec [natByte 64] = none := rfl

/-- REX plus legacy prefix only refuses. -/
theorem intVec_nichts_kurz :
    decodeIntVec [natByte 64, natByte 102] = none := rfl

/-- REX, prefix and escape without opcode refuses. -/
theorem intVec_nichts_ohneOpcode :
    decodeIntVec [natByte 64, natByte 102, natByte 15] = none := rfl

/-- A memory ModRM on an arithmetic opcode refuses: only the
    register rows of PADDB/W/D/Q are selected. -/
theorem intVec_nichts_modMem_fuerPadd :
    decodeIntVec [natByte 64, natByte 102, natByte 15, natByte 252,
      natByte 128] = none := by
  rfl

/-- A register ModRM on a load opcode refuses: only the load/store
    rows of MOVDQA/MOVDQU are selected, never the register move. -/
theorem intVec_nichts_modReg_fuerLade :
    decodeIntVec [natByte 64, natByte 102, natByte 15, natByte 111,
      natByte 192] = none := rfl

/-- A memory count operand for PSLLQ refuses: only register counts
    and imm8 are covered. -/
theorem intVec_nichts_speicherZaehler :
    decodeIntVec [natByte 64, natByte 102, natByte 15, natByte 243,
      natByte 128] = none := rfl

/-- A set REX.R bit on the `0F 73` group refuses (the reg field is
    the `/6` vs `/2` extension, extended by nothing). -/
theorem intVec_nichts_immRexR :
    decodeIntVec [natByte 68, natByte 102, natByte 15, natByte 115,
      natByte 240, natByte 8] = none := rfl

/-- A `0F 73` group ModRM without its imm8 byte refuses. -/
theorem intVec_nichts_immAbgeschnitten :
    decodeIntVec [natByte 64, natByte 102, natByte 15, natByte 115,
      natByte 240] = none := rfl

/-- A VEX prefix refuses. -/
theorem intVec_nichts_vex :
    decodeIntVec [natByte 197, natByte 240, natByte 239,
      natByte 192] = none := rfl

/-- A bare `0F` escape without REX and legacy prefix refuses. -/
theorem intVec_nichts_bare0F :
    decodeIntVec [natByte 15, natByte 131, natByte 0, natByte 0,
      natByte 0, natByte 0] = none := rfl

/-- The accepted FP bytes refuse here (F2 prefix, never selected). -/
theorem intVec_weist_fp_zurueck (dst src : XmmReg) :
    decodeIntVec (fpEncodeMovsdRR dst src) = none := by
  cases dst <;> cases src <;> rfl

/-- The accepted pilot bytes refuse here (no canonical REX). -/
theorem intVec_weist_pilot_zurueck :
    decodeIntVec (encode .ret) = none := by
  rfl

/-- SHARED ROW: the accepted PXOR bytes decode identically here. -/
theorem intVec_decode_pxor_agree (dst src : XmmReg)
    (suffix : List Byte) :
    decodeIntVec (encodeVector (.pxorRR dst src) ++ suffix) =
      some ((⟨.pxorRR dst src, 5⟩ : IntVecDec), suffix) := by
  have h : encodeVector (.pxorRR dst src) =
      encodeIntVec (.pxorRR dst src) := rfl
  rw [h]
  exact roundtrip_pxor128 dst src suffix

/-- SHARED ROW: the accepted PADDQ bytes decode identically here. -/
theorem intVec_decode_paddq_agree (dst src : XmmReg)
    (suffix : List Byte) :
    decodeIntVec (encodeVector (.paddqRR dst src) ++ suffix) =
      some ((⟨.paddqRR dst src, 5⟩ : IntVecDec), suffix) := by
  have h : encodeVector (.paddqRR dst src) =
      encodeIntVec (.paddqRR dst src) := rfl
  rw [h]
  exact roundtrip_paddq128 dst src suffix

/-! ## 6. Unified-dispatcher disjointness.

  The accepted unified decoder `decodeExt` refuses every selected
  canonical row: no pilot, narrow, muldiv, shift, SETcc, CMOVcc, FP
  or vector arm accepts them, so a consumer can chain this decoder
  after `decodeExt` without shadowing any existing form (and without
  any existing form shadowing the new rows). Each pin is one
  opcode group. -/

/-- The unified dispatcher refuses the PADDB row. -/
theorem intVec_ext_weist_paddb_zurueck :
    decodeExt (encodeIntVec (.paddbRR .xmm0 .xmm1)) = none := by
  decide

/-- The unified dispatcher refuses the PAND row. -/
theorem intVec_ext_weist_pand_zurueck :
    decodeExt (encodeIntVec (.pandRR .xmm0 .xmm1)) = none := by
  decide

/-- The unified dispatcher refuses the POR row. -/
theorem intVec_ext_weist_por_zurueck :
    decodeExt (encodeIntVec (.porRR .xmm0 .xmm1)) = none := by
  decide

/-- The unified dispatcher refuses the PSLLQ register-count row. -/
theorem intVec_ext_weist_psllqRR_zurueck :
    decodeExt (encodeIntVec (.psllqRR .xmm0 .xmm1)) = none := by
  decide

/-- The unified dispatcher refuses the PSLLQ imm8 row. -/
theorem intVec_ext_weist_psllqImm_zurueck :
    decodeExt (encodeIntVec (.psllqImm .xmm2 8)) = none := by
  decide

/-- The unified dispatcher refuses the MOVDQA load row. -/
theorem intVec_ext_weist_movdqaLd_zurueck :
    decodeExt (encodeIntVec (.movdqaLd .xmm0 .rax 0)) = none := by
  decide

/-- The unified dispatcher refuses the MOVDQU load row. -/
theorem intVec_ext_weist_movdquLd_zurueck :
    decodeExt (encodeIntVec (.movdquLd .xmm0 .rax 0)) = none := by
  decide

/-! ## 7. Legacy SSE2 admission: the correct selected-profile gate.

  Per the manual, a legacy SSE instruction faults with #UD exactly
  when CR0.EM is set, CR4.OSFXSR is clear, a LOCK prefix is used, or
  the CPUID feature flag is clear, and with #NM when CR0.TS is set
  (Type 4 class exception conditions, Vol. 2A Table 2-21/2-18
  region, extracted lines 34747-34760). The XCR0 check applies only
  to VEX-encoded (AVX) forms (`If XCR0[2:1] != 11b` is listed under
  the VEX prefix only), so XCR0 is NOT an unconditional
  architectural prerequisite for the selected legacy SSE2 rows.
  The accepted `vektorHwZugelassen` gate (lane 674) additionally
  requires XCR0 SSE readiness: a safe stronger gate, preserved as
  such below -- its over-strength is never claimed to be a hardware
  fault. OS configuration and context-preservation code remain user
  logic: these are checked inputs, never assumed-correct behaviour. -/

/-- Control-register freedom for legacy SSE: no emulation, no task
    switch, OS FXSAVE/FXRSTOR support enabled. No XCR0 conjunct. -/
def kontrollSseLegacyFrei (k : KontrollBild) : Bool :=
  (!k.cr0Em) && (!k.cr0Ts) && k.cr4Osfxsr

/-- Checked enabled-state readiness for legacy SSE2: silicon SSE2,
    control freedom, OS bit. No XCR0 input at all. -/
def hwSse2LegacyBereit (cpu : CpuMerkmal) (k : KontrollBild)
    (b : BereitProfil) : Bool :=
  cpu.hatSse2 && kontrollSseLegacyFrei k && b.osXmm

/-- Tier admission: the finite `paketInt128` admission AND the legacy
    readiness. Either side alone admits nothing. -/
def vektorLegacyZugelassen (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (k : KontrollBild) : Bool :=
  merkmalZugelassen hw b .paketInt128 && hwSse2LegacyBereit cpu k b

/-- SAFE REFINEMENT: the accepted stronger gate implies the legacy
    gate, so every `stepVectorHw` admission carries over. The old
    gate stays valid (stronger); its over-strength is stated as a
    safe over-approximation, never as a hardware fault. -/
theorem vektorLegacy_verfeinert (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (h : vektorHwZugelassen hw b cpu x k = true) :
    vektorLegacyZugelassen hw b cpu k = true := by
  have hm := vektorHw_braucht_merkmal hw b cpu x k h
  have hcpu := vektorHw_braucht_cpu hw b cpu x k h
  have hkont := vektorHw_braucht_kontrolle hw b cpu x k h
  have hos := vektorHw_verfeinert hw b cpu x k h
  simp only [vektorLegacyZugelassen, hwSse2LegacyBereit,
    kontrollSseLegacyFrei, vecEintritt] at hm hcpu hos ⊢
  simp only [kontrollSseFrei] at hkont
  simp only [Bool.and_eq_true] at hm hcpu hkont hos ⊢
  exact ⟨hm, ⟨⟨hcpu, hkont⟩, hos⟩⟩

/-- STRICTNESS: legacy admission holds where the old gate refuses
    (XCR0 SSE bit clear, everything else ready). This exhibits the
    refinement as strict without faulting the old gate: the old gate
    remains the safe choice wherever it admits. -/
theorem vektorLegacy_strikt :
    vektorLegacyZugelassen basisHw vecZeugeBereit basisCpu
        basisKontrolle = true ∧
      vektorHwZugelassen basisHw vecZeugeBereit basisCpu
        ⟨true, false, false⟩ basisKontrolle = false := by
  exact ⟨by decide, by decide⟩

/-- Missing silicon SSE2 refuses legacy admission. -/
theorem vektorLegacy_ohne_cpu (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (k : KontrollBild)
    (hcpu : cpu.hatSse2 = false) :
    vektorLegacyZugelassen hw b cpu k = false := by
  unfold vektorLegacyZugelassen hwSse2LegacyBereit
  rw [hcpu]
  simp

/-- Set control bits (emulation or task-switch) refuse. -/
theorem vektorLegacy_ohne_kontrolle (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (k : KontrollBild)
    (hk : kontrollSseLegacyFrei k = false) :
    vektorLegacyZugelassen hw b cpu k = false := by
  unfold vektorLegacyZugelassen hwSse2LegacyBereit
  rw [hk]
  simp

/-- A cleared OS vector-state bit refuses. -/
theorem vektorLegacy_ohne_osxmm (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (k : KontrollBild)
    (hos : b.osXmm = false) :
    vektorLegacyZugelassen hw b cpu k = false := by
  unfold vektorLegacyZugelassen hwSse2LegacyBereit
  rw [hos]
  simp

/-! ## 8. Selected byte-execution on the shared XMM state.

  `stepIntVec` steps ONLY the §1 rows on the SAME `FpZustand` the
  accepted scalar and vector steps use. Guards, in order: decode
  length (`laengeOk`, checked data), legacy tier admission
  (§7, validator refusal), then the form. Register arithmetic
  reuses the accepted `vecAdd` at all four widths (modular per
  lane, no inter-lane carry); logicals reuse `vecAnd`/`vecOr`/
  `vecXor` at `.b64` (bitwise, hence width-free); shifts reuse the
  §2 saturating lanes with the low 64 bits of the count register
  (only the low 64 bits of a 128-bit count are checked, per the
  SDM); loads/stores go through the two ordered canonical chunk
  accesses (`vecRead`/`vecWrite`), with the #GP classification for
  the aligned shape. Flags, GPRs and every other XMM register are
  untouched; legacy upper bits beyond 128 are unmodelled (CUTS).
  `none` is an explicit refusal, never a silent substitution. -/

/-- Single selected step; `none` is an explicit refusal (bad length,
    refused legacy admission, #GP classification, or a failed
    memory access). -/
def stepIntVec (d : IntVecDec) (t : FpZustand) (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) :
    Option FpZustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    match vektorLegacyZugelassen hw b cpu k with
    | false => none
    | true =>
      let nach := ripNach t.kern.rip d.laenge
      match d.op with
      | .paddbRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecAdd .b8 (t.xmm dst) (t.xmm src)) }
      | .paddwRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecAdd .b16 (t.xmm dst) (t.xmm src)) }
      | .padddRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecAdd .b32 (t.xmm dst) (t.xmm src)) }
      | .paddqRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecAdd .b64 (t.xmm dst) (t.xmm src)) }
      | .pandRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecAnd .b64 (t.xmm dst) (t.xmm src)) }
      | .porRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecOr .b64 (t.xmm dst) (t.xmm src)) }
      | .pxorRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecXor .b64 (t.xmm dst) (t.xmm src)) }
      | .psllqRR dst cnt =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecShlQ (t.xmm dst) (vLo (t.xmm cnt)).toNat) }
      | .psrlqRR dst cnt =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecShrQ (t.xmm dst) (vLo (t.xmm cnt)).toNat) }
      | .psllqImm dst imm =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecShlQ (t.xmm dst) imm) }
      | .psrlqImm dst imm =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecShrQ (t.xmm dst) imm) }
      | .movdqaLd dst base disp =>
        let a := effAddr t.kern base disp
        match vektorGpFehler a .ausgerichtet with
        | true => none
        | false =>
          match vecRead t.kern.speicher a with
          | none => none
          | some v => some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst v }
      | .movdqaSt base src disp =>
        let a := effAddr t.kern base disp
        match vektorGpFehler a .ausgerichtet with
        | true => none
        | false =>
          match vecWrite t.kern.speicher a (t.xmm src) with
          | none => none
          | some m' => some { t with kern := { t.kern with rip := nach, speicher := m' } }
      | .movdquLd dst base disp =>
        let a := effAddr t.kern base disp
        match vecRead t.kern.speicher a with
        | none => none
        | some v => some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst v }
      | .movdquSt base src disp =>
        let a := effAddr t.kern base disp
        match vecWrite t.kern.speicher a (t.xmm src) with
        | none => none
        | some m' => some { t with kern := { t.kern with rip := nach, speicher := m' } }

/-! ## 9. Per-row step equations for the register rows.

  Each equation pins the exact successor: RIP past the decoded
  length, the destination XMM holding the accepted lane word. -/

/-- `paddb`: the destination holds the accepted byte-lane sum. -/
theorem stepIntVec_paddb (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .paddbRR dst src) : stepIntVec d t hw b cpu k = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecAdd .b8 (t.xmm dst) (t.xmm src)) } := by
  unfold stepIntVec
  simp [hok, hgate, h]

/-- `paddw`: the destination holds the accepted word-lane sum. -/
theorem stepIntVec_paddw (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .paddwRR dst src) : stepIntVec d t hw b cpu k = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecAdd .b16 (t.xmm dst) (t.xmm src)) } := by
  unfold stepIntVec
  simp [hok, hgate, h]

/-- `paddd`: the destination holds the accepted doubleword-lane sum. -/
theorem stepIntVec_paddd (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .padddRR dst src) : stepIntVec d t hw b cpu k = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecAdd .b32 (t.xmm dst) (t.xmm src)) } := by
  unfold stepIntVec
  simp [hok, hgate, h]

/-- `paddq`: the destination holds the accepted quadword-lane sum. -/
theorem stepIntVec_paddq (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .paddqRR dst src) : stepIntVec d t hw b cpu k = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecAdd .b64 (t.xmm dst) (t.xmm src)) } := by
  unfold stepIntVec
  simp [hok, hgate, h]

/-- `pand`: the destination holds the accepted lane conjunction. -/
theorem stepIntVec_pand (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .pandRR dst src) : stepIntVec d t hw b cpu k = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecAnd .b64 (t.xmm dst) (t.xmm src)) } := by
  unfold stepIntVec
  simp [hok, hgate, h]

/-- `por`: the destination holds the accepted lane disjunction. -/
theorem stepIntVec_por (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .porRR dst src) : stepIntVec d t hw b cpu k = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecOr .b64 (t.xmm dst) (t.xmm src)) } := by
  unfold stepIntVec
  simp [hok, hgate, h]

/-- `pxor`: the destination holds the accepted lane xor. -/
theorem stepIntVec_pxor (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .pxorRR dst src) : stepIntVec d t hw b cpu k = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecXor .b64 (t.xmm dst) (t.xmm src)) } := by
  unfold stepIntVec
  simp [hok, hgate, h]

/-- `psllq` with a register count: the destination holds the
    accepted saturated shift by the low 64 bits of the count. -/
theorem stepIntVec_psllqRR (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst cnt : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .psllqRR dst cnt) : stepIntVec d t hw b cpu k = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecShlQ (t.xmm dst) (vLo (t.xmm cnt)).toNat) } := by
  unfold stepIntVec
  simp [hok, hgate, h]

/-- `psrlq` with a register count: the destination holds the
    accepted saturated shift by the low 64 bits of the count. -/
theorem stepIntVec_psrlqRR (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst cnt : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .psrlqRR dst cnt) : stepIntVec d t hw b cpu k = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecShrQ (t.xmm dst) (vLo (t.xmm cnt)).toNat) } := by
  unfold stepIntVec
  simp [hok, hgate, h]

/-- `psllq` with an imm8 count. -/
theorem stepIntVec_psllqImm (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst : XmmReg) (imm : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .psllqImm dst imm) : stepIntVec d t hw b cpu k = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecShlQ (t.xmm dst) imm) } := by
  unfold stepIntVec
  simp [hok, hgate, h]

/-- `psrlq` with an imm8 count. -/
theorem stepIntVec_psrlqImm (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst : XmmReg) (imm : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .psrlqImm dst imm) : stepIntVec d t hw b cpu k = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecShrQ (t.xmm dst) imm) } := by
  unfold stepIntVec
  simp [hok, hgate, h]

/-! ## 10. Per-row step equations for the memory rows, and refusals.

  Loads carry the read word into the destination XMM; stores carry
  the written memory. The #GP classification and the failed access
  each refuse explicitly. -/

/-- `movdqa` load: the destination holds the read word. -/
theorem stepIntVec_movdqaLd (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Vektor) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .movdqaLd dst base disp) (hgp : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = false) (hrd : vecRead t.kern.speicher (effAddr t.kern base disp) = some v) : stepIntVec d t hw b cpu k = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst v } := by
  unfold stepIntVec
  simp [hok, hgate, h, hgp, hrd]

/-- `movdqa` store: memory holds the written word. -/
theorem stepIntVec_movdqaSt (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (base : Register) (src : XmmReg) (disp : BitVec 32) (m' : Speicher) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .movdqaSt base src disp) (hgp : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = false) (hwr : vecWrite t.kern.speicher (effAddr t.kern base disp) (t.xmm src) = some m') : stepIntVec d t hw b cpu k = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge, speicher := m' } } := by
  unfold stepIntVec
  simp [hok, hgate, h, hgp, hwr]

/-- `movdqu` load: the destination holds the read word. -/
theorem stepIntVec_movdquLd (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Vektor) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .movdquLd dst base disp) (hrd : vecRead t.kern.speicher (effAddr t.kern base disp) = some v) : stepIntVec d t hw b cpu k = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst v } := by
  unfold stepIntVec
  simp [hok, hgate, h, hrd]

/-- `movdqu` store: memory holds the written word. -/
theorem stepIntVec_movdquSt (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (base : Register) (src : XmmReg) (disp : BitVec 32) (m' : Speicher) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .movdquSt base src disp) (hwr : vecWrite t.kern.speicher (effAddr t.kern base disp) (t.xmm src) = some m') : stepIntVec d t hw b cpu k = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge, speicher := m' } } := by
  unfold stepIntVec
  simp [hok, hgate, h, hwr]

/-- A bad decode length refuses every selected form. -/
theorem stepIntVec_laenge_verweigert (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (h : laengeOk d.laenge = false) : stepIntVec d t hw b cpu k = none := by
  unfold stepIntVec
  simp [h]

/-- Refused legacy admission refuses every selected form (validator
    admission, not a hardware fault). -/
theorem stepIntVec_profil_verweigert (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (hok : laengeOk d.laenge = true) (h : vektorLegacyZugelassen hw b cpu k = false) : stepIntVec d t hw b cpu k = none := by
  unfold stepIntVec
  simp [hok, h]

/-- A #GP classification refuses the `movdqa` load. -/
theorem stepIntVec_movdqaLd_gp (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst : XmmReg) (base : Register) (disp : BitVec 32) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .movdqaLd dst base disp) (hgp : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = true) : stepIntVec d t hw b cpu k = none := by
  unfold stepIntVec
  simp [hok, hgate, h, hgp]

/-- A #GP classification refuses the `movdqa` store. -/
theorem stepIntVec_movdqaSt_gp (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (base : Register) (src : XmmReg) (disp : BitVec 32) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .movdqaSt base src disp) (hgp : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = true) : stepIntVec d t hw b cpu k = none := by
  unfold stepIntVec
  simp [hok, hgate, h, hgp]

/-- A failed chunk read refuses the `movdqa` load. -/
theorem stepIntVec_movdqaLd_speicher (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst : XmmReg) (base : Register) (disp : BitVec 32) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .movdqaLd dst base disp) (hgp : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = false) (hrd : vecRead t.kern.speicher (effAddr t.kern base disp) = none) : stepIntVec d t hw b cpu k = none := by
  unfold stepIntVec
  simp [hok, hgate, h, hgp, hrd]

/-- A failed chunk write refuses the `movdqa` store. -/
theorem stepIntVec_movdqaSt_speicher (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (base : Register) (src : XmmReg) (disp : BitVec 32) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .movdqaSt base src disp) (hgp : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = false) (hwr : vecWrite t.kern.speicher (effAddr t.kern base disp) (t.xmm src) = none) : stepIntVec d t hw b cpu k = none := by
  unfold stepIntVec
  simp [hok, hgate, h, hgp, hwr]

/-- A failed chunk read refuses the `movdqu` load. -/
theorem stepIntVec_movdquLd_speicher (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst : XmmReg) (base : Register) (disp : BitVec 32) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .movdquLd dst base disp) (hrd : vecRead t.kern.speicher (effAddr t.kern base disp) = none) : stepIntVec d t hw b cpu k = none := by
  unfold stepIntVec
  simp [hok, hgate, h, hrd]

/-- A failed chunk write refuses the `movdqu` store. -/
theorem stepIntVec_movdquSt_speicher (d : IntVecDec) (t : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (base : Register) (src : XmmReg) (disp : BitVec 32) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .movdquSt base src disp) (hwr : vecWrite t.kern.speicher (effAddr t.kern base disp) (t.xmm src) = none) : stepIntVec d t hw b cpu k = none := by
  unfold stepIntVec
  simp [hok, hgate, h, hwr]

/-! ## 11. Step frames: flags, RIP, GPRs.

  Every selected row preserves rFLAGS (manual: Flags Affected None
  for PAND/POR/PXOR/PSLLQ/PSRLQ/MOVDQA/MOVDQU legacy entries; the
  PADD description states no EFLAGS bit is set), advances RIP past
  the decoded length, and keeps every GPR. Each arm reuses its §9/§10
  equation; nothing is re-evaluated. -/

/-- Every selected step preserves the flags. -/
theorem stepIntVec_flags (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (hstep : stepIntVec d t hw b cpu k = some t') : t'.kern.flags = t.kern.flags := by
  cases hop : d.op with
  | paddbRR dst src =>
    have heq := stepIntVec_paddb d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | paddwRR dst src =>
    have heq := stepIntVec_paddw d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | padddRR dst src =>
    have heq := stepIntVec_paddd d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | paddqRR dst src =>
    have heq := stepIntVec_paddq d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | pandRR dst src =>
    have heq := stepIntVec_pand d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | porRR dst src =>
    have heq := stepIntVec_por d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | pxorRR dst src =>
    have heq := stepIntVec_pxor d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | psllqRR dst cnt =>
    have heq := stepIntVec_psllqRR d t hw b cpu k dst cnt hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | psrlqRR dst cnt =>
    have heq := stepIntVec_psrlqRR d t hw b cpu k dst cnt hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | psllqImm dst imm =>
    have heq := stepIntVec_psllqImm d t hw b cpu k dst imm hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | psrlqImm dst imm =>
    have heq := stepIntVec_psrlqImm d t hw b cpu k dst imm hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | movdqaLd dst base disp =>
    by_cases hgp : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = true
    · have heq := stepIntVec_movdqaLd_gp d t hw b cpu k dst base disp hok hgate hop hgp
      rw [heq] at hstep; cases hstep
    · have hgp' : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = false := by
        cases h : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet
        · rfl
        · exact (hgp h).elim
      cases hrd : vecRead t.kern.speicher (effAddr t.kern base disp) with
      | none =>
        have heq := stepIntVec_movdqaLd_speicher d t hw b cpu k dst base disp hok hgate hop hgp' hrd
        rw [heq] at hstep; cases hstep
      | some v =>
        have heq := stepIntVec_movdqaLd d t hw b cpu k dst base disp v hok hgate hop hgp' hrd
        rw [heq] at hstep; cases hstep; rfl
  | movdqaSt base src disp =>
    by_cases hgp : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = true
    · have heq := stepIntVec_movdqaSt_gp d t hw b cpu k base src disp hok hgate hop hgp
      rw [heq] at hstep; cases hstep
    · have hgp' : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = false := by
        cases h : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet
        · rfl
        · exact (hgp h).elim
      cases hwr : vecWrite t.kern.speicher (effAddr t.kern base disp) (t.xmm src) with
      | none =>
        have heq := stepIntVec_movdqaSt_speicher d t hw b cpu k base src disp hok hgate hop hgp' hwr
        rw [heq] at hstep; cases hstep
      | some m' =>
        have heq := stepIntVec_movdqaSt d t hw b cpu k base src disp m' hok hgate hop hgp' hwr
        rw [heq] at hstep; cases hstep; rfl
  | movdquLd dst base disp =>
    cases hrd : vecRead t.kern.speicher (effAddr t.kern base disp) with
    | none =>
      have heq := stepIntVec_movdquLd_speicher d t hw b cpu k dst base disp hok hgate hop hrd
      rw [heq] at hstep; cases hstep
    | some v =>
      have heq := stepIntVec_movdquLd d t hw b cpu k dst base disp v hok hgate hop hrd
      rw [heq] at hstep; cases hstep; rfl
  | movdquSt base src disp =>
    cases hwr : vecWrite t.kern.speicher (effAddr t.kern base disp) (t.xmm src) with
    | none =>
      have heq := stepIntVec_movdquSt_speicher d t hw b cpu k base src disp hok hgate hop hwr
      rw [heq] at hstep; cases hstep
    | some m' =>
      have heq := stepIntVec_movdquSt d t hw b cpu k base src disp m' hok hgate hop hwr
      rw [heq] at hstep; cases hstep; rfl

/-- Every selected step advances RIP past the decoded length. -/
theorem stepIntVec_rip (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (hstep : stepIntVec d t hw b cpu k = some t') : t'.kern.rip = ripNach t.kern.rip d.laenge := by
  cases hop : d.op with
  | paddbRR dst src =>
    have heq := stepIntVec_paddb d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | paddwRR dst src =>
    have heq := stepIntVec_paddw d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | padddRR dst src =>
    have heq := stepIntVec_paddd d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | paddqRR dst src =>
    have heq := stepIntVec_paddq d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | pandRR dst src =>
    have heq := stepIntVec_pand d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | porRR dst src =>
    have heq := stepIntVec_por d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | pxorRR dst src =>
    have heq := stepIntVec_pxor d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | psllqRR dst cnt =>
    have heq := stepIntVec_psllqRR d t hw b cpu k dst cnt hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | psrlqRR dst cnt =>
    have heq := stepIntVec_psrlqRR d t hw b cpu k dst cnt hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | psllqImm dst imm =>
    have heq := stepIntVec_psllqImm d t hw b cpu k dst imm hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | psrlqImm dst imm =>
    have heq := stepIntVec_psrlqImm d t hw b cpu k dst imm hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | movdqaLd dst base disp =>
    by_cases hgp : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = true
    · have heq := stepIntVec_movdqaLd_gp d t hw b cpu k dst base disp hok hgate hop hgp
      rw [heq] at hstep; cases hstep
    · have hgp' : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = false := by
        cases h : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet
        · rfl
        · exact (hgp h).elim
      cases hrd : vecRead t.kern.speicher (effAddr t.kern base disp) with
      | none =>
        have heq := stepIntVec_movdqaLd_speicher d t hw b cpu k dst base disp hok hgate hop hgp' hrd
        rw [heq] at hstep; cases hstep
      | some v =>
        have heq := stepIntVec_movdqaLd d t hw b cpu k dst base disp v hok hgate hop hgp' hrd
        rw [heq] at hstep; cases hstep; rfl
  | movdqaSt base src disp =>
    by_cases hgp : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = true
    · have heq := stepIntVec_movdqaSt_gp d t hw b cpu k base src disp hok hgate hop hgp
      rw [heq] at hstep; cases hstep
    · have hgp' : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = false := by
        cases h : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet
        · rfl
        · exact (hgp h).elim
      cases hwr : vecWrite t.kern.speicher (effAddr t.kern base disp) (t.xmm src) with
      | none =>
        have heq := stepIntVec_movdqaSt_speicher d t hw b cpu k base src disp hok hgate hop hgp' hwr
        rw [heq] at hstep; cases hstep
      | some m' =>
        have heq := stepIntVec_movdqaSt d t hw b cpu k base src disp m' hok hgate hop hgp' hwr
        rw [heq] at hstep; cases hstep; rfl
  | movdquLd dst base disp =>
    cases hrd : vecRead t.kern.speicher (effAddr t.kern base disp) with
    | none =>
      have heq := stepIntVec_movdquLd_speicher d t hw b cpu k dst base disp hok hgate hop hrd
      rw [heq] at hstep; cases hstep
    | some v =>
      have heq := stepIntVec_movdquLd d t hw b cpu k dst base disp v hok hgate hop hrd
      rw [heq] at hstep; cases hstep; rfl
  | movdquSt base src disp =>
    cases hwr : vecWrite t.kern.speicher (effAddr t.kern base disp) (t.xmm src) with
    | none =>
      have heq := stepIntVec_movdquSt_speicher d t hw b cpu k base src disp hok hgate hop hwr
      rw [heq] at hstep; cases hstep
    | some m' =>
      have heq := stepIntVec_movdquSt d t hw b cpu k base src disp m' hok hgate hop hwr
      rw [heq] at hstep; cases hstep; rfl

/-- Every selected step keeps every GPR. -/
theorem stepIntVec_gpr (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (q : Register) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (hstep : stepIntVec d t hw b cpu k = some t') : t'.kern.register q = t.kern.register q := by
  cases hop : d.op with
  | paddbRR dst src =>
    have heq := stepIntVec_paddb d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | paddwRR dst src =>
    have heq := stepIntVec_paddw d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | padddRR dst src =>
    have heq := stepIntVec_paddd d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | paddqRR dst src =>
    have heq := stepIntVec_paddq d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | pandRR dst src =>
    have heq := stepIntVec_pand d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | porRR dst src =>
    have heq := stepIntVec_por d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | pxorRR dst src =>
    have heq := stepIntVec_pxor d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | psllqRR dst cnt =>
    have heq := stepIntVec_psllqRR d t hw b cpu k dst cnt hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | psrlqRR dst cnt =>
    have heq := stepIntVec_psrlqRR d t hw b cpu k dst cnt hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | psllqImm dst imm =>
    have heq := stepIntVec_psllqImm d t hw b cpu k dst imm hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | psrlqImm dst imm =>
    have heq := stepIntVec_psrlqImm d t hw b cpu k dst imm hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | movdqaLd dst base disp =>
    by_cases hgp : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = true
    · have heq := stepIntVec_movdqaLd_gp d t hw b cpu k dst base disp hok hgate hop hgp
      rw [heq] at hstep; cases hstep
    · have hgp' : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = false := by
        cases h : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet
        · rfl
        · exact (hgp h).elim
      cases hrd : vecRead t.kern.speicher (effAddr t.kern base disp) with
      | none =>
        have heq := stepIntVec_movdqaLd_speicher d t hw b cpu k dst base disp hok hgate hop hgp' hrd
        rw [heq] at hstep; cases hstep
      | some v =>
        have heq := stepIntVec_movdqaLd d t hw b cpu k dst base disp v hok hgate hop hgp' hrd
        rw [heq] at hstep; cases hstep; rfl
  | movdqaSt base src disp =>
    by_cases hgp : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = true
    · have heq := stepIntVec_movdqaSt_gp d t hw b cpu k base src disp hok hgate hop hgp
      rw [heq] at hstep; cases hstep
    · have hgp' : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = false := by
        cases h : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet
        · rfl
        · exact (hgp h).elim
      cases hwr : vecWrite t.kern.speicher (effAddr t.kern base disp) (t.xmm src) with
      | none =>
        have heq := stepIntVec_movdqaSt_speicher d t hw b cpu k base src disp hok hgate hop hgp' hwr
        rw [heq] at hstep; cases hstep
      | some m' =>
        have heq := stepIntVec_movdqaSt d t hw b cpu k base src disp m' hok hgate hop hgp' hwr
        rw [heq] at hstep; cases hstep; rfl
  | movdquLd dst base disp =>
    cases hrd : vecRead t.kern.speicher (effAddr t.kern base disp) with
    | none =>
      have heq := stepIntVec_movdquLd_speicher d t hw b cpu k dst base disp hok hgate hop hrd
      rw [heq] at hstep; cases hstep
    | some v =>
      have heq := stepIntVec_movdquLd d t hw b cpu k dst base disp v hok hgate hop hrd
      rw [heq] at hstep; cases hstep; rfl
  | movdquSt base src disp =>
    cases hwr : vecWrite t.kern.speicher (effAddr t.kern base disp) (t.xmm src) with
    | none =>
      have heq := stepIntVec_movdquSt_speicher d t hw b cpu k base src disp hok hgate hop hwr
      rw [heq] at hstep; cases hstep
    | some m' =>
      have heq := stepIntVec_movdquSt d t hw b cpu k base src disp m' hok hgate hop hwr
      rw [heq] at hstep; cases hstep; rfl

/-! ## 12. XMM preservation: every other register is kept whole.

  Register and load rows write only their destination (via the
  accepted `xmmSet`); stores write no XMM register at all. -/

/-- `paddb` keeps every other XMM register whole. -/
theorem stepIntVec_paddb_fremd (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src q : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .paddbRR dst src) (hstep : stepIntVec d t hw b cpu k = some t') (hq : q ≠ dst) : t'.xmm q = t.xmm q := by
  rw [stepIntVec_paddb d t hw b cpu k dst src hok hgate h] at hstep
  cases hstep
  exact xmmSet_fremd _ _ _ _ hq

/-- `paddw` keeps every other XMM register whole. -/
theorem stepIntVec_paddw_fremd (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src q : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .paddwRR dst src) (hstep : stepIntVec d t hw b cpu k = some t') (hq : q ≠ dst) : t'.xmm q = t.xmm q := by
  rw [stepIntVec_paddw d t hw b cpu k dst src hok hgate h] at hstep
  cases hstep
  exact xmmSet_fremd _ _ _ _ hq

/-- `paddd` keeps every other XMM register whole. -/
theorem stepIntVec_paddd_fremd (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src q : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .padddRR dst src) (hstep : stepIntVec d t hw b cpu k = some t') (hq : q ≠ dst) : t'.xmm q = t.xmm q := by
  rw [stepIntVec_paddd d t hw b cpu k dst src hok hgate h] at hstep
  cases hstep
  exact xmmSet_fremd _ _ _ _ hq

/-- `paddq` keeps every other XMM register whole. -/
theorem stepIntVec_paddq_fremd (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src q : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .paddqRR dst src) (hstep : stepIntVec d t hw b cpu k = some t') (hq : q ≠ dst) : t'.xmm q = t.xmm q := by
  rw [stepIntVec_paddq d t hw b cpu k dst src hok hgate h] at hstep
  cases hstep
  exact xmmSet_fremd _ _ _ _ hq

/-- `pand` keeps every other XMM register whole. -/
theorem stepIntVec_pand_fremd (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src q : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .pandRR dst src) (hstep : stepIntVec d t hw b cpu k = some t') (hq : q ≠ dst) : t'.xmm q = t.xmm q := by
  rw [stepIntVec_pand d t hw b cpu k dst src hok hgate h] at hstep
  cases hstep
  exact xmmSet_fremd _ _ _ _ hq

/-- `por` keeps every other XMM register whole. -/
theorem stepIntVec_por_fremd (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src q : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .porRR dst src) (hstep : stepIntVec d t hw b cpu k = some t') (hq : q ≠ dst) : t'.xmm q = t.xmm q := by
  rw [stepIntVec_por d t hw b cpu k dst src hok hgate h] at hstep
  cases hstep
  exact xmmSet_fremd _ _ _ _ hq

/-- `pxor` keeps every other XMM register whole. -/
theorem stepIntVec_pxor_fremd (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src q : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .pxorRR dst src) (hstep : stepIntVec d t hw b cpu k = some t') (hq : q ≠ dst) : t'.xmm q = t.xmm q := by
  rw [stepIntVec_pxor d t hw b cpu k dst src hok hgate h] at hstep
  cases hstep
  exact xmmSet_fremd _ _ _ _ hq

/-- `psllq` with a register count keeps every other XMM register whole. -/
theorem stepIntVec_psllqRR_fremd (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst cnt q : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .psllqRR dst cnt) (hstep : stepIntVec d t hw b cpu k = some t') (hq : q ≠ dst) : t'.xmm q = t.xmm q := by
  rw [stepIntVec_psllqRR d t hw b cpu k dst cnt hok hgate h] at hstep
  cases hstep
  exact xmmSet_fremd _ _ _ _ hq

/-- `psrlq` with a register count keeps every other XMM register whole. -/
theorem stepIntVec_psrlqRR_fremd (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst cnt q : XmmReg) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .psrlqRR dst cnt) (hstep : stepIntVec d t hw b cpu k = some t') (hq : q ≠ dst) : t'.xmm q = t.xmm q := by
  rw [stepIntVec_psrlqRR d t hw b cpu k dst cnt hok hgate h] at hstep
  cases hstep
  exact xmmSet_fremd _ _ _ _ hq

/-- `psllq` with an imm8 count keeps every other XMM register whole. -/
theorem stepIntVec_psllqImm_fremd (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst q : XmmReg) (imm : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .psllqImm dst imm) (hstep : stepIntVec d t hw b cpu k = some t') (hq : q ≠ dst) : t'.xmm q = t.xmm q := by
  rw [stepIntVec_psllqImm d t hw b cpu k dst imm hok hgate h] at hstep
  cases hstep
  exact xmmSet_fremd _ _ _ _ hq

/-- `psrlq` with an imm8 count keeps every other XMM register whole. -/
theorem stepIntVec_psrlqImm_fremd (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst q : XmmReg) (imm : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .psrlqImm dst imm) (hstep : stepIntVec d t hw b cpu k = some t') (hq : q ≠ dst) : t'.xmm q = t.xmm q := by
  rw [stepIntVec_psrlqImm d t hw b cpu k dst imm hok hgate h] at hstep
  cases hstep
  exact xmmSet_fremd _ _ _ _ hq

/-- `movdqa` load keeps every other XMM register whole. -/
theorem stepIntVec_movdqaLd_fremd (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst q : XmmReg) (base : Register) (disp : BitVec 32) (v : Vektor) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .movdqaLd dst base disp) (hgp : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = false) (hrd : vecRead t.kern.speicher (effAddr t.kern base disp) = some v) (hstep : stepIntVec d t hw b cpu k = some t') (hq : q ≠ dst) : t'.xmm q = t.xmm q := by
  rw [stepIntVec_movdqaLd d t hw b cpu k dst base disp v hok hgate h hgp hrd] at hstep
  cases hstep
  exact xmmSet_fremd _ _ _ _ hq

/-- `movdqu` load keeps every other XMM register whole. -/
theorem stepIntVec_movdquLd_fremd (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst q : XmmReg) (base : Register) (disp : BitVec 32) (v : Vektor) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .movdquLd dst base disp) (hrd : vecRead t.kern.speicher (effAddr t.kern base disp) = some v) (hstep : stepIntVec d t hw b cpu k = some t') (hq : q ≠ dst) : t'.xmm q = t.xmm q := by
  rw [stepIntVec_movdquLd d t hw b cpu k dst base disp v hok hgate h hrd] at hstep
  cases hstep
  exact xmmSet_fremd _ _ _ _ hq

/-- `movdqa` store writes no XMM register at all. -/
theorem stepIntVec_movdqaSt_xmm (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (base : Register) (src : XmmReg) (disp : BitVec 32) (m' : Speicher) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .movdqaSt base src disp) (hgp : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = false) (hwr : vecWrite t.kern.speicher (effAddr t.kern base disp) (t.xmm src) = some m') (hstep : stepIntVec d t hw b cpu k = some t') : t'.xmm = t.xmm := by
  rw [stepIntVec_movdqaSt d t hw b cpu k base src disp m' hok hgate h hgp hwr] at hstep
  cases hstep
  rfl

/-- `movdqu` store writes no XMM register at all. -/
theorem stepIntVec_movdquSt_xmm (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (base : Register) (src : XmmReg) (disp : BitVec 32) (m' : Speicher) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .movdquSt base src disp) (hwr : vecWrite t.kern.speicher (effAddr t.kern base disp) (t.xmm src) = some m') (hstep : stepIntVec d t hw b cpu k = some t') : t'.xmm = t.xmm := by
  rw [stepIntVec_movdquSt d t hw b cpu k base src disp m' hok hgate h hwr] at hstep
  cases hstep
  rfl

/-! ## 13. Memory preservation outside the stores.

  Register rows and loads change no memory byte; only the two
  store rows go through `vecWrite`. The two exclusion premises name
  exactly the store shapes. -/

/-- Every non-store selected step changes no memory byte. -/
theorem stepIntVec_speicher (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (hstep : stepIntVec d t hw b cpu k = some t') (hA : ∀ (base : Register) (src : XmmReg) (disp : BitVec 32), d.op ≠ .movdqaSt base src disp) (hU : ∀ (base : Register) (src : XmmReg) (disp : BitVec 32), d.op ≠ .movdquSt base src disp) : t'.kern.speicher = t.kern.speicher := by
  cases hop : d.op with
  | paddbRR dst src =>
    have heq := stepIntVec_paddb d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | paddwRR dst src =>
    have heq := stepIntVec_paddw d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | padddRR dst src =>
    have heq := stepIntVec_paddd d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | paddqRR dst src =>
    have heq := stepIntVec_paddq d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | pandRR dst src =>
    have heq := stepIntVec_pand d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | porRR dst src =>
    have heq := stepIntVec_por d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | pxorRR dst src =>
    have heq := stepIntVec_pxor d t hw b cpu k dst src hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | psllqRR dst cnt =>
    have heq := stepIntVec_psllqRR d t hw b cpu k dst cnt hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | psrlqRR dst cnt =>
    have heq := stepIntVec_psrlqRR d t hw b cpu k dst cnt hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | psllqImm dst imm =>
    have heq := stepIntVec_psllqImm d t hw b cpu k dst imm hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | psrlqImm dst imm =>
    have heq := stepIntVec_psrlqImm d t hw b cpu k dst imm hok hgate hop
    rw [heq] at hstep; cases hstep; rfl
  | movdqaLd dst base disp =>
    by_cases hgp : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = true
    · have heq := stepIntVec_movdqaLd_gp d t hw b cpu k dst base disp hok hgate hop hgp
      rw [heq] at hstep; cases hstep
    · have hgp' : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = false := by
        cases h : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet
        · rfl
        · exact (hgp h).elim
      cases hrd : vecRead t.kern.speicher (effAddr t.kern base disp) with
      | none =>
        have heq := stepIntVec_movdqaLd_speicher d t hw b cpu k dst base disp hok hgate hop hgp' hrd
        rw [heq] at hstep; cases hstep
      | some v =>
        have heq := stepIntVec_movdqaLd d t hw b cpu k dst base disp v hok hgate hop hgp' hrd
        rw [heq] at hstep; cases hstep; rfl
  | movdqaSt base src disp =>
    exact ((hA base src disp) hop).elim
  | movdquLd dst base disp =>
    cases hrd : vecRead t.kern.speicher (effAddr t.kern base disp) with
    | none =>
      have heq := stepIntVec_movdquLd_speicher d t hw b cpu k dst base disp hok hgate hop hrd
      rw [heq] at hstep; cases hstep
    | some v =>
      have heq := stepIntVec_movdquLd d t hw b cpu k dst base disp v hok hgate hop hrd
      rw [heq] at hstep; cases hstep; rfl
  | movdquSt base src disp =>
    exact ((hU base src disp) hop).elim

/-! ## 14. Per-lane effects: every admitted width derives from producers.

  Each lane of a PADD result is the canonical modular lane sum at
  its width (`laneGet_add`, no inter-lane carry); each lane of a
  logical result is the canonical lane operation (`laneGet_and` /
  `laneGet_or` / `laneGet_xor`); each lane of a shift result is the
  saturating lane shift (§2). No lane effect is re-evaluated here. -/

/-- `paddb` reads per lane as the canonical modular byte add. -/
theorem stepIntVec_paddb_spur (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src : XmmReg) (i : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .paddbRR dst src) (hstep : stepIntVec d t hw b cpu k = some t') (hi : i < laneCount .b8) : laneGet .b8 (t'.xmm dst) i = addB .b8 (laneGet .b8 (t.xmm dst) i) (laneGet .b8 (t.xmm src) i) := by
  rw [stepIntVec_paddb d t hw b cpu k dst src hok hgate h] at hstep
  cases hstep
  show laneGet .b8 ((xmmSet t.xmm dst (vecAdd .b8 (t.xmm dst) (t.xmm src))) dst) i = _
  rw [xmmSet_gleich]
  exact laneGet_add .b8 _ _ i hi

/-- `paddw` reads per lane as the canonical modular word add. -/
theorem stepIntVec_paddw_spur (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src : XmmReg) (i : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .paddwRR dst src) (hstep : stepIntVec d t hw b cpu k = some t') (hi : i < laneCount .b16) : laneGet .b16 (t'.xmm dst) i = addB .b16 (laneGet .b16 (t.xmm dst) i) (laneGet .b16 (t.xmm src) i) := by
  rw [stepIntVec_paddw d t hw b cpu k dst src hok hgate h] at hstep
  cases hstep
  show laneGet .b16 ((xmmSet t.xmm dst (vecAdd .b16 (t.xmm dst) (t.xmm src))) dst) i = _
  rw [xmmSet_gleich]
  exact laneGet_add .b16 _ _ i hi

/-- `paddd` reads per lane as the canonical modular doubleword add. -/
theorem stepIntVec_paddd_spur (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src : XmmReg) (i : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .padddRR dst src) (hstep : stepIntVec d t hw b cpu k = some t') (hi : i < laneCount .b32) : laneGet .b32 (t'.xmm dst) i = addB .b32 (laneGet .b32 (t.xmm dst) i) (laneGet .b32 (t.xmm src) i) := by
  rw [stepIntVec_paddd d t hw b cpu k dst src hok hgate h] at hstep
  cases hstep
  show laneGet .b32 ((xmmSet t.xmm dst (vecAdd .b32 (t.xmm dst) (t.xmm src))) dst) i = _
  rw [xmmSet_gleich]
  exact laneGet_add .b32 _ _ i hi

/-- `paddq` reads per lane as the canonical modular quadword add. -/
theorem stepIntVec_paddq_spur (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src : XmmReg) (i : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .paddqRR dst src) (hstep : stepIntVec d t hw b cpu k = some t') (hi : i < laneCount .b64) : laneGet .b64 (t'.xmm dst) i = addB .b64 (laneGet .b64 (t.xmm dst) i) (laneGet .b64 (t.xmm src) i) := by
  rw [stepIntVec_paddq d t hw b cpu k dst src hok hgate h] at hstep
  cases hstep
  show laneGet .b64 ((xmmSet t.xmm dst (vecAdd .b64 (t.xmm dst) (t.xmm src))) dst) i = _
  rw [xmmSet_gleich]
  exact laneGet_add .b64 _ _ i hi

/-- `pand` reads per lane as the truncated lane conjunction. -/
theorem stepIntVec_pand_spur (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src : XmmReg) (i : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .pandRR dst src) (hstep : stepIntVec d t hw b cpu k = some t') (hi : i < laneCount .b64) : laneGet .b64 (t'.xmm dst) i = trunc .b64 (laneGet .b64 (t.xmm dst) i &&& laneGet .b64 (t.xmm src) i) := by
  rw [stepIntVec_pand d t hw b cpu k dst src hok hgate h] at hstep
  cases hstep
  show laneGet .b64 ((xmmSet t.xmm dst (vecAnd .b64 (t.xmm dst) (t.xmm src))) dst) i = _
  rw [xmmSet_gleich]
  exact laneGet_and .b64 _ _ i hi

/-- `por` reads per lane as the truncated lane disjunction. -/
theorem stepIntVec_por_spur (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src : XmmReg) (i : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .porRR dst src) (hstep : stepIntVec d t hw b cpu k = some t') (hi : i < laneCount .b64) : laneGet .b64 (t'.xmm dst) i = trunc .b64 (laneGet .b64 (t.xmm dst) i ||| laneGet .b64 (t.xmm src) i) := by
  rw [stepIntVec_por d t hw b cpu k dst src hok hgate h] at hstep
  cases hstep
  show laneGet .b64 ((xmmSet t.xmm dst (vecOr .b64 (t.xmm dst) (t.xmm src))) dst) i = _
  rw [xmmSet_gleich]
  exact laneGet_or .b64 _ _ i hi

/-- `pxor` reads per lane as the canonical lane xor. -/
theorem stepIntVec_pxor_spur (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst src : XmmReg) (i : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .pxorRR dst src) (hstep : stepIntVec d t hw b cpu k = some t') (hi : i < laneCount .b64) : laneGet .b64 (t'.xmm dst) i = xorB .b64 (laneGet .b64 (t.xmm dst) i) (laneGet .b64 (t.xmm src) i) := by
  rw [stepIntVec_pxor d t hw b cpu k dst src hok hgate h] at hstep
  cases hstep
  show laneGet .b64 ((xmmSet t.xmm dst (vecXor .b64 (t.xmm dst) (t.xmm src))) dst) i = _
  rw [xmmSet_gleich]
  exact laneGet_xor .b64 _ _ i hi

/-- `psllq` with a register count shifts each lane by the low 64
    count bits (admitted-count case). -/
theorem stepIntVec_psllqRR_spur (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst cnt : XmmReg) (i : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .psllqRR dst cnt) (hstep : stepIntVec d t hw b cpu k = some t') (hc : ¬ 63 < (vLo (t.xmm cnt)).toNat) (hi : i < laneCount .b64) : laneNat .b64 (t'.xmm dst) i = (laneNat .b64 (t.xmm dst) i * 2 ^ (vLo (t.xmm cnt)).toNat) % 2 ^ 64 := by
  rw [stepIntVec_psllqRR d t hw b cpu k dst cnt hok hgate h] at hstep
  cases hstep
  show laneNat .b64 ((xmmSet t.xmm dst (vecShlQ (t.xmm dst) (vLo (t.xmm cnt)).toNat)) dst) i = _
  rw [xmmSet_gleich]
  exact laneNat_shlQ _ _ _ hc hi

/-- `psrlq` with a register count shifts each lane by the low 64
    count bits (admitted-count case). -/
theorem stepIntVec_psrlqRR_spur (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst cnt : XmmReg) (i : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .psrlqRR dst cnt) (hstep : stepIntVec d t hw b cpu k = some t') (hc : ¬ 63 < (vLo (t.xmm cnt)).toNat) (hi : i < laneCount .b64) : laneNat .b64 (t'.xmm dst) i = (laneNat .b64 (t.xmm dst) i / 2 ^ (vLo (t.xmm cnt)).toNat) % 2 ^ 64 := by
  rw [stepIntVec_psrlqRR d t hw b cpu k dst cnt hok hgate h] at hstep
  cases hstep
  show laneNat .b64 ((xmmSet t.xmm dst (vecShrQ (t.xmm dst) (vLo (t.xmm cnt)).toNat)) dst) i = _
  rw [xmmSet_gleich]
  exact laneNat_shrQ _ _ _ hc hi

/-- `psllq` with an imm8 count shifts each lane (admitted case). -/
theorem stepIntVec_psllqImm_spur (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst : XmmReg) (imm i : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .psllqImm dst imm) (hstep : stepIntVec d t hw b cpu k = some t') (hc : ¬ 63 < imm) (hi : i < laneCount .b64) : laneNat .b64 (t'.xmm dst) i = (laneNat .b64 (t.xmm dst) i * 2 ^ imm) % 2 ^ 64 := by
  rw [stepIntVec_psllqImm d t hw b cpu k dst imm hok hgate h] at hstep
  cases hstep
  show laneNat .b64 ((xmmSet t.xmm dst (vecShlQ (t.xmm dst) imm)) dst) i = _
  rw [xmmSet_gleich]
  exact laneNat_shlQ _ _ _ hc hi

/-- `psrlq` with an imm8 count shifts each lane (admitted case). -/
theorem stepIntVec_psrlqImm_spur (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst : XmmReg) (imm i : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .psrlqImm dst imm) (hstep : stepIntVec d t hw b cpu k = some t') (hc : ¬ 63 < imm) (hi : i < laneCount .b64) : laneNat .b64 (t'.xmm dst) i = (laneNat .b64 (t.xmm dst) i / 2 ^ imm) % 2 ^ 64 := by
  rw [stepIntVec_psrlqImm d t hw b cpu k dst imm hok hgate h] at hstep
  cases hstep
  show laneNat .b64 ((xmmSet t.xmm dst (vecShrQ (t.xmm dst) imm)) dst) i = _
  rw [xmmSet_gleich]
  exact laneNat_shrQ _ _ _ hc hi

/-- Saturated register-count shift left zeroes every lane. -/
theorem stepIntVec_psllqRR_satt (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst cnt : XmmReg) (i : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .psllqRR dst cnt) (hstep : stepIntVec d t hw b cpu k = some t') (hc : 63 < (vLo (t.xmm cnt)).toNat) : laneNat .b64 (t'.xmm dst) i = 0 := by
  rw [stepIntVec_psllqRR d t hw b cpu k dst cnt hok hgate h] at hstep
  cases hstep
  show laneNat .b64 ((xmmSet t.xmm dst (vecShlQ (t.xmm dst) (vLo (t.xmm cnt)).toNat)) dst) i = _
  rw [xmmSet_gleich]
  exact laneNat_shlQ_satt _ _ _ hc

/-- Saturated register-count shift right zeroes every lane. -/
theorem stepIntVec_psrlqRR_satt (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (dst cnt : XmmReg) (i : Nat) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .psrlqRR dst cnt) (hstep : stepIntVec d t hw b cpu k = some t') (hc : 63 < (vLo (t.xmm cnt)).toNat) : laneNat .b64 (t'.xmm dst) i = 0 := by
  rw [stepIntVec_psrlqRR d t hw b cpu k dst cnt hok hgate h] at hstep
  cases hstep
  show laneNat .b64 ((xmmSet t.xmm dst (vecShrQ (t.xmm dst) (vLo (t.xmm cnt)).toNat)) dst) i = _
  rw [xmmSet_gleich]
  exact laneNat_shrQ_satt _ _ _ hc

/-! ## 15. Store read-back and shared-row step agreement.

  A successful store reads back as the written word (through the
  accepted two-chunk `vecRead_nach_write`); the shared PXOR/PADDQ
  rows step exactly as the accepted `stepVector` under the old gate. -/

/-- A successful vector store goes through two ordered chunk
    writes: the low half first, then the high half. -/
theorem vecWrite_aufgeteilt (m m' : Speicher) (a : Adresse) (v : Vektor)
    (h : vecWrite m a v = some m') :
    ∃ m1 : Speicher, write64 m a (vLo v) = some m1 ∧
      write64 m1 (vecHiAddr a) (vHi v) = some m' := by
  unfold vecWrite at h
  revert h
  cases h1 : write64 m a (vLo v) with
  | none => intro h; cases h
  | some m1 => intro h; dsimp only at h; exact ⟨m1, rfl, h⟩

/-- `movdqa` store reads back as the written word. -/
theorem stepIntVec_movdqaSt_read (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (base : Register) (src : XmmReg) (disp : BitVec 32) (m' : Speicher) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .movdqaSt base src disp) (hgp : vektorGpFehler (effAddr t.kern base disp) .ausgerichtet = false) (hwr : vecWrite t.kern.speicher (effAddr t.kern base disp) (t.xmm src) = some m') (hstep : stepIntVec d t hw b cpu k = some t') (hrd1 : lesbar8 t.kern.speicher (effAddr t.kern base disp) = true) (hrd2 : lesbar8 t.kern.speicher (vecHiAddr (effAddr t.kern base disp)) = true) (hno : OhneUmbruch16 (effAddr t.kern base disp)) : vecRead t'.kern.speicher (effAddr t.kern base disp) = some (t.xmm src) := by
  rw [stepIntVec_movdqaSt d t hw b cpu k base src disp m' hok hgate h hgp hwr] at hstep
  cases hstep
  show vecRead m' (effAddr t.kern base disp) = some (t.xmm src)
  obtain ⟨m1, h1, h2⟩ := vecWrite_aufgeteilt _ _ _ _ hwr
  exact vecRead_nach_write _ _ _ _ _ h1 h2 hrd1 hrd2 hno

/-- `movdqu` store reads back as the written word. -/
theorem stepIntVec_movdquSt_read (d : IntVecDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) (base : Register) (src : XmmReg) (disp : BitVec 32) (m' : Speicher) (hok : laengeOk d.laenge = true) (hgate : vektorLegacyZugelassen hw b cpu k = true) (h : d.op = .movdquSt base src disp) (hwr : vecWrite t.kern.speicher (effAddr t.kern base disp) (t.xmm src) = some m') (hstep : stepIntVec d t hw b cpu k = some t') (hrd1 : lesbar8 t.kern.speicher (effAddr t.kern base disp) = true) (hrd2 : lesbar8 t.kern.speicher (vecHiAddr (effAddr t.kern base disp)) = true) (hno : OhneUmbruch16 (effAddr t.kern base disp)) : vecRead t'.kern.speicher (effAddr t.kern base disp) = some (t.xmm src) := by
  rw [stepIntVec_movdquSt d t hw b cpu k base src disp m' hok hgate h hwr] at hstep
  cases hstep
  show vecRead m' (effAddr t.kern base disp) = some (t.xmm src)
  obtain ⟨m1, h1, h2⟩ := vecWrite_aufgeteilt _ _ _ _ hwr
  exact vecRead_nach_write _ _ _ _ _ h1 h2 hrd1 hrd2 hno

/-- SHARED ROW: admitted PXOR steps exactly as the accepted
    `stepVector` under the old (stronger) gate. -/
theorem stepIntVec_pxor_agree_step (d : VectorDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild) (dst src : XmmReg) (hgate : vektorHwZugelassen hw b cpu x k = true) (hok : laengeOk d.laenge = true) (h : d.op = .pxorRR dst src) (hs : stepVector d t b = some t') : stepIntVec (⟨.pxorRR dst src, d.laenge⟩ : IntVecDec) t hw b cpu k = some t' := by
  have hleg := vektorLegacy_verfeinert hw b cpu x k hgate
  have hfp := vektorHw_verfeinert hw b cpu x k hgate
  rw [stepVector_pxor d t b dst src hok hfp h] at hs
  cases hs
  rw [stepIntVec_pxor _ t hw b cpu k dst src hok hleg rfl]

/-- SHARED ROW: admitted PADDQ steps exactly as the accepted
    `stepVector` under the old (stronger) gate. -/
theorem stepIntVec_paddq_agree_step (d : VectorDec) (t t' : FpZustand) (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild) (dst src : XmmReg) (hgate : vektorHwZugelassen hw b cpu x k = true) (hok : laengeOk d.laenge = true) (h : d.op = .paddqRR dst src) (hs : stepVector d t b = some t') : stepIntVec (⟨.paddqRR dst src, d.laenge⟩ : IntVecDec) t hw b cpu k = some t' := by
  have hleg := vektorLegacy_verfeinert hw b cpu x k hgate
  have hfp := vektorHw_verfeinert hw b cpu x k hgate
  rw [stepVector_paddq d t b dst src hok hfp h] at hs
  cases hs
  rw [stepIntVec_paddq _ t hw b cpu k dst src hok hleg rfl]

/-! ## 16. Fetched byte execution and validator adapter.

  For the consumers (hardware execution, fault classification,
  validator): the fetch discipline over actual memory bytes, the
  fetched byte step under the legacy gate, the full validator
  admission (fetch discipline AND hardware gate), and a combined
  decoder that chains the accepted unified dispatcher first and
  the selected decoder where it refuses -- shadowing nothing. -/

/-- Fetch discipline for a selected form: the length equation, the
    length guard, and execute permission of the consumed prefix. -/
def intVecZugelassen (t : FpZustand) (fenster : List Byte)
    (d : IntVecDec) (rest : List Byte) : Bool :=
  decide (d.laenge + rest.length = fenster.length) &&
    laengeOk d.laenge &&
    ausfuehrbarN t.kern.speicher t.kern.rip d.laenge

/-- Admission carries the length equation. -/
theorem intVecZugelassen_summe (t : FpZustand) (fenster : List Byte)
    (d : IntVecDec) (rest : List Byte)
    (h : intVecZugelassen t fenster d rest = true) :
    d.laenge + rest.length = fenster.length := by
  simp only [intVecZugelassen, Bool.and_eq_true] at h
  obtain ⟨⟨hsum, _⟩, _⟩ := h
  exact of_decide_eq_true hsum

/-- Admission carries the length guard. -/
theorem intVecZugelassen_laenge (t : FpZustand) (fenster : List Byte)
    (d : IntVecDec) (rest : List Byte)
    (h : intVecZugelassen t fenster d rest = true) :
    laengeOk d.laenge = true := by
  simp only [intVecZugelassen, Bool.and_eq_true] at h
  obtain ⟨⟨_, hlen⟩, _⟩ := h
  exact hlen

/-- Admission carries execute permission of the consumed prefix. -/
theorem intVecZugelassen_ausfuehrbar (t : FpZustand)
    (fenster : List Byte) (d : IntVecDec) (rest : List Byte)
    (h : intVecZugelassen t fenster d rest = true) :
    ausfuehrbarN t.kern.speicher t.kern.rip d.laenge = true := by
  simp only [intVecZugelassen, Bool.and_eq_true] at h
  obtain ⟨_, hexe⟩ := h
  exact hexe

/-- Fetch and decode: the selected decoder over the given window,
    gated by the fetch discipline. A forged `IntVecDec` cannot inject
    an instruction: only actual bytes feed the step. -/
def fetchIntVec (t : FpZustand) (fenster : List Byte) :
    Option (IntVecDec × List Byte) :=
  match decodeIntVec fenster with
  | none => none
  | some p =>
    if intVecZugelassen t fenster p.1 p.2 then some p else none

/-- A successful fetch decodes to the admitted instruction: length
    equation, length guard and execute permission all hold. -/
theorem fetchIntVec_erfolg (t : FpZustand) (fenster : List Byte)
    (d : IntVecDec) (rest : List Byte)
    (h : fetchIntVec t fenster = some (d, rest)) :
    decodeIntVec fenster = some (d, rest) ∧
      d.laenge + rest.length = fenster.length ∧
      laengeOk d.laenge = true ∧
      ausfuehrbarN t.kern.speicher t.kern.rip d.laenge = true := by
  have e : fetchIntVec t fenster =
      match decodeIntVec fenster with
      | none => (none : Option (IntVecDec × List Byte))
      | some p =>
        if intVecZugelassen t fenster p.1 p.2 then some p else none := rfl
  rw [e] at h
  cases hdec : decodeIntVec fenster with
  | none =>
    simp [hdec] at h
  | some p =>
    simp only [hdec] at h
    by_cases hz : intVecZugelassen t fenster p.1 p.2 = true
    · rw [if_pos hz] at h
      obtain rfl := Option.some_inj.mp h
      exact ⟨rfl, intVecZugelassen_summe _ _ _ _ hz,
        intVecZugelassen_laenge _ _ _ _ hz,
        intVecZugelassen_ausfuehrbar _ _ _ _ hz⟩
    · rw [if_neg hz] at h
      cases h

/-- Fetched selected byte step under the legacy gate: decode the
    ACTUAL fetched bytes, then run the selected step. -/
def intVecByteschritt (t : FpZustand) (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) :
    Option FpZustand :=
  match fetchIntVec t (geholt t.kern) with
  | none => none
  | some (d, _) => stepIntVec d t hw b cpu k

/-- Full validator admission for a fetched selected form: the fetch
    discipline AND the legacy hardware gate. -/
def intVecValidatorZugelassen (t : FpZustand) (fenster : List Byte)
    (d : IntVecDec) (rest : List Byte) (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild) : Bool :=
  intVecZugelassen t fenster d rest &&
    vektorLegacyZugelassen hw b cpu k

/-- Full admission needs the fetch discipline. -/
theorem intVecValidator_braucht_fetch (t : FpZustand)
    (fenster : List Byte) (d : IntVecDec) (rest : List Byte)
    (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal)
    (k : KontrollBild)
    (h : intVecValidatorZugelassen t fenster d rest hw b cpu k = true) :
    intVecZugelassen t fenster d rest = true := by
  simp only [intVecValidatorZugelassen, Bool.and_eq_true] at h
  exact h.1

/-- Full admission needs the legacy hardware gate. -/
theorem intVecValidator_braucht_hw (t : FpZustand)
    (fenster : List Byte) (d : IntVecDec) (rest : List Byte)
    (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal)
    (k : KontrollBild)
    (h : intVecValidatorZugelassen t fenster d rest hw b cpu k = true) :
    vektorLegacyZugelassen hw b cpu k = true := by
  simp only [intVecValidatorZugelassen, Bool.and_eq_true] at h
  exact h.2

/-- FETCH BRIDGE: a fetched selected form steps through the fetched
    byte step. -/
theorem intVec_fetch_bridge (t t' : FpZustand) (hw : HwProfil)
    (b : BereitProfil) (cpu : CpuMerkmal) (k : KontrollBild)
    (d : IntVecDec) (rest : List Byte)
    (hf : fetchIntVec t (geholt t.kern) = some (d, rest))
    (hs : stepIntVec d t hw b cpu k = some t') :
    intVecByteschritt t hw b cpu k = some t' := by
  unfold intVecByteschritt
  rw [hf]
  exact hs

/-- Combined decode: the accepted unified dispatcher first, the
    selected decoder only where it refuses. No existing form is
    shadowed and no selected row is re-decided. -/
def decodeComboIV (bs : List Byte) :
    Option ((ExtInstr ⊕ IntVecDec) × List Byte) :=
  match decodeExt bs with
  | some (e, rest) => some (.inl e, rest)
  | none =>
    match decodeIntVec bs with
    | some (n, rest) => some (.inr n, rest)
    | none => none

/-- The combined decoder agrees with the unified dispatcher on every
    byte string it accepts. -/
theorem decodeComboIV_kanonisch (bs : List Byte) (e : ExtInstr)
    (rest : List Byte) (h : decodeExt bs = some (e, rest)) :
    decodeComboIV bs = some (.inl e, rest) := by
  unfold decodeComboIV
  rw [h]

/-- Where the unified dispatcher refuses, a selected row is taken. -/
theorem decodeComboIV_erweitert (bs : List Byte) (n : IntVecDec)
    (rest : List Byte) (h1 : decodeExt bs = none)
    (h2 : decodeIntVec bs = some (n, rest)) :
    decodeComboIV bs = some (.inr n, rest) := by
  unfold decodeComboIV
  rw [h1, h2]

/-- Where both refuse, the combined decoder refuses. -/
theorem decodeComboIV_nichts (bs : List Byte) (h1 : decodeExt bs = none)
    (h2 : decodeIntVec bs = none) :
    decodeComboIV bs = none := by
  unfold decodeComboIV
  rw [h1, h2]

/-- PINNED CHAIN: the PADDB row passes through the combined decoder
    on the selected arm. -/
theorem decodeComboIV_paddb :
    decodeComboIV (encodeIntVec (.paddbRR .xmm0 .xmm1)) =
      some (.inr (⟨.paddbRR .xmm0 .xmm1, 5⟩ : IntVecDec), []) := by
  refine decodeComboIV_erweitert _ _ _ ?_ ?_
  · exact intVec_ext_weist_paddb_zurueck
  · simpa using roundtrip_paddb .xmm0 .xmm1 []

/-! ## 17. Joint fetched packed sequence with memory witnesses.

  One concrete sequence exercises narrow-lane overflow, logical
  independence is carried by the producers, shift saturation and
  both memory shapes together: a `movdqu` load of the nonzero
  packed word, a `paddb` whose lane 0 wraps (`0x01 + 0xFF`) while
  lane 1 adds independently (`0x02 + 0x10`), a `psllq` imm8 shift,
  and a `movdqa` store that observably changes one memory byte
  while the neighboring frame byte, another XMM register and the
  flags stay put. Every step goes through its §9/§10 equation;
  the store goes through the two ordered canonical chunk writes
  (`vecWrite_aufgeteilt`), never an atomic 16-byte claim. -/

/-- Narrow-lane add pattern: lane 0 wraps, lane 1 adds
    independently, all other lanes add zero. -/
def witX4 : Vektor :=
  vecMk .b8 (fun i => if i = 0 then 255 else if i = 1 then 16 else 0)

/-- Witness readiness: OS vector state enabled. -/
def witBereit : BereitProfil := ⟨kontextReset.mxcsr, true⟩

/-- Witness legacy admission holds. -/
theorem wit_gate :
    vektorLegacyZugelassen basisHw witBereit basisCpu
      basisKontrolle = true := by
  decide

/-- Witness initial core: zeroed registers, default flags, RIP zero,
    the nonzero packed word stored at bytes zero through fifteen. -/
def witKern0 : Zustand :=
  { register := fun _ => 0
    flags := ⟨false, false, none, false, false, false⟩
    rip := 0
    speicher := vecZeugenM2 }

/-- Witness XMM file: the add pattern in xmm4, a sentinel in xmm7,
    zero elsewhere. -/
def witXmm0 : XmmDatei
  | .xmm4 => witX4
  | .xmm7 => BitVec.ofNat 128 0x0F0E0D0C0B0A090807060504030201
  | _ => 0

/-- Witness initial extended state at the FP reset context. -/
def witT0 : FpZustand := ⟨witKern0, witXmm0, kontextReset⟩

/-- The two ordered chunk writes behind the witness pattern store. -/
theorem witHw1 :
    write64 vecZeugenSpeicher 0 (vLo vecZeugenVektor) =
      some vecZeugenM1 := by
  unfold write64
  have hc : schreibbar8 vecZeugenSpeicher 0 = true := rfl
  rw [if_pos hc]
  rfl

/-- The second chunk write behind the witness pattern store. -/
theorem witHw2 :
    write64 vecZeugenM1 (vecHiAddr 0) (vHi vecZeugenVektor) =
      some vecZeugenM2 := by
  unfold write64
  have hc : schreibbar8 vecZeugenM1 (vecHiAddr 0) = true := rfl
  rw [if_pos hc]
  rfl

/-- No-wrap at the witness load address. -/
theorem witHno0 : OhneUmbruch16 (0 : Adresse) := by
  unfold OhneUmbruch16
  decide

/-- The witness load reads the nonzero packed word. -/
theorem witLd :
    vecRead vecZeugenM2 (effAddr witKern0 .rax 0) =
      some vecZeugenVektor :=
  vecRead_nach_write vecZeugenSpeicher vecZeugenM1 vecZeugenM2 0
    vecZeugenVektor witHw1 witHw2 rfl rfl witHno0

/-- Witness successor after the `movdqu` load. -/
def witT1 : FpZustand :=
  { witT0 with kern := { witT0.kern with rip := ripNach witT0.kern.rip 9 }, xmm := xmmSet witT0.xmm .xmm3 vecZeugenVektor }

/-- Witness successor after the wrapping `paddb`. -/
def witT2 : FpZustand :=
  { witT1 with kern := { witT1.kern with rip := ripNach witT1.kern.rip 5 }, xmm := xmmSet witT1.xmm .xmm3 (vecAdd .b8 vecZeugenVektor witX4) }

/-- Witness successor after the `psllq` imm8 shift. -/
def witT3 : FpZustand :=
  { witT2 with kern := { witT2.kern with rip := ripNach witT2.kern.rip 6 }, xmm := xmmSet witT2.xmm .xmm3 (vecShlQ (vecAdd .b8 vecZeugenVektor witX4) 8) }

/-- Memory after the low chunk of the witness `movdqa` store. -/
def witM4a : Speicher :=
  { vecZeugenM2 with bytes := writeBytes vecZeugenM2 (effAddr witT3.kern .rax 16) (vLo (witT3.xmm .xmm3)) }

/-- Memory after both chunks of the witness `movdqa` store. -/
def witM4 : Speicher :=
  { witM4a with bytes := writeBytes witM4a (vecHiAddr (effAddr witT3.kern .rax 16)) (vHi (witT3.xmm .xmm3)) }

/-- Witness successor after the `movdqa` store. -/
def witT4 : FpZustand :=
  { witT3 with kern := { witT3.kern with rip := ripNach witT3.kern.rip 9, speicher := witM4 } }

/-- The low chunk write behind the witness store. -/
theorem witHs1 :
    write64 witT3.kern.speicher (effAddr witT3.kern .rax 16)
      (vLo (witT3.xmm .xmm3)) = some witM4a := by
  unfold write64
  have hc : schreibbar8 witT3.kern.speicher
      (effAddr witT3.kern .rax 16) = true := by
    decide
  rw [if_pos hc]
  rfl

/-- The high chunk write behind the witness store. -/
theorem witHs2 :
    write64 witM4a (vecHiAddr (effAddr witT3.kern .rax 16))
      (vHi (witT3.xmm .xmm3)) = some witM4 := by
  unfold write64
  have hc : schreibbar8 witM4a
      (vecHiAddr (effAddr witT3.kern .rax 16)) = true := by
    decide
  rw [if_pos hc]
  rfl

/-- No #GP at the witness store address (sixteen is aligned). -/
theorem witGp :
    vektorGpFehler (effAddr witT3.kern .rax 16) .ausgerichtet =
      false := by
  decide

/-- No-wrap across the witness store footprints. -/
theorem witHno16 : OhneUmbruch16 (effAddr witT3.kern .rax 16) := by
  unfold OhneUmbruch16
  decide

/-- Step one of the joint sequence: the `movdqu` load. -/
theorem witS1 :
    stepIntVec (⟨.movdquLd .xmm3 .rax 0, 9⟩ : IntVecDec) witT0
      basisHw witBereit basisCpu basisKontrolle = some witT1 :=
  stepIntVec_movdquLd (⟨.movdquLd .xmm3 .rax 0, 9⟩ : IntVecDec) witT0
    basisHw witBereit basisCpu basisKontrolle .xmm3 .rax 0
    vecZeugenVektor (by decide) wit_gate rfl witLd

/-- Step two of the joint sequence: the wrapping `paddb`. -/
theorem witS2 :
    stepIntVec (⟨.paddbRR .xmm3 .xmm4, 5⟩ : IntVecDec) witT1
      basisHw witBereit basisCpu basisKontrolle = some witT2 :=
  stepIntVec_paddb (⟨.paddbRR .xmm3 .xmm4, 5⟩ : IntVecDec) witT1
    basisHw witBereit basisCpu basisKontrolle .xmm3 .xmm4 (by decide)
    wit_gate rfl

/-- Step three of the joint sequence: the `psllq` imm8 shift. -/
theorem witS3 :
    stepIntVec (⟨.psllqImm .xmm3 8, 6⟩ : IntVecDec) witT2
      basisHw witBereit basisCpu basisKontrolle = some witT3 :=
  stepIntVec_psllqImm (⟨.psllqImm .xmm3 8, 6⟩ : IntVecDec) witT2
    basisHw witBereit basisCpu basisKontrolle .xmm3 8 (by decide)
    wit_gate rfl

/-- Step four of the joint sequence: the `movdqa` store. -/
theorem witS4 :
    stepIntVec (⟨.movdqaSt .rax .xmm3 16, 9⟩ : IntVecDec) witT3
      basisHw witBereit basisCpu basisKontrolle = some witT4 := by
  have hwr : vecWrite witT3.kern.speicher
      (effAddr witT3.kern .rax 16) (witT3.xmm .xmm3) = some witM4 := by
    unfold vecWrite
    simp only [witHs1, witHs2]
  exact stepIntVec_movdqaSt (⟨.movdqaSt .rax .xmm3 16, 9⟩ : IntVecDec)
    witT3 basisHw witBereit basisCpu basisKontrolle .rax .xmm3 16
    witM4 (by decide) wit_gate rfl witGp hwr

/-- The vector store behind step four. -/
theorem witHwr : vecWrite witT3.kern.speicher
    (effAddr witT3.kern .rax 16) (witT3.xmm .xmm3) = some witM4 := by
  unfold vecWrite
  simp only [witHs1, witHs2]

/-- The neighboring frame byte past the store is unchanged. -/
theorem witNachbar32 :
    witT4.kern.speicher.bytes (natAdresse 32) =
      witT0.kern.speicher.bytes (natAdresse 32) := by
  have hau1 : ∀ k : Nat, k < 8 → natAdresse 32 ≠
      addrOff (effAddr witT3.kern .rax 16) k := by
    decide
  have hau2 : ∀ k : Nat, k < 8 → natAdresse 32 ≠
      addrOff (vecHiAddr (effAddr witT3.kern .rax 16)) k := by
    decide
  have hframe := vecWrite_rahmen witT3.kern.speicher witM4a witM4
    (effAddr witT3.kern .rax 16) (natAdresse 32)
    (witT3.xmm .xmm3) witHs1 witHs2 hau1 hau2
  have hspeicher : witT3.kern.speicher = vecZeugenM2 := rfl
  rw [hspeicher] at hframe
  have hspeicher4 : witT4.kern.speicher = witM4 := rfl
  have hspeicher0 : witT0.kern.speicher = vecZeugenM2 := rfl
  rw [hspeicher4, hspeicher0]
  exact hframe

/-- The sentinel XMM register survives the whole sequence. -/
theorem witXmm7 : witT4.xmm .xmm7 = witT0.xmm .xmm7 := by
  have f1 : witT1.xmm .xmm7 = witT0.xmm .xmm7 :=
    stepIntVec_movdquLd_fremd
      (⟨.movdquLd .xmm3 .rax 0, 9⟩ : IntVecDec) witT0 witT1
      basisHw witBereit basisCpu basisKontrolle .xmm3 .xmm7 .rax 0
      vecZeugenVektor (by decide) wit_gate rfl witLd witS1
      (by decide)
  have f2 : witT2.xmm .xmm7 = witT1.xmm .xmm7 :=
    stepIntVec_paddb_fremd
      (⟨.paddbRR .xmm3 .xmm4, 5⟩ : IntVecDec) witT1 witT2 basisHw
      witBereit basisCpu basisKontrolle .xmm3 .xmm4 .xmm7 (by decide)
      wit_gate rfl witS2 (by decide)
  have f3 : witT3.xmm .xmm7 = witT2.xmm .xmm7 :=
    stepIntVec_psllqImm_fremd
      (⟨.psllqImm .xmm3 8, 6⟩ : IntVecDec) witT2 witT3 basisHw
      witBereit basisCpu basisKontrolle .xmm3 .xmm7 8 (by decide)
      wit_gate rfl witS3 (by decide)
  have f4 : witT4.xmm = witT3.xmm :=
    stepIntVec_movdqaSt_xmm
      (⟨.movdqaSt .rax .xmm3 16, 9⟩ : IntVecDec) witT3 witT4 basisHw
      witBereit basisCpu basisKontrolle .rax .xmm3 16 witM4 (by decide)
      wit_gate rfl witGp witHwr witS4
  rw [f4, f3, f2, f1]

/-- The flags survive the whole sequence. -/
theorem witFlags : witT4.kern.flags = witT0.kern.flags := by
  have g1 : witT1.kern.flags = witT0.kern.flags :=
    stepIntVec_flags (⟨.movdquLd .xmm3 .rax 0, 9⟩ : IntVecDec)
      witT0 witT1 basisHw witBereit basisCpu basisKontrolle
      (by decide) wit_gate witS1
  have g2 : witT2.kern.flags = witT1.kern.flags :=
    stepIntVec_flags (⟨.paddbRR .xmm3 .xmm4, 5⟩ : IntVecDec)
      witT1 witT2 basisHw witBereit basisCpu basisKontrolle
      (by decide) wit_gate witS2
  have g3 : witT3.kern.flags = witT2.kern.flags :=
    stepIntVec_flags (⟨.psllqImm .xmm3 8, 6⟩ : IntVecDec)
      witT2 witT3 basisHw witBereit basisCpu basisKontrolle
      (by decide) wit_gate witS3
  have g4 : witT4.kern.flags = witT3.kern.flags :=
    stepIntVec_flags (⟨.movdqaSt .rax .xmm3 16, 9⟩ : IntVecDec)
      witT3 witT4 basisHw witBereit basisCpu basisKontrolle
      (by decide) wit_gate witS4
  exact g4.trans (g3.trans (g2.trans g1))

/-- JOINT WITNESS: pinned canonical bytes decode with their
    consumed lengths, the four decoded steps run on the shared XMM
    state (narrow-lane overflow, then shift, then store), one memory
    byte observably changes while the neighboring frame byte, the
    sentinel XMM register and the flags stay put. -/
theorem intVec_joint_zeuge :
    ∃ (bs1 bs2 bs3 bs4 : List Byte)
      (d1 d2 d3 d4 : IntVecDec)
      (t1 t2 t3 t4 : FpZustand),
      decodeIntVec bs1 = some (d1, []) ∧
      decodeIntVec bs2 = some (d2, []) ∧
      decodeIntVec bs3 = some (d3, []) ∧
      decodeIntVec bs4 = some (d4, []) ∧
      d1.laenge + ([] : List Byte).length = bs1.length ∧
      d2.laenge + ([] : List Byte).length = bs2.length ∧
      d3.laenge + ([] : List Byte).length = bs3.length ∧
      d4.laenge + ([] : List Byte).length = bs4.length ∧
      stepIntVec d1 witT0 basisHw witBereit basisCpu
        basisKontrolle = some t1 ∧
      stepIntVec d2 t1 basisHw witBereit basisCpu
        basisKontrolle = some t2 ∧
      stepIntVec d3 t2 basisHw witBereit basisCpu
        basisKontrolle = some t3 ∧
      stepIntVec d4 t3 basisHw witBereit basisCpu
        basisKontrolle = some t4 ∧
      t4.kern.speicher.bytes (natAdresse 18) ≠
        witT0.kern.speicher.bytes (natAdresse 18) ∧
      t4.kern.speicher.bytes (natAdresse 32) =
        witT0.kern.speicher.bytes (natAdresse 32) ∧
      t4.xmm .xmm7 = witT0.xmm .xmm7 ∧
      t4.kern.flags = witT0.kern.flags := by
  refine ⟨encodeIntVec (.movdquLd .xmm3 .rax 0),
    encodeIntVec (.paddbRR .xmm3 .xmm4),
    encodeIntVec (.psllqImm .xmm3 8),
    encodeIntVec (.movdqaSt .rax .xmm3 16),
    (⟨.movdquLd .xmm3 .rax 0, 9⟩ : IntVecDec),
    (⟨.paddbRR .xmm3 .xmm4, 5⟩ : IntVecDec),
    (⟨.psllqImm .xmm3 8, 6⟩ : IntVecDec),
    (⟨.movdqaSt .rax .xmm3 16, 9⟩ : IntVecDec),
    witT1, witT2, witT3, witT4,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact roundtrip_movdquLd .xmm3 .rax 0 []
  · exact roundtrip_paddb .xmm3 .xmm4 []
  · exact roundtrip_psllqImm .xmm3 8 []
  · exact roundtrip_movdqaSt .rax .xmm3 16 []
  · rfl
  · rfl
  · rfl
  · rfl
  · exact witS1
  · exact witS2
  · exact witS3
  · exact witS4
  · decide
  · exact witNachbar32
  · exact witXmm7
  · exact witFlags

/-! ## 18. Fetched-byte pin and concrete refusals.

  One pinned fetched step goes through actual code bytes in
  executable memory (`geholt`, never a forged decoder value); the
  negatives pin saturated-vs-masked counts, #GP alignment, missing
  byte permissions on both sides, the feature gate, high
  registers, malformed neighbors and overlapping footprints. -/

/-- Pinned code bytes: the 5-byte PADDB encoding, then zeros. -/
def witCodeBytes (a : Adresse) : Byte :=
  if a.toNat = 0 then natByte 64
  else if a.toNat = 1 then natByte 102
  else if a.toNat = 2 then natByte 15
  else if a.toNat = 3 then natByte 252
  else if a.toNat = 4 then natByte 193
  else BitVec.ofNat 8 0

/-- Pinned code memory: the code bytes, fully executable. -/
def witCodeMem : Speicher :=
  { vecZeugenSpeicher with bytes := witCodeBytes, ausfuehrbar := fun _ => true }

/-- Pinned fetch state: RIP zero over the code memory. -/
def witCodeT : FpZustand :=
  ⟨{ register := fun _ => 0
     flags := ⟨false, false, none, false, false, false⟩
     rip := 0
     speicher := witCodeMem },
   fun _ => 0, kontextReset⟩

/-- FETCHED PIN: actual code bytes fetch to the PADDB row with ten
    trailing bytes of rest. -/
theorem intVec_fetch_pin :
    fetchIntVec witCodeT (geholt witCodeT.kern) =
      some ((⟨.paddbRR .xmm0 .xmm1, 5⟩ : IntVecDec),
        List.replicate 10 (BitVec.ofNat 8 0)) := by
  decide

/-- FETCHED BRIDGE PIN: the fetched byte step IS the selected step. -/
theorem intVec_fetch_bridge_pin :
    ∃ t' : FpZustand,
      intVecByteschritt witCodeT basisHw witBereit basisCpu
          basisKontrolle = some t' ∧
        stepIntVec (⟨.paddbRR .xmm0 .xmm1, 5⟩ : IntVecDec)
            witCodeT basisHw witBereit basisCpu
            basisKontrolle = some t' := by
  have hf : fetchIntVec witCodeT (geholt witCodeT.kern) =
      some ((⟨.paddbRR .xmm0 .xmm1, 5⟩ : IntVecDec),
        List.replicate 10 (BitVec.ofNat 8 0)) := by
    decide
  have hs : stepIntVec (⟨.paddbRR .xmm0 .xmm1, 5⟩ : IntVecDec)
      witCodeT basisHw witBereit basisCpu basisKontrolle =
      some { witCodeT with kern := { witCodeT.kern with rip := ripNach witCodeT.kern.rip 5 }, xmm := xmmSet witCodeT.xmm .xmm0 (vecAdd .b8 (witCodeT.xmm .xmm0) (witCodeT.xmm .xmm1)) } :=
    stepIntVec_paddb (⟨.paddbRR .xmm0 .xmm1, 5⟩ : IntVecDec) witCodeT
      basisHw witBereit basisCpu basisKontrolle .xmm0 .xmm1
      (by decide) wit_gate rfl
  refine ⟨_, intVec_fetch_bridge _ _ _ _ _ _ _ _ hf hs, hs⟩

/-- SATURATE, NOT MASK, AT STEP LEVEL: imm8 count 64 on the nonzero
    pattern zeroes the destination (a masked count would shift by
    zero and keep it). -/
theorem intVec_neg_satt_null :
    stepIntVec (⟨.psllqImm .xmm4 64, 6⟩ : IntVecDec) witT0 basisHw
      witBereit basisCpu basisKontrolle =
      some { witT0 with kern := { witT0.kern with rip := ripNach witT0.kern.rip 6 }, xmm := xmmSet witT0.xmm .xmm4 0 } := by
  have h := stepIntVec_psllqImm
    (⟨.psllqImm .xmm4 64, 6⟩ : IntVecDec) witT0 basisHw witBereit
    basisCpu basisKontrolle .xmm4 64 (by decide) wit_gate rfl
  have hsatt : vecShlQ (witT0.xmm .xmm4) 64 = 0 := by
    have hx : witT0.xmm .xmm4 = witX4 := rfl
    rw [hx]
    exact vecShlQ_satt_null _ _ (by decide)
  rw [hsatt] at h
  exact h

/-- The saturate witness operand is nonzero (the test is not vacuous:
    masked semantics would keep it). -/
theorem intVec_neg_satt_operand : witT0.xmm .xmm4 ≠ (0 : Vektor) := by
  decide

/-- ALIGNMENT: a `movdqa` store eight past the boundary refuses with
    the #GP classification (the decoder accepts these bytes; the
    step refuses them). -/
theorem intVec_neg_ausrichtung :
    stepIntVec (⟨.movdqaSt .rax .xmm3 8, 9⟩ : IntVecDec) witT0
      basisHw witBereit basisCpu basisKontrolle = none :=
  stepIntVec_movdqaSt_gp
    (⟨.movdqaSt .rax .xmm3 8, 9⟩ : IntVecDec) witT0 basisHw
    witBereit basisCpu basisKontrolle .rax .xmm3 8 (by decide)
    wit_gate rfl (by decide)

/-- Read-only memory for the permission negatives. -/
def witMemRO : Speicher :=
  { vecZeugenSpeicher with schreibbar := fun _ => false }

/-- Write-only-blind memory for the permission negatives. -/
def witMemWO : Speicher :=
  { vecZeugenSpeicher with lesbar := fun _ => false }

/-- Read-only witness state for the store permission negative. -/
def witTRO : FpZustand :=
  { witT0 with kern := { witT0.kern with speicher := witMemRO } }

/-- Write-only-blind witness state for the load permission negative. -/
def witTWO : FpZustand :=
  { witT0 with kern := { witT0.kern with speicher := witMemWO } }

/-- PERMISSION, STORE: a `movdqa` store without write permission
    refuses (the #GP classification passes; the chunk write fails). -/
theorem intVec_neg_schreibrecht :
    stepIntVec (⟨.movdqaSt .rax .xmm3 0, 9⟩ : IntVecDec) witTRO
      basisHw witBereit basisCpu basisKontrolle = none := by
  have hgp : vektorGpFehler (effAddr witTRO.kern .rax 0)
      .ausgerichtet = false := by
    decide
  have hwr : vecWrite witMemRO (effAddr witTRO.kern .rax 0)
      (witTRO.xmm .xmm3) = none := by
    have h1 : write64 witMemRO (effAddr witTRO.kern .rax 0)
        (vLo (witTRO.xmm .xmm3)) = none := by
      unfold write64
      exact if_neg (by decide)
    unfold vecWrite
    rw [h1]
  exact stepIntVec_movdqaSt_speicher
    (⟨.movdqaSt .rax .xmm3 0, 9⟩ : IntVecDec) witTRO
    basisHw witBereit basisCpu basisKontrolle .rax .xmm3 0
    (by decide) wit_gate rfl hgp hwr

/-- PERMISSION, LOAD: a `movdqu` load without read permission refuses. -/
theorem intVec_neg_leserecht :
    stepIntVec (⟨.movdquLd .xmm3 .rax 0, 9⟩ : IntVecDec) witTWO
      basisHw witBereit basisCpu basisKontrolle = none := by
  have hrd : vecRead witMemWO (effAddr witTWO.kern .rax 0) = none := by
    have h1 : read64 witMemWO (effAddr witTWO.kern .rax 0) = none := by
      unfold read64
      exact if_neg (by decide)
    unfold vecRead
    rw [h1]
  exact stepIntVec_movdquLd_speicher
    (⟨.movdquLd .xmm3 .rax 0, 9⟩ : IntVecDec) witTWO
    basisHw witBereit basisCpu basisKontrolle .xmm3 .rax 0
    (by decide) wit_gate rfl hrd

/-- FEATURE GATE: no silicon SSE2 refuses every selected row. -/
theorem intVec_neg_gate :
    stepIntVec (⟨.paddbRR .xmm0 .xmm1, 5⟩ : IntVecDec) witT0
      basisHw witBereit ⟨false, false⟩ basisKontrolle = none :=
  stepIntVec_profil_verweigert
    (⟨.paddbRR .xmm0 .xmm1, 5⟩ : IntVecDec) witT0 basisHw witBereit
    ⟨false, false⟩ basisKontrolle (by decide)
    (vektorLegacy_ohne_cpu _ _ _ _ rfl)

/-- HIGH REGISTERS: the selected rows decode over xmm8-xmm15 through
    the canonical REX extension. -/
theorem intVec_hoch_register :
    decodeIntVec (encodeIntVec (.pandRR .xmm8 .xmm15)) =
      some ((⟨.pandRR .xmm8 .xmm15, 5⟩ : IntVecDec), []) :=
  roundtrip_pand .xmm8 .xmm15 []

/-- OVERLAP: partially overlapping vector footprints classify
    unknown and refuse alias admission (reused, not re-proved). -/
theorem intVec_neg_alias :
    klassifiziere (vecFuss (natAdresse 8192))
        (vecFuss (natAdresse 8200)) = .unbekannt ∧
      aliasZulassen (klassifiziere (vecFuss (natAdresse 8192))
        (vecFuss (natAdresse 8200))) = false :=
  vecFuss_teilueberlapp_verweigert

/- CUTS: what is not proved here.

   Manual provenance (checked 2026-10-02, local
   `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
   Intel SDM 325462-093US September 2026, REFERENCES.json
   sha256 a4a62e6a...f9168ee599f321):
   - PADD[B/W/D/Q] `66 0F FC/FD/FE/D4 /r`, SSE2 (opcode table,
     Vol. 2B 4-201); wraparound overflow and "does not set bits in
     the EFLAGS register" (description, Vol. 2B 4-202; no separate
     Flags-Affected entry exists for the plain PADD rows).
   - PAND `66 0F DB /r`, SSE2, Flags Affected None (entry, PAND
     section); POR `66 0F EB /r`, SSE2, Flags None (entry, POR
     section); PXOR legacy entry, Flags None, SIMD FP exceptions
     None, Type 4 class (entry, Vol. 2B 4-531).
   - PSLLQ `66 0F F3 /r` and `66 0F 73 /6 ib`, SSE2; PSRLQ
     `66 0F D3 /r` and `66 0F 73 /2 ib`, SSE2; saturating counts
     (`COUNT := COUNT_SRC[63:0]`, only the low 64 bits of a
     128-bit count are checked; `COUNT > 63` zeroes the
     destination), Flags None (entries, Vol. 2B 4-445/446 and
     4-469/470); PSLLQ/PSRLQ legacy operation text states
     `DEST[MAXVL-1:128] (Unmodified)`.
   - MOVDQA `66 0F 6F/7F /r`, SSE2 (opcode table, Vol. 2B 4-59);
     "The memory address must be aligned to a 16-byte boundary;
     otherwise, a general-protection exception (#GP) is generated"
     (Vol. 1 description); legacy operation `DEST[127:0] := SRC`,
     `DEST[MAXVL-1:128] (Unmodified)`; SIMD FP exceptions None;
     Type 1 class (`#GP(0)` "Legacy SSE: Memory operand is not
     16-byte aligned", Vol. 2A Table 2-18). MOVDQU `F3 0F 6F/7F
     /r`, SSE2, "except that 16-byte alignment ... is not
     required" (Vol. 1 description).
   - Legacy SSE admission (Type 4 class, Vol. 2A Table 2-21
     region): #UD iff CR0.EM set, CR4.OSFXSR clear, LOCK prefix,
     or CPUID feature flag clear; #NM iff CR0.TS set; the XCR0
     check applies to the VEX prefix only. No MXCSR word is
     required for these integer rows (integer SSE needs no
     MXCSR; scalar DOUBLE keeps its own premise in ScalarFloat).
   - MOVDQA/MOVDQU legacy entries carry no Flags-Affected
     section: flag preservation is modelled from the Operation
     text (DEST-only writes), stated as observed absence, never
     as a quoted manual sentence.
   Silicon correspondence of each bit position, fault priority
   against concurrent faults, and TSO/global visibility stay
   OPEN and are claimed nowhere.

   Coverage boundary (15 rows, enumerated, all others refused):
   PADDB/W/D/Q register-register; PAND/POR/PXOR
   register-register; PSLLQ/PSRLQ with register count and with
   imm8; MOVDQA/MOVDQU 128-bit load/store (base+disp32, pilot
   SIB rule). Refused by absence (pinned): memory-source
   arithmetic/logical/shift-count forms, the register-register
   move shape of 6F/7F, non-canonical REX (W/X bits), VEX/EVEX
   rows, MMX 64-bit forms, saturated/fused variants
   (PADDS/PSUB/PMUL/PACK/PUNPCK/PCMP/PSHUFD/MASKMOVDQU), and
   every packed-FP row. The register move shape is a documented
   gap, not an oversight: only load/store rows were selected.
   The `0F 73` group requires a zero REX.R bit (canonical
   subset; silicon ignores the bit, which is recorded, not
   modelled).
   Logical rows step at `.b64` only: bitwise ops are
   width-independent per bit, but no separate width-equality
   lemma is proved here.
   Legacy YMM upper bits (`MAXVL-1:128` unmodified) are NOT
   modelled: no YMM state exists in `FpZustand`, so the manual
   sentence is recorded, never claimed as proved. Likewise no
   MXCSR, x87, segment, paging, privilege, interrupt, SMM,
   debug, perfmon, transactional or virtualization state is
   modelled; execute/read/write permissions are per-byte data
   facts over the canonical `Speicher`, and timing is absent.
   No vector memory traffic is atomic: every load/store goes
   through the two ordered canonical 64-bit chunk accesses with
   the torn intermediate state standing (`vektorHw_teilt`,
   reused); footprint disjointness never implies atomicity or
   reordering. Per-access TSO granularity, GX refinement,
   source correspondence, budget transfer, progress and
   call-log effects stay open; `simdFreigabe` is untouched.
   The accepted stronger XCR0 gate stays valid: the legacy
   refinement is strictly weaker (witnessed), and the
   over-strength of the old gate is stated as a safe
   over-approximation, never as a hardware fault.
-/

#print axioms intVecRexByte
#print axioms encodeIntVec
#print axioms vecShlQ
#print axioms vecShrQ
#print axioms decodeIntVec
#print axioms stepIntVec
#print axioms vektorLegacyZugelassen
#print axioms vektorLegacy_verfeinert
#print axioms intVec_fetch_bridge
#print axioms decodeComboIV
#print axioms intVec_joint_zeuge
#print axioms intVec_fetch_bridge_pin
#print axioms intVec_neg_satt_null
#print axioms intVec_neg_ausrichtung
#print axioms intVec_neg_schreibrecht
#print axioms intVec_neg_leserecht
#print axioms intVec_neg_gate

end Gabbro.Grammatik.X86
