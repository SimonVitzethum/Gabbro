/-
  Byte codec pilot for the direct x86-64 validation (lane 279, wave B).
  Canonical bytes for every `Befehl` per `dokumente/x86/BYTE-PILOT.md`;
  the decoder parses bytes (never encode-equality); no hardware or
  source correspondence is claimed here.
-/
import Grammatik.X86.Typen

namespace Gabbro.Grammatik.X86

/-- Architectural register code: rax=0 through r15=15. -/
def regCode : Register → Nat
  | .rax => 0 | .rcx => 1 | .rdx => 2 | .rbx => 3
  | .rsp => 4 | .rbp => 5 | .rsi => 6 | .rdi => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11
  | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

/-- Inverse check: 4-bit code back to a register. -/
def codeReg : Nat → Option Register
  | 0 => some .rax | 1 => some .rcx | 2 => some .rdx | 3 => some .rbx
  | 4 => some .rsp | 5 => some .rbp | 6 => some .rsi | 7 => some .rdi
  | 8 => some .r8 | 9 => some .r9 | 10 => some .r10 | 11 => some .r11
  | 12 => some .r12 | 13 => some .r13 | 14 => some .r14 | 15 => some .r15
  | _ => none

/-- Decoding inverts encoding on every register. -/
theorem codeReg_regCode (r : Register) : codeReg (regCode r) = some r := by
  cases r <;> rfl

/-- Every register code fits in four bits. -/
theorem regCode_lt (r : Register) : regCode r < 16 := by
  cases r <;> decide

/-- Condition code follows `Bedingung` order 0 through 15. -/
def condCode : Bedingung → Nat
  | .o => 0 | .no => 1 | .b => 2 | .ae => 3
  | .e => 4 | .ne => 5 | .be => 6 | .a => 7
  | .s => 8 | .ns => 9 | .p => 10 | .np => 11
  | .l => 12 | .ge => 13 | .le => 14 | .g => 15

/-- Inverse check: low nibble back to a condition. -/
def codeCond : Nat → Option Bedingung
  | 0 => some .o | 1 => some .no | 2 => some .b | 3 => some .ae
  | 4 => some .e | 5 => some .ne | 6 => some .be | 7 => some .a
  | 8 => some .s | 9 => some .ns | 10 => some .p | 11 => some .np
  | 12 => some .l | 13 => some .ge | 14 => some .le | 15 => some .g
  | _ => none

/-- Decoding inverts encoding on every condition. -/
theorem codeCond_condCode (c : Bedingung) : codeCond (condCode c) = some c := by
  cases c <;> rfl

/-- Every condition code fits in four bits. -/
theorem condCode_lt (c : Bedingung) : condCode c < 16 := by
  cases c <;> decide

/-- A natural number below 256 as one byte. -/
def natByte (n : Nat) : Byte := BitVec.ofNat 8 n

/-- A byte as a natural number. -/
def byteNat (b : Byte) : Nat := b.toNat

/-- Bytes below 256 survive the round trip through `BitVec`. -/
theorem byteNat_natByte_of_lt (n : Nat) (h : n < 256) :
    byteNat (natByte n) = n := by
  unfold byteNat natByte
  rw [BitVec.toNat_ofNat]
  have h8 : (2 : Nat) ^ 8 = 256 := by decide
  rw [h8]
  exact Nat.mod_eq_of_lt h

/-- Every byte survives the round trip through `Nat`. -/
theorem natByte_byteNat (b : Byte) : natByte (byteNat b) = b := by
  apply BitVec.eq_of_toNat_eq
  unfold natByte byteNat
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt b.isLt

/-- A remainder below 256 survives the byte round trip. -/
theorem byteNat_natByte_mod (n : Nat) :
    byteNat (natByte (n % 256)) = n % 256 :=
  byteNat_natByte_of_lt _ (Nat.mod_lt _ (by decide))

/-- Every natural number survives the byte round trip modulo 256. -/
@[simp] theorem byteNat_natByte_any (n : Nat) :
    byteNat (natByte n) = n % 256 := by
  unfold byteNat natByte
  rw [BitVec.toNat_ofNat]

/-- Little-endian bytes of a 32-bit displacement. -/
def leBytes32 (d : BitVec 32) : List Byte :=
  [natByte (d.toNat % 256), natByte ((d.toNat / 256) % 256),
   natByte ((d.toNat / 65536) % 256), natByte ((d.toNat / 16777216) % 256)]

/-- Parse four little-endian bytes, returning the rest. -/
def parseLe32 : List Byte → Option (BitVec 32 × List Byte)
  | b0 :: b1 :: b2 :: b3 :: rest =>
    some (BitVec.ofNat 32 (byteNat b0 + byteNat b1 * 256 +
      byteNat b2 * 65536 + byteNat b3 * 16777216), rest)
  | _ => none

/-- Little-endian 32-bit bytes parse back to the same value. -/
theorem parseLe32_leBytes32 (d : BitVec 32) (suffix : List Byte) :
    parseLe32 (leBytes32 d ++ suffix) = some (d, suffix) := by
  have happ : leBytes32 d ++ suffix =
      natByte (d.toNat % 256) :: natByte ((d.toNat / 256) % 256) ::
      natByte ((d.toNat / 65536) % 256) ::
      natByte ((d.toNat / 16777216) % 256) :: suffix := rfl
  rw [happ]
  simp only [parseLe32, byteNat_natByte_mod]
  have hval : BitVec.ofNat 32 (d.toNat % 256 + d.toNat / 256 % 256 * 256 +
      d.toNat / 65536 % 256 * 65536 +
      d.toNat / 16777216 % 256 * 16777216) = d := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have hd := d.isLt
    omega
  rw [hval]

/-- Little-endian bytes of a 64-bit immediate. -/
def leBytes64 (v : Wort) : List Byte :=
  [natByte (v.toNat % 256), natByte ((v.toNat / 256) % 256),
   natByte ((v.toNat / 65536) % 256), natByte ((v.toNat / 16777216) % 256),
   natByte ((v.toNat / 4294967296) % 256),
   natByte ((v.toNat / 1099511627776) % 256),
   natByte ((v.toNat / 281474976710656) % 256),
   natByte ((v.toNat / 72057594037927936) % 256)]

/-- Parse eight little-endian bytes, returning the rest. -/
def parseLe64 : List Byte → Option (Wort × List Byte)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    some (BitVec.ofNat 64 (byteNat b0 + byteNat b1 * 256 +
      byteNat b2 * 65536 + byteNat b3 * 16777216 +
      byteNat b4 * 4294967296 + byteNat b5 * 1099511627776 +
      byteNat b6 * 281474976710656 +
      byteNat b7 * 72057594037927936), rest)
  | _ => none

/-- Little-endian 64-bit bytes parse back to the same value. -/
theorem parseLe64_leBytes64 (v : Wort) (suffix : List Byte) :
    parseLe64 (leBytes64 v ++ suffix) = some (v, suffix) := by
  have happ : leBytes64 v ++ suffix =
      natByte (v.toNat % 256) :: natByte ((v.toNat / 256) % 256) ::
      natByte ((v.toNat / 65536) % 256) ::
      natByte ((v.toNat / 16777216) % 256) ::
      natByte ((v.toNat / 4294967296) % 256) ::
      natByte ((v.toNat / 1099511627776) % 256) ::
      natByte ((v.toNat / 281474976710656) % 256) ::
      natByte ((v.toNat / 72057594037927936) % 256) :: suffix := rfl
  rw [happ]
  simp only [parseLe64, byteNat_natByte_mod]
  have hval : BitVec.ofNat 64 (v.toNat % 256 + v.toNat / 256 % 256 * 256 +
      v.toNat / 65536 % 256 * 65536 + v.toNat / 16777216 % 256 * 16777216 +
      v.toNat / 4294967296 % 256 * 4294967296 +
      v.toNat / 1099511627776 % 256 * 1099511627776 +
      v.toNat / 281474976710656 % 256 * 281474976710656 +
      v.toNat / 72057594037927936 % 256 * 72057594037927936) = v := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have hv := v.isLt
    omega
  rw [hval]

/-- The displacement encoding is four bytes. -/
theorem length_leBytes32 (d : BitVec 32) : (leBytes32 d).length = 4 := rfl

/-- The immediate encoding is eight bytes. -/
theorem length_leBytes64 (v : Wort) : (leBytes64 v).length = 8 := rfl

/-- Little-endian 32-bit bytes in cons form parse back to the same value. -/
theorem parseLe32_cons (d : BitVec 32) (suffix : List Byte) :
    parseLe32 (natByte (d.toNat % 256) :: natByte ((d.toNat / 256) % 256) ::
      natByte ((d.toNat / 65536) % 256) ::
      natByte ((d.toNat / 16777216) % 256) :: suffix) = some (d, suffix) := by
  simp only [parseLe32, byteNat_natByte_mod]
  have hval : BitVec.ofNat 32 (d.toNat % 256 + d.toNat / 256 % 256 * 256 +
      d.toNat / 65536 % 256 * 65536 +
      d.toNat / 16777216 % 256 * 16777216) = d := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have hd := d.isLt
    omega
  rw [hval]

/-- Little-endian 64-bit bytes in cons form parse back to the same value. -/
theorem parseLe64_cons (v : Wort) (suffix : List Byte) :
    parseLe64 (natByte (v.toNat % 256) :: natByte ((v.toNat / 256) % 256) ::
      natByte ((v.toNat / 65536) % 256) ::
      natByte ((v.toNat / 16777216) % 256) ::
      natByte ((v.toNat / 4294967296) % 256) ::
      natByte ((v.toNat / 1099511627776) % 256) ::
      natByte ((v.toNat / 281474976710656) % 256) ::
      natByte ((v.toNat / 72057594037927936) % 256) :: suffix) =
      some (v, suffix) := by
  simp only [parseLe64, byteNat_natByte_mod]
  have hval : BitVec.ofNat 64 (v.toNat % 256 + v.toNat / 256 % 256 * 256 +
      v.toNat / 65536 % 256 * 65536 + v.toNat / 16777216 % 256 * 16777216 +
      v.toNat / 4294967296 % 256 * 4294967296 +
      v.toNat / 1099511627776 % 256 * 1099511627776 +
      v.toNat / 281474976710656 % 256 * 281474976710656 +
      v.toNat / 72057594037927936 % 256 * 72057594037927936) = v := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have hv := v.isLt
    omega
  rw [hval]

/-- High bit of a register code (the REX R/B extension). -/
def regHigh (r : Register) : Nat := regCode r / 8

/-- Low three bits of a register code (ModRM field). -/
def regLow (r : Register) : Nat := regCode r % 8

/-- The extension bit is 0 or 1. -/
theorem regHigh_lt (r : Register) : regHigh r < 2 := by
  cases r <;> decide

/-- The low field is a 3-bit value. -/
theorem regLow_lt (r : Register) : regLow r < 8 := by
  cases r <;> decide

/-- High and low bits reassemble the register code. -/
theorem regCode_split (r : Register) :
    regCode r = regHigh r * 8 + regLow r := by
  cases r <;> decide

/-- REX.W prefix with R=rh and B=bh extension bits (X=0). -/
def rexByte (rh bh : Nat) : Byte := natByte (72 + 4 * rh + bh)

/-- ModRM byte with mod=3 (register-direct) over low 3-bit codes. -/
def modrmReg (rl rm : Nat) : Byte := natByte (192 + 8 * (rl % 8) + rm % 8)

/-- ModRM byte with mod=2 (base plus disp32) over low 3-bit codes. -/
def modrmMem (rl rm : Nat) : Byte := natByte (128 + 8 * (rl % 8) + rm % 8)

/-- Canonical byte encoding of one pilot instruction (`BYTE-PILOT.md`).
    Multi-byte immediates and displacements are little endian. -/
def encode : Befehl → List Byte
  | .movImm64 dst v =>
    natByte (72 + regCode dst / 8) :: natByte (184 + regCode dst % 8) ::
      leBytes64 v
  | .movReg64 dst src =>
    [rexByte (regHigh src) (regHigh dst), natByte 137,
     modrmReg (regLow src) (regLow dst)]
  | .addReg64 dst src =>
    [rexByte (regHigh src) (regHigh dst), natByte 1,
     modrmReg (regLow src) (regLow dst)]
  | .subReg64 dst src =>
    [rexByte (regHigh src) (regHigh dst), natByte 41,
     modrmReg (regLow src) (regLow dst)]
  | .xorReg64 dst src =>
    [rexByte (regHigh src) (regHigh dst), natByte 49,
     modrmReg (regLow src) (regLow dst)]
  | .cmpReg64 lhs rhs =>
    [rexByte (regHigh rhs) (regHigh lhs), natByte 57,
     modrmReg (regLow rhs) (regLow lhs)]
  | .load64 dst base d =>
    let head := [rexByte (regHigh dst) (regHigh base), natByte 139,
      modrmMem (regLow dst) (regLow base)]
    if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
    else head ++ leBytes32 d
  | .store64 base src d =>
    let head := [rexByte (regHigh src) (regHigh base), natByte 137,
      modrmMem (regLow src) (regLow base)]
    if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
    else head ++ leBytes32 d
  | .jump32 d => natByte 233 :: leBytes32 d
  | .jumpIf32 c d => natByte 15 :: natByte (128 + condCode c) :: leBytes32 d
  | .call32 d => natByte 232 :: leBytes32 d
  | .push64 src =>
    if regCode src < 8 then [natByte (80 + regCode src)]
    else [natByte 65, natByte (80 + (regCode src - 8))]
  | .pop64 dst =>
    if regCode dst < 8 then [natByte (88 + regCode dst)]
    else [natByte 65, natByte (88 + (regCode dst - 8))]
  | .ret => [natByte 195]

/-- Every canonical encoding is between 1 and 15 bytes long. -/
theorem encode_len (b : Befehl) :
    1 ≤ (encode b).length ∧ (encode b).length ≤ 15 := by
  cases b with
  | movImm64 dst v => exact show 1 ≤ 10 ∧ 10 ≤ 15 from by decide
  | movReg64 dst src => exact show 1 ≤ 3 ∧ 3 ≤ 15 from by decide
  | addReg64 dst src => exact show 1 ≤ 3 ∧ 3 ≤ 15 from by decide
  | subReg64 dst src => exact show 1 ≤ 3 ∧ 3 ≤ 15 from by decide
  | xorReg64 dst src => exact show 1 ≤ 3 ∧ 3 ≤ 15 from by decide
  | cmpReg64 lhs rhs => exact show 1 ≤ 3 ∧ 3 ≤ 15 from by decide
  | load64 dst base d =>
    simp only [encode]
    split
    · exact show 1 ≤ 8 ∧ 8 ≤ 15 from by decide
    · exact show 1 ≤ 7 ∧ 7 ≤ 15 from by decide
  | store64 base src d =>
    simp only [encode]
    split
    · exact show 1 ≤ 8 ∧ 8 ≤ 15 from by decide
    · exact show 1 ≤ 7 ∧ 7 ≤ 15 from by decide
  | jump32 d => exact show 1 ≤ 5 ∧ 5 ≤ 15 from by decide
  | jumpIf32 c d => exact show 1 ≤ 6 ∧ 6 ≤ 15 from by decide
  | call32 d => exact show 1 ≤ 5 ∧ 5 ≤ 15 from by decide
  | push64 src =>
    simp only [encode]
    split
    · exact show 1 ≤ 1 ∧ 1 ≤ 15 from by decide
    · exact show 1 ≤ 2 ∧ 2 ≤ 15 from by decide
  | pop64 dst =>
    simp only [encode]
    split
    · exact show 1 ≤ 1 ∧ 1 ≤ 15 from by decide
    · exact show 1 ≤ 2 ∧ 2 ≤ 15 from by decide
  | ret => exact show 1 ≤ 1 ∧ 1 ≤ 15 from by decide

/-- Decode one register-direct operation after REX, opcode and ModRM.
    The first result register always comes from the ModRM r/m side:
    destination for mov/add/sub/xor, left-hand side for cmp. -/
def decodeRegReg (op rBit bBit reg rm : Nat) (rest : List Byte) :
    Option (Decodiert × List Byte) :=
  match codeReg (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
  | some rs, some rd =>
    match op with
    | 137 => some (⟨.movReg64 rd rs, 3⟩, rest)
    | 1 => some (⟨.addReg64 rd rs, 3⟩, rest)
    | 41 => some (⟨.subReg64 rd rs, 3⟩, rest)
    | 49 => some (⟨.xorReg64 rd rs, 3⟩, rest)
    | 57 => some (⟨.cmpReg64 rd rs, 3⟩, rest)
    | _ => none
  | _, _ => none

/-- Decode one base-plus-displacement access after REX, opcode and ModRM.
    Length 8 with the SIB byte, 7 without; both refused when truncated. -/
def decodeMem (isLoad : Bool) (rBit bBit reg rm : Nat) :
    List Byte → Option (Decodiert × List Byte)
  | [] => none
  | b :: rest =>
    if rm == 4 then
      if byteNat b == 36 then
        match parseLe32 rest with
        | some (d, rest') =>
          match codeReg (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
          | some rr, some rb =>
            if isLoad then some (⟨.load64 rr rb d, 8⟩, rest')
            else some (⟨.store64 rb rr d, 8⟩, rest')
          | _, _ => none
        | none => none
      else none
    else
      match parseLe32 (b :: rest) with
      | some (d, rest') =>
        match codeReg (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
        | some rr, some rb =>
          if isLoad then some (⟨.load64 rr rb d, 7⟩, rest')
          else some (⟨.store64 rb rr d, 7⟩, rest')
        | _, _ => none
      | none => none

/-- Dispatch on the ModRM mod field after REX and opcode.
    Only mod=3 (register-direct, five opcodes) and mod=2 (disp32,
    load/store only) are canonical; every other mode refuses. -/
def decodeModrm (rBit bBit op : Nat) :
    List Byte → Option (Decodiert × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    match byteNat m / 64 with
    | 3 => decodeRegReg op rBit bBit reg rm rest
    | 2 =>
      match op with
      | 137 => decodeMem false rBit bBit reg rm rest
      | 139 => decodeMem true rBit bBit reg rm rest
      | _ => none
    | _ => none

/-- Decode after one canonical REX.W prefix (X=0). -/
def decodeRex (rBit bBit : Nat) :
    List Byte → Option (Decodiert × List Byte)
  | [] => none
  | op :: rest =>
    let n := byteNat op
    if 184 ≤ n ∧ n < 192 then
      match codeReg (bBit * 8 + (n - 184)) with
      | some dst =>
        match parseLe64 rest with
        | some (v, rest') => some (⟨.movImm64 dst v, 10⟩, rest')
        | none => none
      | none => none
    else
      match n with
      | 137 => decodeModrm rBit bBit 137 rest
      | 1 => decodeModrm rBit bBit 1 rest
      | 41 => decodeModrm rBit bBit 41 rest
      | 49 => decodeModrm rBit bBit 49 rest
      | 57 => decodeModrm rBit bBit 57 rest
      | 139 => decodeModrm rBit bBit 139 rest
      | _ => none

/-- Decode the first canonical instruction, returning it with its
    consumed length and the remaining bytes. Only canonical encodings
    are accepted; anything else is refused with `none`. -/
def decode : List Byte → Option (Decodiert × List Byte)
  | [] => none
  | b :: rest =>
    match byteNat b with
    | 195 => some (⟨.ret, 1⟩, rest)
    | 232 =>
      match parseLe32 rest with
      | some (d, rest') => some (⟨.call32 d, 5⟩, rest')
      | none => none
    | 233 =>
      match parseLe32 rest with
      | some (d, rest') => some (⟨.jump32 d, 5⟩, rest')
      | none => none
    | 15 =>
      match rest with
      | [] => none
      | b2 :: rest2 =>
        let c := byteNat b2
        if 128 ≤ c ∧ c < 144 then
          match codeCond (c - 128) with
          | some cond =>
            match parseLe32 rest2 with
            | some (d, rest') => some (⟨.jumpIf32 cond d, 6⟩, rest')
            | none => none
          | none => none
        else none
    | 65 =>
      match rest with
      | [] => none
      | b2 :: rest2 =>
        let v := byteNat b2
        if 80 ≤ v ∧ v < 88 then
          match codeReg (v - 80 + 8) with
          | some r => some (⟨.push64 r, 2⟩, rest2)
          | none => none
        else if 88 ≤ v ∧ v < 96 then
          match codeReg (v - 88 + 8) with
          | some r => some (⟨.pop64 r, 2⟩, rest2)
          | none => none
        else none
    | 72 => decodeRex 0 0 rest
    | 73 => decodeRex 0 1 rest
    | 76 => decodeRex 1 0 rest
    | 77 => decodeRex 1 1 rest
    | n =>
      if 80 ≤ n ∧ n < 88 then
        match codeReg (n - 80) with
        | some r => some (⟨.push64 r, 1⟩, rest)
        | none => none
      else if 88 ≤ n ∧ n < 96 then
        match codeReg (n - 88) with
        | some r => some (⟨.pop64 r, 1⟩, rest)
        | none => none
      else none

/-- Round trip for `ret`. -/
theorem roundtrip_ret (suffix : List Byte) :
    decode (encode .ret ++ suffix) =
      some (⟨.ret, (encode .ret).length⟩, suffix) := by
  simp [encode, decode]

/-- Round trip for `jump32`. -/
theorem roundtrip_jump32 (d : BitVec 32) (suffix : List Byte) :
    decode (encode (.jump32 d) ++ suffix) =
      some (⟨.jump32 d, (encode (.jump32 d)).length⟩, suffix) := by
  simp [encode, decode, parseLe32_leBytes32, length_leBytes32]

/-- Round trip for `movReg64`. -/
theorem roundtrip_movReg64 (dst src : Register) (suffix : List Byte) :
    decode (encode (.movReg64 dst src) ++ suffix) =
      some (⟨.movReg64 dst src, (encode (.movReg64 dst src)).length⟩, suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for `addReg64`. -/
theorem roundtrip_addReg64 (dst src : Register) (suffix : List Byte) :
    decode (encode (.addReg64 dst src) ++ suffix) =
      some (⟨.addReg64 dst src, (encode (.addReg64 dst src)).length⟩, suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for `subReg64`. -/
theorem roundtrip_subReg64 (dst src : Register) (suffix : List Byte) :
    decode (encode (.subReg64 dst src) ++ suffix) =
      some (⟨.subReg64 dst src, (encode (.subReg64 dst src)).length⟩, suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for `xorReg64`. -/
theorem roundtrip_xorReg64 (dst src : Register) (suffix : List Byte) :
    decode (encode (.xorReg64 dst src) ++ suffix) =
      some (⟨.xorReg64 dst src, (encode (.xorReg64 dst src)).length⟩, suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for `cmpReg64`. -/
theorem roundtrip_cmpReg64 (lhs rhs : Register) (suffix : List Byte) :
    decode (encode (.cmpReg64 lhs rhs) ++ suffix) =
      some (⟨.cmpReg64 lhs rhs, (encode (.cmpReg64 lhs rhs)).length⟩, suffix) := by
  cases lhs <;> cases rhs <;> rfl

/-- Round trip for `call32`. -/
theorem roundtrip_call32 (d : BitVec 32) (suffix : List Byte) :
    decode (encode (.call32 d) ++ suffix) =
      some (⟨.call32 d, (encode (.call32 d)).length⟩, suffix) := by
  simp [encode, decode, parseLe32_leBytes32, length_leBytes32]

/-- Round trip for `jumpIf32`. -/
theorem roundtrip_jumpIf32 (c : Bedingung) (d : BitVec 32)
    (suffix : List Byte) :
    decode (encode (.jumpIf32 c d) ++ suffix) =
      some (⟨.jumpIf32 c d, (encode (.jumpIf32 c d)).length⟩, suffix) := by
  cases c <;> simp [encode, decode, condCode, codeCond,
    parseLe32_leBytes32, length_leBytes32]

/-- Round trip for `push64`. -/
theorem roundtrip_push64 (src : Register) (suffix : List Byte) :
    decode (encode (.push64 src) ++ suffix) =
      some (⟨.push64 src, (encode (.push64 src)).length⟩, suffix) := by
  cases src <;> rfl

/-- Round trip for `pop64`. -/
theorem roundtrip_pop64 (dst : Register) (suffix : List Byte) :
    decode (encode (.pop64 dst) ++ suffix) =
      some (⟨.pop64 dst, (encode (.pop64 dst)).length⟩, suffix) := by
  cases dst <;> rfl

/-- Round trip for `movImm64`. -/
theorem roundtrip_movImm64 (dst : Register) (v : Wort)
    (suffix : List Byte) :
    decode (encode (.movImm64 dst v) ++ suffix) =
      some (⟨.movImm64 dst v, (encode (.movImm64 dst v)).length⟩, suffix) := by
  cases dst <;> simp [encode, decode, decodeRex, regCode, codeReg,
    parseLe64_cons, leBytes64]

-- Exhaustive register-pair round trips need a larger heartbeat
-- budget: every one of the 256 architectural combinations is checked.
set_option maxHeartbeats 4000000

/-- Round trip for `load64`, both SIB and non-SIB shapes. -/
theorem roundtrip_load64 (dst base : Register) (d : BitVec 32)
    (suffix : List Byte) :
    decode (encode (.load64 dst base d) ++ suffix) =
      some (⟨.load64 dst base d, (encode (.load64 dst base d)).length⟩,
        suffix) := by
  cases dst <;> cases base <;>
    simp [encode, decode, decodeRex, decodeModrm, decodeMem,
      codeReg, regCode, regHigh, regLow, rexByte, modrmMem, leBytes32,
      parseLe32_cons]

/-- Round trip for `store64`, both SIB and non-SIB shapes. -/
theorem roundtrip_store64 (base src : Register) (d : BitVec 32)
    (suffix : List Byte) :
    decode (encode (.store64 base src d) ++ suffix) =
      some (⟨.store64 base src d, (encode (.store64 base src d)).length⟩,
        suffix) := by
  cases base <;> cases src <;>
    simp [encode, decode, decodeRex, decodeModrm, decodeMem,
      codeReg, regCode, regHigh, regLow, rexByte, modrmMem, leBytes32,
      parseLe32_cons]

set_option maxHeartbeats 200000

/-- Decoding inverts encoding on every pilot instruction, over any suffix.
    The decoded length is the consumed prefix length. -/
theorem roundtrip (b : Befehl) (suffix : List Byte) :
    decode (encode b ++ suffix) =
      some (⟨b, (encode b).length⟩, suffix) := by
  cases b with
  | movImm64 dst v => exact roundtrip_movImm64 dst v suffix
  | movReg64 dst src => exact roundtrip_movReg64 dst src suffix
  | addReg64 dst src => exact roundtrip_addReg64 dst src suffix
  | subReg64 dst src => exact roundtrip_subReg64 dst src suffix
  | xorReg64 dst src => exact roundtrip_xorReg64 dst src suffix
  | cmpReg64 lhs rhs => exact roundtrip_cmpReg64 lhs rhs suffix
  | load64 dst base d => exact roundtrip_load64 dst base d suffix
  | store64 base src d => exact roundtrip_store64 base src d suffix
  | jump32 d => exact roundtrip_jump32 d suffix
  | jumpIf32 c d => exact roundtrip_jumpIf32 c d suffix
  | call32 d => exact roundtrip_call32 d suffix
  | push64 src => exact roundtrip_push64 src suffix
  | pop64 dst => exact roundtrip_pop64 dst suffix
  | ret => exact roundtrip_ret suffix

/-- A successful round trip consumes exactly its prefix, within 1..15. -/
theorem roundtrip_len_ok (b : Befehl) (suffix : List Byte) :
    ∃ (n : Nat) (rest : List Byte),
      decode (encode b ++ suffix) = some (⟨b, n⟩, rest) ∧
        n + rest.length = (encode b ++ suffix).length ∧
        1 ≤ n ∧ n ≤ 15 := by
  refine ⟨(encode b).length, suffix, roundtrip b suffix, ?_, ?_, ?_⟩
  · rw [List.length_append]
  · exact (encode_len b).1
  · exact (encode_len b).2

/-- The empty input decodes to nothing. -/
theorem decode_nichts_leer : decode [] = none := rfl

/-- A lone REX prefix is truncated. -/
theorem decode_nichts_rex_allein : decode [natByte 72] = none := rfl

/-- A jump with a short displacement is truncated. -/
theorem decode_nichts_sprung_kurz :
    decode [natByte 233, natByte 1] = none := rfl

/-- A lone two-byte prefix is truncated. -/
theorem decode_nichts_zweibyte_allein : decode [natByte 15] = none := rfl

/-- A lone extension prefix is truncated. -/
theorem decode_nichts_erweiterung_allein : decode [natByte 65] = none := rfl

/-- An unknown opcode is refused. -/
theorem decode_nichts_unbekannt : decode [natByte 255] = none := rfl

/-- A REX prefix with the X bit set is not canonical. -/
theorem decode_nichts_rex_x :
    decode [natByte 74, natByte 137, natByte 192] = none := rfl

/-- A register move without REX.W is not canonical. -/
theorem decode_nichts_ohne_rex :
    decode [natByte 137, natByte 192] = none := rfl

/-- A mod=0 memory form is not canonical. -/
theorem decode_nichts_modus_null :
    decode [natByte 72, natByte 137, natByte 0] = none := rfl

/-- A register-direct load is not canonical (loads use mod=2). -/
theorem decode_nichts_lade_register :
    decode [natByte 72, natByte 139, natByte 192] = none := rfl

/-- A wrong SIB byte is refused. -/
theorem decode_nichts_sib_falsch :
    decode [natByte 72, natByte 139, natByte 132, natByte 0,
      natByte 0, natByte 0, natByte 0, natByte 0] = none := rfl

/-- A present SIB byte with a short displacement is truncated. -/
theorem decode_nichts_sib_kurz :
    decode [natByte 72, natByte 139, natByte 132, natByte 36] = none := rfl

/-- A short branch form is not canonical. -/
theorem decode_nichts_kurzsprung :
    decode [natByte 235, natByte 0] = none := rfl

/-- An operand-size prefix is not canonical. -/
theorem decode_nichts_vorsatz :
    decode [natByte 102, natByte 195] = none := rfl

/-- A non-branch second byte after 0F is refused. -/
theorem decode_nichts_zweite_kein_sprung :
    decode [natByte 15, natByte 144, natByte 0, natByte 0,
      natByte 0, natByte 0] = none := rfl

/-- Pinned bytes: immediate to the extended register r8. -/
theorem pin_movImm64_r8 :
    encode (.movImm64 .r8 0x0102030405060708) =
      [natByte 73, natByte 184, natByte 8, natByte 7, natByte 6,
       natByte 5, natByte 4, natByte 3, natByte 2, natByte 1] := by
  decide

/-- Pinned decode: immediate to r8. -/
theorem pin_movImm64_r8_dekode :
    decode [natByte 73, natByte 184, natByte 8, natByte 7, natByte 6,
      natByte 5, natByte 4, natByte 3, natByte 2, natByte 1] =
      some ((⟨.movImm64 .r8 0x0102030405060708, 10⟩ : Decodiert), []) := by
  decide

/-- Pinned bytes: binary operation over two extended registers. -/
theorem pin_addReg64_erweitert :
    encode (.addReg64 .r9 .r15) =
      [natByte 77, natByte 1, natByte 249] := by
  decide

/-- Pinned decode: binary operation over two extended registers. -/
theorem pin_addReg64_erweitert_dekode :
    decode [natByte 77, natByte 1, natByte 249] =
      some ((⟨.addReg64 .r9 .r15, 3⟩ : Decodiert), []) := by
  decide

/-- Pinned bytes: load through rsp needs the SIB byte. -/
theorem pin_load64_rsp :
    encode (.load64 .rax .rsp 16) =
      [natByte 72, natByte 139, natByte 132, natByte 36,
       natByte 16, natByte 0, natByte 0, natByte 0] := by
  decide

/-- Pinned decode: load through rsp. -/
theorem pin_load64_rsp_dekode :
    decode [natByte 72, natByte 139, natByte 132, natByte 36,
      natByte 16, natByte 0, natByte 0, natByte 0] =
      some ((⟨.load64 .rax .rsp 16, 8⟩ : Decodiert), []) := by
  decide

/-- Pinned bytes: store through r12 needs the SIB byte. -/
theorem pin_store64_r12 :
    encode (.store64 .r12 .rdx 0) =
      [natByte 73, natByte 137, natByte 148, natByte 36,
       natByte 0, natByte 0, natByte 0, natByte 0] := by
  decide

/-- Pinned decode: store through r12. -/
theorem pin_store64_r12_dekode :
    decode [natByte 73, natByte 137, natByte 148, natByte 36,
      natByte 0, natByte 0, natByte 0, natByte 0] =
      some ((⟨.store64 .r12 .rdx 0, 8⟩ : Decodiert), []) := by
  decide

/-- Pinned bytes: load through rbp keeps its disp32 (never RIP-relative). -/
theorem pin_load64_rbp :
    encode (.load64 .rcx .rbp 0) =
      [natByte 72, natByte 139, natByte 141,
       natByte 0, natByte 0, natByte 0, natByte 0] := by
  decide

/-- Pinned decode: load through rbp. -/
theorem pin_load64_rbp_dekode :
    decode [natByte 72, natByte 139, natByte 141,
      natByte 0, natByte 0, natByte 0, natByte 0] =
      some ((⟨.load64 .rcx .rbp 0, 7⟩ : Decodiert), []) := by
  decide

/-- Pinned bytes: store through r13 keeps its disp32. -/
theorem pin_store64_r13 :
    encode (.store64 .r13 .r8 1) =
      [natByte 77, natByte 137, natByte 133,
       natByte 1, natByte 0, natByte 0, natByte 0] := by
  decide

/-- Pinned decode: store through r13. -/
theorem pin_store64_r13_dekode :
    decode [natByte 77, natByte 137, natByte 133,
      natByte 1, natByte 0, natByte 0, natByte 0] =
      some ((⟨.store64 .r13 .r8 1, 7⟩ : Decodiert), []) := by
  decide

/-- Pinned bytes: jump with a negative displacement (-5). -/
theorem pin_jump32_negativ :
    encode (.jump32 (BitVec.ofNat 32 4294967291)) =
      [natByte 233, natByte 251, natByte 255, natByte 255, natByte 255] := by
  decide

/-- Pinned decode: jump with a negative displacement. -/
theorem pin_jump32_negativ_dekode :
    decode [natByte 233, natByte 251, natByte 255, natByte 255, natByte 255] =
      some ((⟨.jump32 (BitVec.ofNat 32 4294967291), 5⟩ : Decodiert), []) := by
  decide

/-- Pinned bytes: push of a high register. -/
theorem pin_push64_r8 :
    encode (.push64 .r8) = [natByte 65, natByte 80] := by
  decide

/-- Pinned decode: push of a high register. -/
theorem pin_push64_r8_dekode :
    decode [natByte 65, natByte 80] =
      some ((⟨.push64 .r8, 2⟩ : Decodiert), []) := by
  decide

/-- Pinned bytes: pop of a high register. -/
theorem pin_pop64_r15 :
    encode (.pop64 .r15) = [natByte 65, natByte 95] := by
  decide

/-- Pinned decode: pop of a high register. -/
theorem pin_pop64_r15_dekode :
    decode [natByte 65, natByte 95] =
      some ((⟨.pop64 .r15, 2⟩ : Decodiert), []) := by
  decide

/-- Pinned bytes: return. -/
theorem pin_ret : encode .ret = [natByte 195] := by decide

/-- Pinned decode: return. -/
theorem pin_ret_dekode :
    decode [natByte 195] =
      some ((⟨.ret, 1⟩ : Decodiert), []) := by
  decide

/- CUTS:
   Proved here: canonical bytes for all 14 `Befehl` constructors with
   generic register/condition inverses, little-endian round trips,
   the universal round trip `roundtrip` (decoded length is the consumed
   prefix length), the 1..15 bound `encode_len`, the packaged
   `roundtrip_len_ok`, explicit refusals of truncated, non-canonical
   and corrupted inputs, and independently pinned bytes for r8
   immediates, extended-register arithmetic, rsp/r12 SIB, rbp/r13
   disp32, a negative branch displacement, high-register push/pop
   and RET.
   NOT proved here, and not claimed:
   - No hardware correspondence: the round trip is self-consistency of
     this pilot against BYTE-PILOT.md, not x86 truth.
   - No source correspondence, no execution, no TSO bridge, no ABI or
     whole-image coverage, no cost transfer.
   - The general length soundness (every successful decode of an
     ARBITRARY input consumes exactly its stated length within 1..15)
     is proved only for round-trip instances (`roundtrip_len_ok`).
   - Non-canonical but architecturally valid encodings are refused by
     construction; correspondence of that refusal set to hardware is open.
-/

#print axioms codeReg_regCode
#print axioms codeCond_condCode
#print axioms parseLe32_leBytes32
#print axioms parseLe64_leBytes64
#print axioms encode_len
#print axioms roundtrip
#print axioms roundtrip_len_ok
#print axioms pin_movImm64_r8_dekode
#print axioms pin_jump32_negativ_dekode
#print axioms decode_nichts_sib_falsch

end Gabbro.Grammatik.X86
