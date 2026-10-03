/-
  File:      Grammatik/X86/CompactImm8Add.lean
  Subject:   Canonical byte codec and execution connection for the compact
    64-bit ADD with sign-extended imm8 (lane 748).

  Covers exactly one row: `REX.W + 83 /0 ib`, ADD r64, imm8, register-direct
  (ModRM mod = 3, extension digit /0). Provenance: Intel SDM combined
  volumes 1-4, edition 325462-093US (September 2026), local snapshot
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`, Vol. 2A 3-14
  "ADD-Add": opcode table "REX.W + 83 /0 ib  ADD r/m64, imm8 ... Add
  sign-extended imm8 to r/m64"; Description "When an immediate value is used
  as an operand, it is sign-extended to the length of the destination
  operand format"; Operation "DEST := DEST + SRC"; Flags Affected "The OF,
  SF, ZF, AF, CF, and PF flags are set according to the result."

  Scope: register destination only (r/m64 with a register; memory forms,
  16/32-bit 83 rows, the 81 imm32 row and the 05/04 accumulator rows stay
  open and refuse here). Value and flags reuse the canonical `Wort`
  vocabulary (`sext`, `trunc`, `cfAdd`, `ofAdd`, `zfTest`, `sfTest`,
  `parityEven`) and the accepted `add64` identities; AF is modelled as
  undefined (`none`), never invented -- a deliberate conservative gap
  against the manual, booked in CUTS. No new word/register/state types, no
  `Befehl` change, no second evaluator of the pilot ADD: at 64 bits the
  value and every defined flag ARE the accepted `add64` ones.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.ShiftLogic

namespace Gabbro.Grammatik.X86

/-- Sign-extended imm8 as a full word: the low byte sign-extended through
    the canonical `sext .b8` (Vol. 2A 3-14 Description: the immediate "is
    sign-extended to the length of the destination operand format"). -/
def immSext (n : Nat) : Wort := sext .b8 (BitVec.ofNat 64 n)

/-- Pin: the largest positive imm8 stays positive. -/
theorem pin_immSext_7f : immSext 127 = 127 := by
  decide

/-- Pin: the smallest negative imm8 fills with ones. -/
theorem pin_immSext_80 : immSext 128 = 0xFFFFFFFFFFFFFF80 := by
  decide

/-- Pin: imm8 -1 (0xFF) fills the whole word. -/
theorem pin_immSext_ff : immSext 255 = 0xFFFFFFFFFFFFFFFF := by
  decide

/-- Pin: imm8 zero extends to zero. -/
theorem pin_immSext_00 : immSext 0 = 0 := by
  decide

/-! ## Width-generic value and flags.

  The REX.W row runs at `.b64`; the helpers take the width explicitly so
  the per-width CF/OF/SF/ZF/PF shape is stated once (Vol. 2A 3-14
  Operation "DEST := DEST + SRC" with the immediate sign-extended).
  Carry and overflow read the truncated operands at the named width;
  SF is the width-correct `negB b` (bit 63 alone misclassifies narrow
  results). AF is `none` at every width: undefined is left undefined,
  never invented (the manual lists AF among the affected flags; leaving
  it `none` is the deliberate conservative gap booked in CUTS). -/

/-- Width-generic ADD-with-imm8 value: truncated operands added, result
    truncated to the named width. -/
def addImmOp (b : Breite) (x : Wort) (n : Nat) : Wort :=
  trunc b (trunc b x + immSext n)

/-- Width-generic ADD-with-imm8 flags: CF/OF/SF/ZF/PF from the canonical
    tests at the named width, AF always `none`. -/
def addImmFlags (b : Breite) (x : Wort) (n : Nat) : Flags :=
  let r := addImmOp b x n
  { cf := decide ((trunc b x).toNat + (trunc b (immSext n)).toNat ≥ 2 ^ b.bits)
    pf := parityEven r, af := none, zf := zfTest r, sf := negB b r,
    of := ofAdd (negB b (trunc b x)) (negB b (trunc b (immSext n)))
      (negB b r) }

/-! ## Per-width identities: AF stays none, 64-bit value is plain addition. -/

/-- AF stays `none` at every width: undefined, never invented. -/
theorem addImmFlags_af (b : Breite) (x : Wort) (n : Nat) :
    (addImmFlags b x n).af = none := rfl

/-- At 64 bits the value is the plain modular sum with the
    sign-extended immediate: no truncation, no second evaluator. -/
theorem addImmOp_b64 (x : Wort) (n : Nat) :
    addImmOp .b64 x n = x + immSext n := by
  simp [addImmOp, trunc_b64]

/-! ## 64-bit flag identities: every defined flag IS the accepted
  `add64` flag on the sign-extended immediate. -/

/-- CF identity: the carry out is the accepted unsigned carry. -/
theorem addImmFlags_cf (x : Wort) (n : Nat) :
    (addImmFlags .b64 x n).cf = (add64 x (immSext n)).2.cf := by
  simp [addImmFlags, addImmOp, add64, cfAdd, trunc_b64, Breite.bits]

/-- OF identity: the signed overflow is the accepted one. -/
theorem addImmFlags_of (x : Wort) (n : Nat) :
    (addImmFlags .b64 x n).of = (add64 x (immSext n)).2.of := by
  simp [addImmFlags, addImmOp, add64, ofAdd, trunc_b64, negB_b64]

/-- SF identity: the sign is the accepted top-bit test. -/
theorem addImmFlags_sf (x : Wort) (n : Nat) :
    (addImmFlags .b64 x n).sf = (add64 x (immSext n)).2.sf := by
  simp [addImmFlags, addImmOp, add64, trunc_b64, negB_b64]

/-- ZF identity: zero is the accepted zero test. -/
theorem addImmFlags_zf (x : Wort) (n : Nat) :
    (addImmFlags .b64 x n).zf = (add64 x (immSext n)).2.zf := by
  simp [addImmFlags, addImmOp, add64, trunc_b64]

/-- PF identity: parity is the accepted even-parity test. -/
theorem addImmFlags_pf (x : Wort) (n : Nat) :
    (addImmFlags .b64 x n).pf = (add64 x (immSext n)).2.pf := by
  simp [addImmFlags, addImmOp, add64, trunc_b64]

/-! ## Canonical codec: exactly the REX.W 83 /0 ib register row.

  Bytes (Vol. 2A 3-14 opcode table "REX.W + 83 /0 ib"): REX.W with only
  the B extension bit (72/73; REX.R would rewrite the /0 extension digit
  into an unadmitted row, so 76/77 refuse), opcode 131, ModRM
  register-direct (mod = 3) with the /0 digit in the reg field, then the
  imm8 byte. Length 4. The encoder takes the immediate as a `Nat` and
  refuses anything outside a byte (`none`): no silent truncation. -/

/-- The one covered compact form: ADD r64, imm8 with the immediate as
    an unbounded `Nat` (range-checked at encode time). -/
inductive CompactAddForm where
  | addImm8 (dst : Register) (imm : Nat)
  deriving DecidableEq, Repr

/-- Canonical byte encoding of the covered row, or `none` outside i8. -/
def encodeCompactAdd : CompactAddForm → Option (List Byte)
  | .addImm8 dst n =>
    if n < 256 then
      some [rexByte 0 (regHigh dst), natByte 131,
        natByte (192 + regLow dst), natByte n]
    else none

/-- Decoded length of the covered row: 4. -/
def compactAddLaenge : CompactAddForm → Nat
  | .addImm8 _ _ => 4

/-- The covered row fits the 1..15 instruction bound. -/
theorem compactAddLaenge_ok (f : CompactAddForm) :
    laengeOk (compactAddLaenge f) = true := by
  cases f <;> rfl

/-- Decode after an admitted REX prefix: opcode 131 is the compact ADD;
    ModRM must be register-direct (mod = 3) with the /0 extension digit
    in the reg field. Anything else refuses with `none` WITHOUT touching
    later bytes. -/
def decodeCompactAddOp (bBit op : Nat) :
    List Byte → Option (CompactAddForm × List Byte)
  | rest =>
    if op == 131 then
      match rest with
      | m :: i :: rest' =>
        if byteNat m / 64 == 3 && byteNat m / 8 % 8 == 0 then
          match codeReg (bBit * 8 + byteNat m % 8) with
          | some dst => some ((.addImm8 dst (byteNat i)), rest')
          | none => none
        else none
      | _ => none
    else none

/-- Decode the covered row: an admitted REX.W prefix (72/73, R = 0 so
    the /0 digit is untouched), then opcode 131, ModRM and imm8. -/
def decodeCompactAdd : List Byte → Option (CompactAddForm × List Byte)
  | r :: rest =>
    if byteNat r == 72 then
      match rest with
      | op :: rest' => decodeCompactAddOp 0 (byteNat op) rest'
      | [] => none
    else if byteNat r == 73 then
      match rest with
      | op :: rest' => decodeCompactAddOp 1 (byteNat op) rest'
      | [] => none
    else none
  | [] => none

/-! ## Round trip: decoding inverts encoding with the suffix.

  The immediate form needs `n < 256` (one byte carries it); the same
  premise is discharged by the byte round trip itself. -/

/-- Round trip over any suffix: the four canonical bytes decode back to
    the form with the immediate intact. -/
theorem roundtripCompactAdd (dst : Register) (n : Nat) (h : n < 256)
    (suffix : List Byte) :
    decodeCompactAdd ([rexByte 0 (regHigh dst), natByte 131,
      natByte (192 + regLow dst), natByte n] ++ suffix) =
      some ((.addImm8 dst n), suffix) := by
  cases dst <;>
    simp [decodeCompactAdd, decodeCompactAddOp, rexByte, regHigh,
      regLow, regCode, codeReg, (byteNat_natByte_of_lt n h)]

/-! ## Encoder range: inside i8 four bytes, outside i8 refusal. -/

/-- Inside i8 the encoder answers with exactly the four canonical bytes. -/
theorem encodeCompactAdd_some (dst : Register) (n : Nat) (h : n < 256) :
    encodeCompactAdd (.addImm8 dst n) =
      some [rexByte 0 (regHigh dst), natByte 131,
        natByte (192 + regLow dst), natByte n] := by
  simp [encodeCompactAdd, h]

/-- Outside i8 the encoder refuses: no silent truncation into a byte. -/
theorem encodeCompactAdd_verweigert (dst : Register) (n : Nat)
    (h : 256 ≤ n) :
    encodeCompactAdd (.addImm8 dst n) = none := by
  simp [encodeCompactAdd, Nat.not_lt.mpr h]

/-- Refusal cause: `none` means the immediate is outside i8. -/
theorem encodeCompactAdd_ursache (dst : Register) (n : Nat)
    (h : encodeCompactAdd (.addImm8 dst n) = none) : 256 ≤ n := by
  by_cases h' : n < 256
  · exfalso
    rw [encodeCompactAdd_some dst n h'] at h
    simp at h
  · exact Nat.le_of_not_lt h'

/- CUTS:
    Proved here so far: sign-extended imm8 (`immSext` reusing canonical
    `sext .b8`) with one pin.
    NOT proved here, and not claimed:
    - Everything else of the lane task: codec, flag identities, pins,
      refusals, execution connection, joint witness.
    - No hardware verification: stated executable semantics only.
-/

#print axioms pin_immSext_7f

end Gabbro.Grammatik.X86
