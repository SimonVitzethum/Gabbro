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

namespace Gabbro.Grammatik.X86

/-- Sign-extended imm8 as a full word: the low byte sign-extended through
    the canonical `sext .b8` (Vol. 2A 3-14 Description: the immediate "is
    sign-extended to the length of the destination operand format"). -/
def immSext (n : Nat) : Wort := sext .b8 (BitVec.ofNat 64 n)

/-- Pin: the largest positive imm8 stays positive. -/
theorem pin_immSext_7f : immSext 127 = 127 := by
  decide

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
