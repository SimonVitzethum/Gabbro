/-
  File:      Grammatik/X86/IntBitTest.lean
  Subject:   Bit test family BT/BTS/BTR/BTC over canonical words,
             connected to the coherent machine.

  Lane 1277: BT/BTS/BTR/BTC (0F A3/AB/B3/BB, 0F BA /4../7 ib) on
  registers (bit offset modulo width) and on memory with a register
  bit offset (signed offset moves the effective address; exact
  footprint as TSO byte events; LOCK-prefixed memory refused).
  CF = selected bit, OF/SF/AF/PF undefined (free, never false),
  ZF unaffected. Widths 16/32/64 (no 8-bit form exists: refused).
  Structure follows ShiftCodec (decode/encode/round-trip/value/step)
  and HwMulDivWidth (dispatcher preferring decodeExt, HwAdapter
  register plug, two-core witness). No hardware correspondence is
  claimed beyond self-consistency (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ganzzahl
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.NarrowOps

namespace Gabbro.Grammatik.X86

/-- The four bit-test operations. -/
inductive BtOp where
  | bt | bts | btr | btc
  deriving DecidableEq, Repr

/-- Register-form opcode: 0F A3/AB/B3/BB. -/
def btOpcode : BtOp → Nat
  | .bt => 163 | .bts => 171 | .btr => 179 | .btc => 187

/-- Group digit in 0F BA /4../7. -/
def btGruppe : BtOp → Nat
  | .bt => 4 | .bts => 5 | .btr => 6 | .btc => 7

/-- Opcode pins: the four SDM second-opcode bytes. -/
theorem pin_bt_opcode :
    btOpcode .bt = 163 ∧ btOpcode .bts = 171 ∧
    btOpcode .btr = 179 ∧ btOpcode .btc = 187 := by
  decide

end Gabbro.Grammatik.X86
