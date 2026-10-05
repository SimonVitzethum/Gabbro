/-
  File:      Grammatik/X86/OpcodeLedger1ByteC0.lean
  Subject:   Opcode ledger for one-byte opcodes C0-FF (lane 1339).

  Region C0-FF of the x86-64 opcode map (Intel SDM Vol 2 Appendix A;
  snapshot `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
  edition 325462-093US): every primary opcode byte, group opcodes
  expanded by ModRM.reg extension. Statuses over the accepted
  decoder chain (`kapDecode` in `HwKapsteinDecoder.lean`) and the
  named family decoders below. No AMD manual is in the clone, so no
  AMD provenance is claimed (rule 17); alias facts (/6, /1) are
  Intel-documented and cited in CUTS.
-/
import Grammatik.X86.HwKapsteinDecoder
import Grammatik.X86.ShiftCodec
import Grammatik.X86.CompactForms
import Grammatik.X86.IndirectControlHardwareForms
import Grammatik.X86.IntCarryForms
import Grammatik.X86.DeviceHardwareForms
import Grammatik.X86.MulDivWidthHardwareForms
import Grammatik.X86.ScalarFloatCodec
import Grammatik.X86.ScalarFloat32HardwareForms
import Grammatik.X86.LockedInstructionExecution
import Grammatik.X86.Avx2Join
import Grammatik.X86.Codec

namespace Gabbro.Grammatik.X86.LedgerC0

/-- Ledger status of one opcode row. -/
inductive LStatus
  | modelliert
  | zurueckgestellt
  | verweigert
  | ungueltig64
  | fehlt
  deriving DecidableEq, Repr

/-- One ledger row: primary opcode byte, optional ModRM.reg
    extension for group opcodes, mnemonic, status, the Lean
    module that models it, and a one-line reason. -/
structure LEintrag where
  opcode : Nat
  ext : Option Nat
  mnemonik : String
  status : LStatus
  familie : String
  grund : String
  deriving DecidableEq, Repr

end Gabbro.Grammatik.X86.LedgerC0
