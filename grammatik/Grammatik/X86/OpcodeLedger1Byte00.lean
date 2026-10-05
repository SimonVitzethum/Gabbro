/-
  File:      Grammatik/X86/OpcodeLedger1Byte00.lean
  Subject:   Opcode ledger: one-byte opcodes 00-3F in 64-bit mode.

  Lane 1333: every opcode byte 0x00-0x3F from the x86-64 opcode map
  (SDM Vol 2 Appendix A, Intel edition 093; no AMD manual in this
  clone, so vendor differences stay FREE) listed exactly once with its
  status against the accepted Lean families. Checked facts use the
  capstone chain `kapDecode` (HwKapsteinDecoder) or the named family
  decoder; every refusal is a proved `none`, never a comment.
-/
import Grammatik.X86.HwKapsteinDecoder
import Grammatik.X86.IntCarryForms
import Grammatik.X86.CompactArithRax

namespace Gabbro.Grammatik.X86.Ledger00

/-- Status of one opcode row in this ledger. -/
inductive LStatus where
  | modelliert : LStatus
  | zurueckgestellt : LStatus
  | verweigert : LStatus
  | ungueltig64 : LStatus
  | fehlt : LStatus
  deriving DecidableEq, Repr

/-- One ledger row: opcode byte, mnemonic, status, modelling family
    module and a one-line reason for every non-`modelliert` entry. -/
structure LEintrag where
  opcode : Nat
  mnemonik : String
  status : LStatus
  familie : String
  grund : String
  deriving DecidableEq, Repr

/-- Skeleton pin: the chain takes REX.W ADD r/m64, r64. -/
theorem kap_add_akzeptiert :
    kapDecode [natByte 72, natByte 1, natByte 192] =
      some (KapDekodiert.breit
        (WdHwInstr.ext (ExtInstr.pilot ⟨Befehl.addReg64 .rax .rax, 3⟩)),
        []) := by
  decide

/-! CUTS:
  - Full 64-row table, counts, coverage and refusal pins: open.
  - Opcode map is a NAMED assumption (Intel SDM edition 093, checked
    against the supplied PDF/TXT extracts, never as proved fact).
  - No AMD manual in this clone: no vendor-difference claim.
-/

#print axioms kap_add_akzeptiert
