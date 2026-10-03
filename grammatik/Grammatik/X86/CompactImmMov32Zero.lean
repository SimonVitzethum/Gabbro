/-
  File:      Grammatik/X86/CompactImmMov32Zero.lean
  Subject:   Compact zero-extending MOV reg, imm32 (lane 746).

  Covers exactly one row: no-REX.W `B8+rd id` (MOV r32, imm32), whose
  32-bit result is zero-extended into the 64-bit destination. Reuses the
  canonical `Register`/`Zustand`/`Speicher` (`Typen`), `trunc` (`Wort`),
  the 32-bit clearing discipline (`NarrowOps.mergeRegNarrow_b32`), the
  register-file helpers (`Ausfuehrung`: `laengeOk`/`ripNach`/`regSet`),
  little-endian bytes (`Codec`), the fetch discipline (`Byteschritt`)
  and decoder-side suffix facts (`DecodingCoverage`). No new word,
  register, state or source type is created.

  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`,
  Intel SDM 325462-093US, September 2026):
  - MOV opcode table (Vol. 2B, section MOV-Move, txt lines 65710-65712):
    `B8+ rd id MOV r32, imm32` versus `REX.W + B8+ rd io MOV r64,
    imm64`. Without REX.W the B8+rd row carries imm32, never imm64.
  - Operand-size rule (Vol. 1, BASIC EXECUTION ENVIRONMENT, Table 3-2
    context, txt lines 4375-4382): 32-bit operands generate a 32-bit
    result, zero-extended to a 64-bit result in the destination
    general-purpose register.
  - MOV Description: in 64-bit mode the default operation size is 32
    bits; REX.R permits R8-R15; REX.W promotes operation to 64 bits.
  - Flags Affected: None (MOV entry).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.NarrowOps

namespace Gabbro.Grammatik.X86

/-- The one covered row: compact move of a 32-bit immediate into the
    low half of a 64-bit register, zero-extending above bit 31. -/
inductive CompactImmMov32 where
  | mov32imm (dst : Register) (imm : BitVec 32)
  deriving DecidableEq, Repr

/-- A decoded compact move with its consumed length (checked data). -/
structure CompactDec where
  op : CompactImmMov32
  laenge : Nat
  deriving DecidableEq, Repr

/-- The zero-extended value: exactly the low 32 bits as a word, reusing
    the canonical `trunc` (no second extension operator). -/
def compactWert (imm : BitVec 32) : Wort :=
  trunc .b32 (BitVec.ofNat 64 imm.toNat)

/- CUTS:
    Skeleton only: encoder, decoder, execution and witnesses are open.
-/

#print axioms compactWert

end Gabbro.Grammatik.X86
