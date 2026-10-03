/-
  File:      Grammatik/X86/OptMovImmSel.lean
  Subject:   MOV-immediate selection rule (lane 892).

  DESIGN section 2B rows (MOV reg, imm32 zero-extending / sign-extended
  vs imm64) as a layer-A local rewrite (DESIGN section 7 register
  discipline): a rule lemma over arbitrary values with validator-decided
  side conditions. Reuses the pilot `movImm64` row (`Codec`,
  `Ausfuehrung`) and the accepted compact zero row
  (`CompactImmMov32Zero`); the sign tile reuses canonical `sext`
  (`Wort`) at value level until lane 747 lands its row.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.CompactImmMov32Zero
import Grammatik.X86.NarrowOps

namespace Gabbro.Grammatik.X86

/-- The three MOV-immediate tiles: the 10-byte pilot `movImm64`, the
    compact zero-extending imm32 row (lane 746), and the sign-extended
    imm32 row (value level only until lane 747 lands). -/
inductive MovTile where
  | weit (v : Wort)
  | kompakt (imm : BitVec 32)
  | sign (imm : BitVec 32)
  deriving DecidableEq, Repr

/-- Value denoted by a tile: the wide word itself, the accepted
    zero extension, or the canonical sign extension. -/
def tileWert : MovTile → Wort
  | .weit v => v
  | .kompakt imm => compactWert imm
  | .sign imm => sext .b32 (BitVec.ofNat 64 imm.toNat)

end Gabbro.Grammatik.X86
