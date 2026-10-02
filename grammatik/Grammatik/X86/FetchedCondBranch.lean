/-
  File:      Grammatik/X86/FetchedCondBranch.lean
  Subject:   Fetched conditional byte-step flag dependency simulation.

  Lane 656 (connection): lifts `FlagDependencies.jccSchritt_stabil` and the
  per-condition read sets (`liestFlag` / `stimmtUebberein`) to the actual
  `Byteschritt.fetchDekodiert` / `byteschritt` path. Fetch/decode identity
  is DERIVED from equal actual code bytes, execute map and RIP (never
  assumed); agreement on exactly the consumed flags then suffices for the
  same branch outcome and next RIP. One `ConditionalMove.cmovLowerOk`
  lowering admission and the `InstructionSelection.wahlOk` refusal are
  connected to this byte-level rule; the `BranchLayout` carried length is
  tied to the fetched length. CMOVcc/SETcc stay on their real
  `ControlCodec` byte helpers (no `fetchDekodiert` path exists for them).
  No new executor, no new source condition language, no new decoder.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Byteschritt
import Grammatik.X86.FlagDependencies
import Grammatik.X86.ControlCodec
import Grammatik.X86.ConditionalMove
import Grammatik.X86.BranchLayout
import Grammatik.X86.InstructionSelection

namespace Gabbro.Grammatik.X86

/-- Witness displacement of the fetched conditional jump (`je +16`). -/
def fjDisp : BitVec 32 := BitVec.ofNat 32 16

/-- Witness code bytes: the canonical `je +16` encoding at 4096, zero
    elsewhere. Actual `encode` output, never a hand-written byte. -/
def fjBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else (encode (.jumpIf32 .e fjDisp)).getD (a.toNat - 4096) (BitVec.ofNat 8 0)

end Gabbro.Grammatik.X86
