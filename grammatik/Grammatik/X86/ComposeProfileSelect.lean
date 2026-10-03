/-
  File:      Grammatik/X86/ComposeProfileSelect.lean
  Subject:   Composition closing: profile-selection closing.

  Lane 844: closes backend form choice to the named CPU profile.
  The measured-trait tables stay tuning only: profile selection names a
  feature (`FeatureProfile.fallback`), the zeroing form choice
  (`Anweisungswahl.waehleNull`) is gated by flag liveness, and every
  selected byte re-decodes through the canonical decoder (`Codec.roundtrip`,
  the same decoder `ValidatorSkeleton` uses for coverage). No internals
  are re-proved; all producer facts are reused by name. No new
  interpreter, no new IR, no source/checker/Spec/goal/emitter change.
-/
import Grammatik.X86.FeatureProfile
import Grammatik.X86.InstructionSelection
import Grammatik.X86.ValidatorSkeleton
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Speicher
import Grammatik.X86.Bild
import Grammatik.X86.InvariantenOpt

namespace Gabbro.Grammatik.X86.ComposeProfileSelect

open Gabbro.Grammatik.X86.Anweisungswahl

/-- Profile-gated zeroing instruction: the preserving 10-byte form under
    live flags, the clobbering 3-byte form under dead flags. The single
    element of `waehleNull`; the CPU profile never changes its meaning. -/
def composeInstr (flagsLive : Bool) (dst : Register) : Befehl :=
  if flagsLive then .movImm64 dst 0 else .xorReg64 dst dst

end Gabbro.Grammatik.X86.ComposeProfileSelect
