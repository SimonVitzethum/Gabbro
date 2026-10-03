/-
  File:      Grammatik/X86/VectorIntegerFetchedSteps.lean
  Subject:   Fetched packed-integer steps with a dispatch-slot interface.

  Lane 1110: fetched packed-integer execution for the accepted `IntVecOp`
  rows (lane 686) on the common machine discipline (`FpZustand`, `geholt`,
  `laengeOk`, `ausfuehrbarN`), with a saturate-not-mask shift interface, a
  checked shared-store gate, and an explicit dispatch-slot API for the
  718-repair and 724 consumers. No unaccepted module is imported.
-/
import Grammatik.X86.VectorIntegerHardwareForms
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.IntegerHardwareForms
import Grammatik.X86.ScalarFloatHardwareForms
import Grammatik.X86.LockedInstructionExecution
import Grammatik.X86.IndirectControlHardwareForms
import Grammatik.X86.FpControlHardwareForms
import Grammatik.X86.CpuFeatureHardwareForms
import Grammatik.X86.ArchitecturalFlags
import Grammatik.X86.MemoryTypeHardwareExecution
import Grammatik.X86.ConcurrentIntegerExecution
import Grammatik.X86.AddressedHardwareExecution

namespace Gabbro.Grammatik.X86

/-- Shared-store gate: a vector store to a shared address is refused
    until the 6B TSO bridge rules it; every other row is unaffected.
    `geteilt` marks a shared target address (established outside this
    file, never assumed here). -/
def vecGeteiltFrei (geteilt : Bool) : IntVecOp → Bool
  | .movdqaSt _ _ _ => !geteilt
  | .movdquSt _ _ _ => !geteilt
  | _ => true

/-- Fetched packed-integer step: decode the ACTUAL fetched bytes, check
    the shared-store gate, then run the accepted selected step. A forged
    `IntVecDec` cannot inject an instruction. -/
def vecFetched (t : FpZustand) (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (k : KontrollBild) (geteilt : Bool) :
    Option FpZustand :=
  match fetchIntVec t (geholt t.kern) with
  | none => none
  | some (d, _) =>
    if vecGeteiltFrei geteilt d.op then stepIntVec d t hw b cpu k else none

end Gabbro.Grammatik.X86
