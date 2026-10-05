/-
  File:      Grammatik/X86/HwIsaFamilies.lean
  Subject:   ISA-strand families (compact/core/cond) on the coherent machine.

  Lane 1141: the ISA strand (`ISA.lean` `Instr`/`stepI`) is imported by NO
  coherent-machine module. This file plugs it into `HwMaschine`
  (`HardwareExecution.lean`) as a `HwAdapter`: the register path lifts
  the accepted `stepI` for memory-unchanged forms only, memory forms go
  through the accepted TSO byte events, and anything else refuses.
  Provenance (headings only, never silicon proofs): Intel SDM
  325462-093US, clone-local `intel-instruction-reference.txt`
  (MOV Vol. 2B 4-28, LEA Vol. 2A 3-547, NOT Vol. 2B 4-161,
  NEG Vol. 2B 4-158, TEST Vol. 2B 4-721, JMP Vol. 2A 3-504,
  ADD Vol. 2A 3-14).
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.ISA
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.ISAWitnesses

namespace Gabbro.Grammatik.X86

/-- Events of one ISA-strand step on the coherent machine: register
    execution of a decoded unified instruction, one observed byte load,
    one issued byte store, or explicit refusal. -/
inductive IsaEreignis where
  | reg : InstrDecoded → IsaEreignis
  | lade : Adresse → Byte → IsaEreignis
  | gibAus : Adresse → Byte → IsaEreignis
  | verweigert : IsaEreignis
  deriving DecidableEq, Repr

/-- Re-embed a `Zustand` successor: register file, flags and RIP move;
    machine memory, buffers, profiles, XMM and FP context stay. -/
def setKernVonZustand (m : HwMaschine) (c : Nat) (s' : Zustand) : HwMaschine :=
  setKernDaten m c ⟨s'.register, s'.flags, s'.rip,
    (m.kerne c).xmm, (m.kerne c).fp⟩

/-- Re-embedding a successor preserves well-formedness. -/
theorem setKernVonZustand_wf (m : HwMaschine) (c : Nat) (s' : Zustand)
    (h : HwWf m) : HwWf (setKernVonZustand m c s') :=
  setKernDaten_wf m c _ h

/- CUTS:
    Skeleton only: the event type and the re-embedding. The classifier,
    the adapter, the stepI/stepExt agreement, the refusals and the
    two-core witness are OPEN.
-/

#print axioms setKernVonZustand_wf

end Gabbro.Grammatik.X86
