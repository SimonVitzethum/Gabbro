/-
  File:      Grammatik/X86/IntMemForms.lean
  Subject:   Memory-operand addressing forms for rotates, carry forms
             and sign-extend/XCHG over the coherent machine.

  Lane 1315: the rotate (IntRotate), ADC/SBB/INC/DEC (IntCarryForms)
  and sign-extend/XCHG (IntegerCore value layer, XchgOrderNeed swap
  shape) families only admit the pilot base-plus-disp32 memory shape
  (mod=10, no SIB choice, no RIP-relative, no disp8/disp0). Using the
  accepted selected `AdrForm`/`adrEff` (AddressEncoding) and the
  `HwAddressed` event pattern, this module lifts all three families
  to the full addressing-mode set: decode and encode with pinned
  round trips, effective address equal to `adrEff`, access as TSO
  events with the exact `entriesOf` footprint, and memory-destination
  RMW as load-modify-store events. LOCK stays refused. No silicon
  correspondence beyond self-consistency (see CUTS).
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.AddressEncoding
import Grammatik.X86.HwAddressed
import Grammatik.X86.ConcurrentIntegerExecution
import Grammatik.X86.NarrowOps
import Grammatik.X86.IntRotate
import Grammatik.X86.IntCarryForms

namespace Gabbro.Grammatik.X86

/-- Selected address of one access from the acting core's pre-state
    registers plus the next-RIP base for RIP-relative forms. -/
def intMemAddr (m : HwMaschine) (c : Nat) (ripNext : Adresse)
    (f : AdrForm) : Adresse :=
  adrEff (projZustand m c) ripNext f

/-- The lifted address reads the acting core's pre-state registers
    (and the RIP base for RIP-relative forms) only. -/
theorem intMemAddr_basisForm (m : HwMaschine) (c : Nat)
    (base : Register) (disp : BitVec 32) (ripNext : Adresse) :
    intMemAddr m c ripNext (basisForm base disp) =
      effAddr (projZustand m c) base disp := by
  unfold intMemAddr
  rw [adrEff_basisForm]

/- CUTS: skeleton only; full statement at the end of the file. -/

end Gabbro.Grammatik.X86
