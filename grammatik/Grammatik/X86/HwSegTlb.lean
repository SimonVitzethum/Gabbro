/-
  File:      Grammatik/X86/HwSegTlb.lean
  Subject:   FS/GS segment bases with override prefixes, and a per-core
             TLB with INVLPG and CR3-flush, over the coherent machine.

  Lane 1285: connects the SELECTED segment/TLB family to the coherent
  `HwMaschine`/`HwSchritt` of `HardwareExecution`, reusing the accepted
  definitions unchanged (lifted, never redefined). The page walk itself
  is a parameter (lane HwPaging owns it); PCID is off (named assumption).
  No silicon correspondence is claimed (see CUTS).
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.AddressEncoding
import Grammatik.X86.TSO

namespace Gabbro.Grammatik.X86

/-- Segment override choice on one memory access: no override, or the
    FS/GS base added to the effective address (64-bit mode). CS/DS/ES/SS
    carry no base here: they are ignored (see `segPraefix_ignoriert`). -/
inductive SegWahl where
  | kein | fs | gs
  deriving DecidableEq, Repr

/- CUTS:
   Skeleton only. NOT proved here, and not claimed: everything.
-/

#print axioms SegWahl

end Gabbro.Grammatik.X86
