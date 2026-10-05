/-
  File:      Grammatik/X86/HwPaging.lean
  Subject:   IA-32e 4-level page translation as a named hardware model.

  Lane 1283: 4-level page walk (PML4/PDPT/PD/PT, 4 KiB pages),
  present/RW/US/XD bits with AND/OR combination, CR0.WP, accessed/dirty
  updates, #PF error-code outcome on the accepted fault vocabulary
  (`HardwareFaults`, `ExceptionPriorityHardware`), canonical-address
  check (#GP), and the bridge to the flat `Speicher` permissions.
  No TLB, no timing. OS policy stays user logic.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.ExceptionPriorityHardware

namespace Gabbro.Grammatik.X86

/-- One IA-32e page-table entry, decoded. Bit positions per SDM Vol 3A
    §4.5 Table 4-18: P bit 0, R/W bit 1, U/S bit 2, A bit 5, D bit 6,
    PS bit 7, XD bit 63; `rahmen` is the page-frame number. -/
structure SeitenEintrag where
  vorhanden : Bool
  schreibbar : Bool
  benutzer : Bool
  gross : Bool
  zugegriffen : Bool
  schmutzig : Bool
  noExec : Bool
  rahmen : Nat
  deriving DecidableEq, Repr

/- CUTS (skeleton):
   NOT proved here, and not claimed:
   - Everything in the lane task: walk, permission combination, WP,
     accessed/dirty rules, #PF error code, canonical check, flat bridge,
     adapter/extended step, witness. This skeleton only fixes the
     entry vocabulary.
-/

end Gabbro.Grammatik.X86
