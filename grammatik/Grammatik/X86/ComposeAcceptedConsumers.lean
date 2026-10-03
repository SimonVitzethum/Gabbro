/-
  File:      Grammatik/X86/ComposeAcceptedConsumers.lean
  Subject:   Close the accepted consumers through the common dispatcher.

  Lane 1104: ONE fetched-execution closing over HwMaschine from
  already-accepted pieces: the 824 decode-to-execution closing as
  dispatch backbone, the 720 integer-to-TSO rows, the 730 address
  adapter, the 738 fault-priority relation, and 728 descriptor/stack
  inputs where entry-adjacent rows need them. Reuses
  decodeExt/stepExt/extByteschritt (575/660 line) and the 824
  composition lemmas; no second executor. Every not-yet-accepted
  producer family stays an explicit pending extension enumerated in
  CUTS, never imported, never assumed.
-/
import Grammatik.X86.ComposeDecodeExec
import Grammatik.X86.ConcurrentIntegerExecution
import Grammatik.X86.AddressedHardwareExecution
import Grammatik.X86.ExceptionPriorityHardware
import Grammatik.X86.InterruptDescriptorHardware
import Grammatik.X86.HardwareExecution

namespace Gabbro.Grammatik.X86

/-- Pending producer families, by owning lane number: width rows
    696/698, LOCK 722, scalar FP 724, paging 726, control 734,
    context 736, AVX2 690, returns 708. Explicit, never imported,
    never assumed, never closed by a premise shaped like the
    conclusion. -/
inductive PendingFam where
  | breite696
  | breite698
  | lock722
  | fp724
  | seiten726
  | steuer734
  | kontext736
  | avx690
  | rueck708
  deriving DecidableEq, Repr

/-- Owning lane number of each pending family (audit only). -/
def familienCode : PendingFam → Nat
  | .breite696 => 696
  | .breite698 => 698
  | .lock722 => 722
  | .fp724 => 724
  | .seiten726 => 726
  | .steuer734 => 734
  | .kontext736 => 736
  | .avx690 => 690
  | .rueck708 => 708

/- CUTS:
   Proved here so far: the pending-family enumeration `PendingFam`
   with its lane-number audit `familienCode`.
   NOT proved here, and not claimed: everything in the lane task --
   the fetched-execution closing, the integer/TSO, address, priority
   and descriptor/stack composition, the joint witness and the
   planted probes. Pending families (width rows 696/698, LOCK 722,
   FP 724, paging 726, control 734, context 736, AVX2 690, returns
   708) are never imported (especially not modules owned by lanes
   718/722/724/726/734/736/690/708/696/698), never assumed, and never
   closed by a premise shaped like the conclusion.
-/

#print axioms familienCode

end Gabbro.Grammatik.X86
