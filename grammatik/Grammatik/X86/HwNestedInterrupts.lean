/-
  File:      Grammatik/X86/HwNestedInterrupts.lean
  Subject:   Nested interrupt delivery, double fault and handler entry
             on the coherent multicore machine.

  Lane 1181: follow-up of lane 1125 (`HwInterrupts.lean`), whose CUTS
  list no nested delivery, no #DF, no handler execution and no concrete
  maskable-success witness. Lifts the accepted `asyncSchritt`/`liefere`
  delivery (HwInterrupts.lean, InterruptDescriptorHardware.lean) and the
  accepted buffered word effects (`hwWortAusgabe`, HwStackCalls.lean)
  unchanged. Delivery never drains the per-core TSO store buffer; every
  silicon fact beyond self-consistency is named in the ANNAHMEN block
  in §1 and the CUTS block at the end.
-/
import Grammatik.X86.HwInterrupts
import Grammatik.X86.HwStackCalls

namespace Gabbro.Grammatik.X86

/-! ## 1. Silicon assumptions (ANNAHMEN).

   Checked against the clone-local Intel SDM extracts (provenance,
   never proofs; see MUSE-REPORT-660 for the extract catalogue):
   - S1: maskable external interrupts (INTR) are gated by IF; NMI
     bypasses IF (Vol. 3 interrupt delivery; Table 6-1). Reused from
     lane 1125 (`asyncBereit`); nested delivery re-checks the UPDATED
     IF after the first delivery.
   - S2: NMI arrives on vector 2; maskable external vectors are
     32-255 (Table 6-1). Reused from lane 1125 (`asyncVektorOk`).
   - S3: delivery is NOT a serialising drain of the per-core store
     buffer. Reused from lane 1125 (`asyncMasch_puffer_still`).
   - S4: a fault during delivery of a fault escalates to double
     fault #DF, vector 8, error code zero (Table 6-1; Vol. 3A Ch. 7
     `DOUBLE FAULT` exception class).
   - S5: an interrupt gate clears IF on delivery, a trap gate keeps
     it. Reused from lane 1125 (`asyncSchritt_interrupt_loescht_if`,
     `asyncSchritt_trap_behaelt_if`).
   - S6: IRET pops RIP, CS, RFLAGS (and SS:RSP where the frame holds
     them) and restores IF from RFLAGS bit 9; a failed load or a
     noncanonical target faults with #SS/#GP instead of returning.
-/

/-- Double-fault vector (S4): #DF is vector 8. -/
def dfVektor : Nat := 8

/- CUTS:
   Proved here: SKELETON ONLY so far -- the double-fault vector
   constant. Nested delivery, #DF escalation, the TSO-buffered
   handler frame, IRET and the two-gate maskable witness are OPEN.
   NOT proved here, and not claimed: everything in the lane task.
-/

#print axioms dfVektor

end Gabbro.Grammatik.X86
