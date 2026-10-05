/-
  File:      Grammatik/X86/HwInterrupts.lean
  Subject:   Asynchronous interrupt delivery on the coherent multicore machine.

  Lane 1125: the interrupt672 family producer. The checked asynchronous
  event type (`AsyncEreignis`) and its `HwAdapter` plug
  (`adapterInterrupt1125`) over the accepted `HwMaschine`/`HwSchritt`
  (HardwareExecution.lean §11), lifting the accepted descriptor-layer
  evaluator `liefere` (InterruptDescriptorHardware.lean) unchanged.
  Delivery never drains the per-core TSO store buffer; IF/mask gating
  follows the SDM; every silicon fact beyond self-consistency is named
  in the ANNAHMEN block in §1 and the CUTS block at the end.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.InterruptDescriptorHardware

namespace Gabbro.Grammatik.X86

/-! ## 1. Checked asynchronous event type and admission gates.

   Silicon assumptions (ANNAHMEN, checked against the clone-local Intel
   SDM extracts; provenance, never proofs):
   - S1: maskable external interrupts (INTR) are gated by IF; NMI
     bypasses IF (Vol. 3 interrupt delivery; Table 6-1).
   - S2: NMI arrives on vector 2; maskable external vectors are
     32-255 (vectors 0-31 are synchronous exceptions, Table 6-1).
   - S3: delivery is NOT a serialising drain of the per-core store
     buffer (memory-ordering chapter: only stated serialising forms
     drain; delivery alone leaves pending stores buffered).
-/

/-- Delivery kind: maskable INTR (IF-gated) or NMI (bypasses IF). -/
inductive AsyncArt where
  | maskierbar : AsyncArt
  | nichtMaskierbar : AsyncArt
  deriving DecidableEq, Repr

/-- Checked asynchronous event: vector, kind, control snapshot, code-row
    input, privilege-change data and frame words. Gate bytes are NEVER
    carried: the step reads them from machine memory (`liesTorBytes`). -/
structure AsyncEreignis where
  vektor : Nat
  art : AsyncArt
  steuer : Steuerstand
  codeOk : Bool
  wechsel : Bool
  neuDpl : Nat
  ssAlt : Wort
  rflags : Wort
  csAlt : Wort
  ripAlt : Wort
  fehlercode : Option Wort
  deriving DecidableEq, Repr

end Gabbro.Grammatik.X86
