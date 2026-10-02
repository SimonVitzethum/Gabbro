/-
  File:      Grammatik/X86/InterruptDescriptorHardware.lean
  Subject:   Actual IDT gate parsing and TSS entry-stack selection on
             canonical memory (long mode).

  Lane 728: the missing generic descriptor-read/check layer -- IDTR
  base/limit, vector gate selection, 16-byte gate parsing,
  type/present/reserved/DPL/selector/canonical-handler checks,
  long-mode TSS IST/RSP slot lookup and stack selection. Checked
  descriptor/stack producer for lanes 672/708. No trusted parsed
  descriptor, no hidden valid-entry assumption.

  Manual provenance (clone-local `.tmp/HARDWARE-REFERENCES/`):
  - Table 6-1 vectors, Vol. 1 Ch. 6 (txt lines 9641-9671).
  - Canonical addresses, Vol. 1 §3.3.7.1 (txt line 4220).
  - IDT delivery push order, Vol. 1 §6.5.1 (txt lines 9690-9705).
  - INT n entry: software-INT DPL check, IA-32e limit/type checks,
    IST/RSP slot arithmetic, push order, IF clearing (txt 58904-59680).
  - The 16-byte gate/TSS figures live in Vol. 3 (outside the local
    txt snapshot): field positions are stated architecture, and every
    CHECK on them is proved from canonical-memory equations.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Codec
import Grammatik.X86.HardwareFaults

namespace Gabbro.Grammatik.X86

/-- Architectural control state: IDT register, current TSS window,
    privilege level and the interrupt-enable bit. No OS content. -/
structure Steuerstand where
  idtBasis : Adresse
  idtLimit : Nat
  tssBasis : Adresse
  tssLimit : Nat
  cpl : Nat
  ifBit : Bool
  deriving DecidableEq, Repr

/-- A 64-bit gate is 16 bytes; a vector selects `basis + v * 16`. -/
def torAdresse (idtBasis : Adresse) (vektor : Nat) : Adresse :=
  idtBasis + BitVec.ofNat 64 (vektor * 16)

/-- The 16 gate bytes fit inside the IDT limit (pseudocode
    `(vector « 4) + 15` within limits, INT entry). -/
def torImLimit (idtLimit vektor : Nat) : Bool :=
  decide (vektor * 16 + 15 ≤ idtLimit)

/- CUTS:
   Skeleton only: control state, gate address and the IDT-limit
   predicate. Parsing, checks, slot lookup, selection, faults,
   priority, frame, producer interface and witnesses are OPEN.
-/

#print axioms torAdresse
#print axioms torImLimit

end Gabbro.Grammatik.X86
