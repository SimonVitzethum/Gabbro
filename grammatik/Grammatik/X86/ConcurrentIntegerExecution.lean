/-
  File:      Grammatik/X86/ConcurrentIntegerExecution.lean
  Subject:   Real selected integer bytes on shared TSO execution.

  Lane 720: width-selected (1/2/4/8-byte) integer load/store execution
  over the canonical HwMaschine (HardwareExecution660) with ordered
  byte issue, youngest-own forwarding, ordered drain and
  register/partial-register effects from the accepted scalar producer
  equations (NarrowOps, EffectiveAddress, AddressEncoding). No SC word
  effect is substituted for a buffered access; word single-event
  claims go through WortGruppe/WortGuard with cross-core interleavings.
  Missing width codec rows stay explicit pending extensions.
  Provenance: Intel SDM 325462-093US (clone-local
  .tmp/HARDWARE-REFERENCES/REFERENCES.json + intel-instruction-reference.txt
  headings, e.g. MOV/MOVZX/MOVSX/ADD/SUB/TEST/LEA); headings are
  provenance, never silicon proofs.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.NarrowOps
import Grammatik.X86.EffectiveAddress

namespace Gabbro.Grammatik.X86

/-- Width-selected integer memory op: load/store at an explicit width
    through base plus displacement (accepted `effAddr` address). -/
inductive ConcIntOp where
  | load (b : Breite) (dst base : Register) (disp : BitVec 32)
  | store (b : Breite) (base src : Register) (disp : BitVec 32)
  deriving DecidableEq, Repr

/-- Address of one op from the pre-state register file: the accepted
    pilot `effAddr` (base plus sign-extended displacement). -/
def concAddr (s : Zustand) : ConcIntOp → Adresse
  | .load _ _ base disp => effAddr s base disp
  | .store _ base _ disp => effAddr s base disp

/- CUTS:
   Skeleton only; full connection pending (see lane report).
-/

#print axioms concAddr

end Gabbro.Grammatik.X86
