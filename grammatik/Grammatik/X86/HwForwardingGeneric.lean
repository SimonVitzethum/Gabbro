/-
  File:      Grammatik/X86/HwForwardingGeneric.lean
  Subject:   Generic word-forwarding theorem on the coherent machine
             (lane 1185, follow-up of lane 1139 `HwStackCalls`).

  Lifts the accepted `hwWortAusgabe` word stores and the accepted
  `stapelLadeWort` forwarding loads to a generic word family on
  `HwMaschine`: under the `WortGruppe` guard the owner core forwards
  the stored word, a foreign core reads canonical memory until drain,
  and partial overlaps follow the accepted byte rules (`loadByte`,
  `neuestens`). Misaligned loads, torn buffers and overlapping older
  or younger entries never group. No model is redefined here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.TSO
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.HardwareExecution
import Grammatik.X86.HwStackCalls

namespace Gabbro.Grammatik.X86

/-! ## 1. Family events and the adapter.

  A word store buffers eight bytes through the accepted
  `hwWortAusgabe`; a word observation reads through the accepted
  `stapelLadeWort` without moving state. -/

/-- Generic word family events on the coherent machine. -/
inductive FwdEreignis where
  | speichere : Adresse → Wort → FwdEreignis
  | beobachte : Adresse → FwdEreignis
  deriving DecidableEq, Repr

/-- The family adapter: stores buffer a word, observations read one
    (state unchanged). -/
def fwdAdapter : HwAdapter FwdEreignis :=
  ⟨fun m c ev => match ev with
    | .speichere a v => hwWortAusgabe m c a v
    | .beobachte a =>
      match stapelLadeWort (tsoAnsicht m) c a with
      | some _ => some m
      | none => none⟩

/- CUTS:
    Skeleton only: events and the adapter are stated, nothing proved.
-/

#print axioms FwdEreignis
#print axioms fwdAdapter

end Gabbro.Grammatik.X86
