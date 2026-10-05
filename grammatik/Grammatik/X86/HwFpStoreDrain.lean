/-
  File:      Grammatik/X86/HwFpStoreDrain.lean
  Subject:   FP 32-bit store drain equals the accepted `write32`.

  Lane 1307 (follow-up of lane 1211 `HwFpDispatch.lean`): the
  drain/write32 byte correspondence for STMXCSR and MOVSS-store was
  open (value and footprint pinned at issue level only). This file
  proves, generically over the TSO model and the `FpFremdFrei32`
  guard, that the four buffered byte entries drain to canonical
  memory equal to the accepted `write32` of the stored value (the
  `HwDrainGeneric.lean` technique for 8 bytes, specialised to 4),
  with forwarding to the owner and the foreign view before drain; a
  misaligned 4-byte store crossing a group boundary stays as the
  accepted tearing refusal. Accepted evaluators are lifted, never
  redefined.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.HwFpControl
import Grammatik.X86.HwFpDispatch
import Grammatik.X86.HwDrainGeneric
import Grammatik.X86.WordAccessGrouping

namespace Gabbro.Grammatik.X86

/-- FP 32-bit store-drain family events on the coherent machine. -/
inductive FpStoreEreignis where
  | speichere32 : Adresse → Wort → FpStoreEreignis
  | eigenSpuele : FpStoreEreignis
  | fremdSpuele : Nat → FpStoreEreignis
  | fremdAusgabe : Nat → TSOEintrag → FpStoreEreignis
  | beobachte : Adresse → FpStoreEreignis
  deriving DecidableEq, Repr

/-- The family adapter: 32-bit stores buffer four bytes, drains
    flush, observations read without moving state. -/
def fpStoreAdapter : HwAdapter FpStoreEreignis :=
  ⟨fun m c ev => match ev with
    | .speichere32 a v => fpCtrlAusgabe32 m c a v
    | .eigenSpuele =>
      match flushKern (tsoAnsicht m) c with
      | some s' => some (setTso m s')
      | none => none
    | .fremdSpuele d =>
      match flushKern (tsoAnsicht m) d with
      | some s' => some (setTso m s')
      | none => none
    | .fremdAusgabe d e =>
      match issueByte (tsoAnsicht m) d e.addr e.wert with
      | some s' => some (setTso m s')
      | none => none
    | .beobachte a =>
      match loadByte (tsoAnsicht m) c a with
      | some _ => some m
      | none => none⟩

/- CUTS: skeleton only; induction, forwarding, refusals open.
-/

#print axioms FpStoreEreignis
#print axioms fpStoreAdapter

end Gabbro.Grammatik.X86
