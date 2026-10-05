/-
  File:      Grammatik/X86/HwDrainGeneric.lean
  Subject:   Generic drain-equals-write64 induction on the coherent machine
             (lane 1207, follow-up of lane 1185 `HwForwardingGeneric`).

  Lifts the accepted word drain (`DrainSpur`, `WortGruppe`, `FremdFrei`,
  `flushKern`, `wortEintraege`) to a generic induction: draining the
  eight buffered entries of a word store, in any interleaving with
  foreign flushes/issues satisfying `FremdFrei`, installs exactly the
  `write64` footprint bytes, with the visited states exactly the stated
  prefixes. A foreign overlapping flush breaks it (counter-witness).
  No model is redefined here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.TSO
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.HwStackCalls
import Grammatik.X86.HardwareExecution

namespace Gabbro.Grammatik.X86

/-! ## 1. Family events and the adapter. -/

/-- Generic drain family events on the coherent machine. -/
inductive DrainEreignis where
  | speichere : Adresse → Wort → DrainEreignis
  | eigenSpuele : DrainEreignis
  | fremdSpuele : Nat → DrainEreignis
  | fremdAusgabe : Nat → TSOEintrag → DrainEreignis
  | beobachte : Adresse → DrainEreignis
  deriving DecidableEq, Repr

/-- The family adapter: word stores buffer, drains flush, observations
    read without moving state. -/
def drainAdapter : HwAdapter DrainEreignis :=
  ⟨fun m c ev => match ev with
    | .speichere a v => hwWortAusgabe m c a v
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
      match stapelLadeWort (tsoAnsicht m) c a with
      | some _ => some m
      | none => none⟩

/- CUTS:
   Skeleton only: adapter defined, induction and witnesses open.
-/

#print axioms drainAdapter

end Gabbro.Grammatik.X86
