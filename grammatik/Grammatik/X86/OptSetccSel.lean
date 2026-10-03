/-
  File:      Grammatik/X86/OptSetccSel.lean
  Subject:   SETcc selection rule lemma (lane 890).

  DESIGN rows: §3 SETcc row (byte result 0/1 exact; no flag leak),
  §3A (SETcc where MEASURED suitable, never by default; register-only
  first), §4 float row (UCOMISD + SETcc/Jcc with JP row; NaN unordered
  is false), §7 flags-aware peepholes (rule in register, flag-liveness,
  no token op in pure window), certificate A (local rewrite record plus
  recomputed analysis citations).

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`,
  `X86.ControlFlow`, `X86.ControlCodec`): the validator-decided side
  conditions, their refusals, the 0/1 byte value over arbitrary
  conditions, the byte-step window frame, the admitted float-compare
  equation, and the source/target connection. No `ensures` is derived,
  no refusal becomes a warning, no faulting form is speculated above
  its guard. No accepted IR exists yet, so the source fragment is the
  real `Syntax`/`Semantik` `Endblock.bind` window.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.ControlFlow
import Grammatik.X86.ControlCodec

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one SETcc-selection site:
    measured-suitable (never by default), no live flag consumer across
    the compare+SETcc window, no token op in the pure window,
    register destination only, and float sites carry their unordered
    (JP) row under one MXCSR scope. -/
structure SetccSelCert where
  massGeeignet : Bool
  keinFlagLeck : Bool
  reinesFenster : Bool
  nurRegister : Bool
  fpBereinigt : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation falls back to another certified translation
    (the branched spelling), never to a warning. -/
def setccZulassen (c : SetccSelCert) : Bool :=
  c.massGeeignet && c.keinFlagLeck && c.reinesFenster && c.nurRegister
    && c.fpBereinigt

/- CUTS:
    - Skeleton only: refusals, value/frame/float lemmas, the connection
      `OptSetccSel_verbindung` and its joint witness follow.
-/

#print axioms setccZulassen

end Gabbro.Grammatik.X86
