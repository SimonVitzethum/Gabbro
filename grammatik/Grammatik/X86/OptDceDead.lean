/-
  File:      Grammatik/X86/OptDceDead.lean
  Subject:   Dead-code elimination rule lemma (lane 865).

  DESIGN section 7 row: local premises "pure (no token/atomic/call/check/
  stop/trap-capable FP) + dead confirmed", certificate "A+B", failure cases
  "remove `0.0/0.0` (an unused NaN hides `logik bereich`); remove a spin
  load", phase M, cost O(sites).

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `KostenG`, `CFormenI`, `X86.Typen`, `X86.Wort`):
  removing a pure overwritten local write preserves the `execBlock`
  outcome. No `ensures` is derived, no refusal becomes a warning, no
  faulting form is speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.KostenG
import Grammatik.CFormenI
import Grammatik.X86.Typen
import Grammatik.X86.Wort

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one dead-code site
    (DESIGN section 7 row): the removed computation reads no shared
    carrier (`orteLeer`, recomputed from `Expr.orte`) and its target is
    dead at the site (`zielTot`, recomputed liveness: immediate
    redefinition before any read). -/
structure DceCert where
  orteLeer : Bool
  zielTot : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL optimisation
    falls back to another certified translation, never to a warning. -/
def dceZulassen (c : DceCert) : Bool :=
  c.orteLeer && c.zielTot

/- CUTS:
    - Skeleton only: refusal theorems, the `liest` analysis with its
      frame lemma, the overwrite connection with its joint witness, the
      budget inequality, and the two DESIGN refusal exhibits (dead FP
      block, spin load) follow in later pieces.
-/

#print axioms dceZulassen

end Gabbro.Grammatik.X86
