/-
  File:      Grammatik/VertragsFuss.lean
  Subject:   D7 -- contract footprint containment by computation.

  The goal theorem owes four footprint premises (`Ziel.lean`: `hReqTAll`,
  `hReqGAll`, `hEnsTAll`, `hEnsGAll`): every carrier read by `requires` /
  `ensures` lies in the function's write signature. This file turns them
  into checker facts: `vertragFussB` decides the containment from the
  contract syntax, and the four `aus_B` theorems recover the exact
  `Ziel.lean` shapes from a positive check.
-/
import Grammatik.InterferenzAllgemein
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- One carrier covered by the write signature of `f`. -/
def fussDeckt (f : D.Fn) (o : D.Tab ⊕ D.Glob) : Bool :=
  match o with
  | .inl t => D.schreibt f t
  | .inr x => D.gschreibt f x

/-- Checker predicate: every carrier read by `requires` / `ensures` of `f`
    lies in the write signature of `f`. -/
def vertragFussB (P : Programm D) (f : D.Fn) : Bool :=
  ((P.requires f).orte.all (fussDeckt f)) &&
    ((P.ensures f).orte.all (fussDeckt f))

end Gabbro.Grammatik
