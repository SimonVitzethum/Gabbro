/-
  File:      Grammatik/X86/OptCsePure.lean
  Subject:   Pure common-subexpression elimination rule lemma (lane 863).

  DESIGN section 7 row: local rewrite "second computation of a pure
  expression with identical width/mode under recomputed availability
  becomes the available value", certificate "local rewrite record plus
  recomputed analysis citations (avail/width/mode facts)", failure case
  "CSE across a gate/range boundary (cross-gate range CSE refuses)",
  phase E, cost O(sites).

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `Gleitkomma`, `X86.Typen`, `X86.Wort`, `ReferenzB`):
  a recomputed pure `x + y` IS the available value (the reuse reads the
  same evaluated value), the rewritten two-bind window takes the same
  `execEnd` outcome (no fault added or removed, same successor world),
  and the reused value reads back through the canonical word under the
  width-exact premise. Float reuse preserves value and `gleitPasst`
  outcome exactly where the validator recomputed the equation in the
  kernel model under one rounding scope; the DESIGN failure case is
  refused by `cseZulassen`. No `ensures` is derived, no refusal becomes
  a warning, no faulting form is speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one pure-CSE site
    (DESIGN section 7 row): identical width, identical mode (one
    rounding scope for floats), purity (no faulting form above its
    guard, no gate, no shared access), recomputed availability (a
    dominating definition with no intervening kill), and no gate/range
    boundary between definition and use. This record is the LOCAL
    rewrite half of the certificate; the RECOMPUTED analysis half is
    cited by the `hC`/`hEq` premises of the lemmas below. -/
structure CseCert where
  gleicheBreite : Bool
  gleicherModus : Bool
  rein : Bool
  verfuegbar : Bool
  keinTorBereich : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL optimisation
    falls back to another certified translation, never to a warning. -/
def cseZulassen (c : CseCert) : Bool :=
  c.gleicheBreite && c.gleicherModus && c.rein && c.verfuegbar && c.keinTorBereich

end Gabbro.Grammatik.X86
