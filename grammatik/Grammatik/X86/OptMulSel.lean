/-
  File:      Grammatik/X86/OptMulSel.lean
  Subject:   Multiply selection rule: 3-operand IMUL for constant multiplies.

  Lane 888: the DESIGN §3A tile "3-operand `IMUL r, r/m, imm8/imm32` for
  constant multiplies with a proved range (strength reduction cites the §3
  row, never a bare pattern)" as a generic rule lemma over arbitrary values
  with validator-decided side conditions (DESIGN §7 strength-reduction row:
  local premise "per-width flag/fault identity lemma (CF vs OF distinct)",
  certificate "A register rule", failure "imul r,8 -> shl r,3 with live CF").
  Reuses the canonical vocabulary (`Typen`, `Syntax`, `Semantik`,
  `ReferenzB`, `X86.Typen`, `X86.Wort`, `X86.Ganzzahl`, `StaerkeReduktion`,
  `MulDiv`); the single accepted IR is not available, so the connection is
  stated over the real `Syntax`/`Semantik` `execEnd` fragment it covers.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Ganzzahl
import Grammatik.X86.StaerkeReduktion
import Grammatik.X86.MulDiv

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one constant-multiply site
    (DESIGN §7 row): the proved range is present at the site (`breiteOk`),
    the constant fits the imm8/imm32 encoding (`immPasst`), the
    per-width flag/fault identity is discharged (`flagsOk`: dead flags or
    the CF-vs-OF row cited), and the site is an integer multiply, never a
    float one (`keinGleit`: `a*2.0 -> a+a` is refused). -/
structure MulSelCert where
  breiteOk : Bool
  immPasst : Bool
  flagsOk : Bool
  keinGleit : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL selection
    keeps another certified translation, never a warning. -/
def mulSelZulassen (c : MulSelCert) : Bool :=
  c.breiteOk && c.immPasst && c.flagsOk && c.keinGleit

/- CUTS (skeleton):
    - Value/fault/observation connection, certificate shape, refusal cases,
      strength-reduction citation and joint witness follow in small pieces.
-/

#print axioms mulSelZulassen

end Gabbro.Grammatik.X86
