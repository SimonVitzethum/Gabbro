/-
  File:      Grammatik/X86/FloatSourceObservations.lean
  Subject:   Finite-value float observation equivalence over real source operations.

  Lane 624 (direct-source closure): proves which ACTUAL source observations can
  distinguish model-equivalent finite floats. Covered operators (pinned by the
  lemmas below): `fllt`/`flle` (`gleitLt`/`gleitLe`), `gleitNarrow` and `gleit`
  range-holding (`gleitPasst`), and the register-write truncation (`gleitRoh`).
  Float `==`/`!=` is EXCLUDED (F-EQ): `Expr.eq` takes only `.int` arguments, so
  no model term equates two floats. NaN non-inhabitation is a corollary: no
  `Gleit` value is NaN. Consumer hook: `cvttPaket`/`ucomiFlags` reuse pins for
  the ScalarFloat decoder consumer. Full source-to-final-bytes stays OPEN.
-/
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.Typen
import Grammatik.Gleitkomma
import Grammatik.X86.Gleitprofil
import Grammatik.X86.ScalarFloat

namespace Gabbro.Grammatik.X86

/-- Two finite floats agree on every model comparison, in all four
    directions, against every third value. This is the premise of the
    observation-equivalence fragment -- comparisons only, never a blanket
    "all observations agree" assumption. -/
def vergleichsGleich (x y : Gabbro.Grammatik.GFloat) : Prop :=
  ∀ z : Gabbro.Grammatik.GFloat,
    Gabbro.Grammatik.gleitLt x z = Gabbro.Grammatik.gleitLt y z ∧
    Gabbro.Grammatik.gleitLt z x = Gabbro.Grammatik.gleitLt z y ∧
    Gabbro.Grammatik.gleitLe x z = Gabbro.Grammatik.gleitLe y z ∧
    Gabbro.Grammatik.gleitLe z x = Gabbro.Grammatik.gleitLe z y

/-- First checked fact: signed zeros compare equal (strict, one direction). -/
theorem null_flt_still :
    Gabbro.Grammatik.gleitLt (Gleitkomma.nullN Gleitkomma.f64)
      (Gleitkomma.nullP Gleitkomma.f64) = false := by
  decide

/- CUTS:
    - Skeleton only: comparison agreement is defined, one strict-equality
      fact is proved. The `gleitRoh`/`gleitPasst` consequences, the NaN
      corollary, the F-EQ exclusion pin, the target reuse hooks and the
      joint table-write witness are still to come.
    - Full source-to-final-loaded-bytes validation remains OPEN.
-/

#print axioms null_flt_still

end Gabbro.Grammatik.X86
