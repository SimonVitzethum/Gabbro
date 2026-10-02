/-
  File:      Grammatik/X86/IntegerHardwareForms.lean
  Subject:   Practical integer logical/test rows over shared width-parametric rules.

  Lane 666: missing practical scalar AND/OR/TEST/NOT/NEG rows reusing the
  canonical producers (Ganzzahl andB/orB/notB, ShiftLogic negW/logikFlags/
  NegGueltig, NarrowOps mergeRegNarrow). No new evaluator of pilot forms,
  no integer-to-pointer conversion. AF none is undefined, never false.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ganzzahl
import Grammatik.X86.ShiftLogic
import Grammatik.X86.NarrowOps
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec

namespace Gabbro.Grammatik.X86

/-- Practical integer logical rows: register AND/OR, non-writing TEST,
    flag-preserving NOT, flag-defining NEG. Width is explicit data. -/
inductive IntHwOp where
  | andRR (b : Breite) (dst src : Register)
  | orRR (b : Breite) (dst src : Register)
  | testRR (b : Breite) (lhs rhs : Register)
  | notR (b : Breite) (dst : Register)
  | negR (b : Breite) (dst : Register)
  deriving DecidableEq, Repr

/-- Shared value dispatch: every row routes to its canonical producer. -/
def intHwWert (op : IntHwOp) (x y : Wort) : Wort :=
  match op with
  | .andRR b _ _ => andB b x y
  | .orRR b _ _ => orB b x y
  | .testRR b _ _ => andB b x y
  | .notR b _ => notB b x
  | .negR b _ => negW b x

/-- Routing is definitional for each row. -/
theorem intHwWert_routen (b : Breite) (x y : Wort) (d s : Register) :
    intHwWert (.andRR b d s) x y = andB b x y ∧
    intHwWert (.orRR b d s) x y = orB b x y ∧
    intHwWert (.notR b d) x y = notB b x ∧
    intHwWert (.negR b d) x y = negW b x := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/- CUTS:
    Skeleton only: codec/step/fetch/witnesses are open.
-/

#print axioms intHwWert_routen

end Gabbro.Grammatik.X86
