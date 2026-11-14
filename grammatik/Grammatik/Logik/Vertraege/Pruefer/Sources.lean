module

public import Grammatik.Logik.Vertraege.Pruefer.Program

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

variable {D : Deklaration}

/-- Reification of the declared oracle predicates. Correspondence is produced
    by elaboration; no truth or locality proof is supplied by the user. The
    checker checks the source's footprint, not this proof field. -/
structure AxiomSources (Q : AxEns D) where
  items : List D.Ax
  complete : ∀ a, a ∈ items
  resources : D.Ax → List (Res D)
  expression : ∀ a, Expr D (ErgCtx [] (D.aerg a)) (resources a) .bool
  correct : ∀ a world value,
    eval world (expression a) world (ergEnv (D.aerg a) value .nil) = Q a world value

/-- The finite source interface table bounds every conforming target. This
    describes the declaration's layout, not semantic contract refinement. -/
structure PointerSignatures (D : Deklaration) where
  count : Nat
  outside : ∀ f n, count ≤ n → D.passt f n = false

end Gabbro.Grammatik.Vertraege.Pruefer
