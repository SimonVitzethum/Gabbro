-- Audit 45 probe B: `contrProjRegel` is unconnected to the build.
-- Pattern (d): the docstring says the rule "ties non-contract steps to the
-- atom lists", but the Lean states a one-sided implication (gates only the
-- `ev = none` case), and nothing in the build consumes it.
-- Demonstration: a rule over entries/returns is trivially inhabited by a
-- run with NO non-contract steps, and the converse direction (atom lists
-- constraining steps) is not stated at all.
import Grammatik.VertragOrtB

namespace GabbroAudit45B

open Gabbro.Grammatik

-- A run whose every step carries an event satisfies the rule vacuously:
-- the rule constrains only `ev = none` steps, so contract-event runs
-- are unconstrained by the atom lists.
example (D : Deklaration) (L : ContrLauf D)
    (hall : ∀ c, c ∈ L.schritte → c.ev ≠ none) :
    contrProjRegel L := by
  intro c hc hev
  exact absurd hev (hall c hc)

#print axioms Gabbro.Grammatik.contrProjRegel

/-
CUTS:
- No claim that `contrProjRegel` is false; it is true but one-sided.
  The audit point is the gap between the docstring ("ties steps to atom
  lists") and the Lean (only `ev = none` steps must hit a non-contract
  atom; the atom lists never constrain event-carrying steps).
- Non-use in the build is a grep observation, not a Lean theorem.
-/
