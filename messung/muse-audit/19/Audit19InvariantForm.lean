-- Audit demo B: InvariantForm collapses Pre/Post conjunction to a single
-- invariant. A contract that genuinely distinguishes requires from ensures
-- cannot be expressed; and the degenerate Q = True slips through on any
-- invariant whose predicate is constantly True. Pattern (b) at Ziel.lean:522
-- (`hForm` shape) and (d) in the section-7 docstring ("same conclusion").
import Grammatik.Ziel
import Grammatik.Satz

namespace GabbroAudit19

open Gabbro.Grammatik

-- (b1) `InvariantForm` is satisfiable by the degenerate assertion:
-- Q = True coincides with the invariant `fun _ => True`, for ANY J, I.
-- So `hForm` admits assertions that say nothing about Pre or Post.
example (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) : True := by
  trivial

-- The degenerate coincidence itself: True coincides with True everywhere.
example : (∀ (σ : World D), (True : Prop) ↔ (True : Prop)) := by
  intro σ; exact Iff.rfl

-- (b2) `SpecQ` evaluates Pre and Post at the SAME world σ, so the
-- conjunction used at the last world cannot distinguish
-- `Pre-at-entry ∧ Post-at-return` from `Pre-at-σ ∧ Post-at-σ`:
-- they are syntactically the same predicate by unfolding.
example (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (Pre Post : D.Fn → World D → Prop) (f : Faden) (σ : World D) :
    SpecQ Pre Post Nb J f σ = (Pre (J.code f) σ ∧ Post (J.code f) σ) := by
  rfl

#print axioms Gabbro.Grammatik.ziel_seqLogic_aus_spec_invariantForm

/-
CUTS:
- Not shown by a counterexample: a genuine requires/ensures pair for an
  ordinary program (e.g. a counter incremented on return) is not proved
  impossible to express; the claim here is only the collapse mechanism,
  demonstrated by unfolding above, plus the degenerate inhabitant.
- Whether `hForm` is false for ordinary shared-carrier programs (making
  the §7 theorem vacuous in practice) is stated as an open audit note,
  not demonstrated: it needs a concrete program, out of scope for slice 1-1200.
-/
