-- Audit demo A: `ziel_seqLogic_aus_spec` conclusion coincides with head,
-- never with the actual execution result. `SpecQ` quantifies `Pre` AND `Post`
-- at the SAME world, so the "return" leg is evaluated at entry worlds too.
-- This shows pattern (b) at Ziel.lean:454 and pattern (d) in its docstring.
import Grammatik.Ziel

namespace Gabbro.Grammatik

open Extraktion in
-- Pattern (b): Pre and Post coincide at the SAME sigma, at entry time.
-- `requiresEigen` is a bare `iff`: it holds for ANY Pre that is
-- preserved by own steps, including the degenerate `fun _ _ => True`.
example (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (f : Faden) (hf : f ∈ J.faeden) :
    SpecTriple (fun _ _ => True) (fun _ _ => True) Nb J f := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _; trivial
  · intro _ _; trivial
  · intro _ _ _ _ _ _; exact Iff.rfl
  · intro _ _ _ _ _ _; exact Iff.rfl

-- Pattern (a): with Pre = Post = True the conclusion `SpecQ ... σ`
-- at the LAST world is definitionally `True ∧ True`, i.e. no information
-- about the run flows from the premises to the conclusion.
example (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (σ : World D) (f : Faden) :
    SpecQ (fun _ _ => True) (fun _ _ => True) Nb J f σ ↔ True ∧ True := by
  rfl

#print axioms Gabbro.Grammatik.ziel_seqLogic_aus_spec

/-
CUTS:
- Not shown: whether an ordinary (non-degenerate) contract really pins
  entry vs return values; that needs QRequires/QEnsures shapes, which
  live downstream and are not wired here (own remainder R1).
-/
