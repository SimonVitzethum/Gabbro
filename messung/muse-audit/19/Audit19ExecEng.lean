-- Audit demo C: `ExecEng.provenienz` over-approximates real `exec` traces.
-- Its worlds `a`/`b` are fully unconstrained except `a.spur = []` and
-- `Brav`; in particular `b`'s memory need not come from any `exec` run.
-- Pattern (e)/(d): the docstring says "per-thread Brav provenance from
-- exec traces", but any Brav pair counts. Ziel.lean:218-232.
import Grammatik.Ziel
import Grammatik.Satz

namespace GabbroAudit19

open Gabbro.Grammatik

-- A Brav pair with ARBITRARY memory: `Brav.refl` over a world with empty
-- trace satisfies every conjunct of `provenienz`'s inner existential,
-- without mentioning `exec`, `execStmt`, `eval`, or any program.
-- Hence `provenienz` admits full traces that no body ever produced.
example (σ : World D) (h : σ.spur = []) (f : Faden)
    (voll : Faden → List (Ereignis D)) (hempty : voll f = []) :
    ∃ a b : World D, a.spur = [] ∧ Brav a b ∧ b.spur = voll f := by
  exact ⟨σ, σ, h, Brav.refl σ, by rw [hempty]; exact h⟩

-- `Brav.refl` never changes memory, so `provenienz` can be discharged by
-- traces whose worlds carry no computed values at all: a semantics that
-- cannot change memory (rule 4c concern), demonstrated as an inhabitant.
example (σ : World D) :
    Brav σ σ ∧ σ.spur = σ.spur ∧ σ.slots = σ.slots ∧ σ.globs = σ.globs := by
  exact ⟨Brav.refl σ, rfl, rfl, rfl⟩

#print axioms Gabbro.Grammatik.Brav.refl

/-
CUTS:
- Not shown: that `ExecEng` is actually INSTANTIATED with such degenerate
  witnesses anywhere downstream; the finding is about the shape admitting
  them, i.e. the narrowed class is narrowed only on paper for W1/W2.
- No claim about W3-W5 here; they genuinely constrain the run.
-/
