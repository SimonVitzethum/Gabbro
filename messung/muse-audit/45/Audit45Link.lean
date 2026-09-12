-- Audit 45 probe D: `ensAmRueck_gibt_qensures_pkt` proves its goal from `w`.
-- Pattern (a): the stated link between `EnsAmRueck` and `QEnsuresB` takes
-- BOTH the place-check `h` AND the quantified check `w`, then concludes by
-- applying `w v rho` alone (`have hv := w v rho`; `h` only rewrites along
-- `hs : s0 = sigma`). Without `w` the goal is unprovable from `h`: `h` is
-- about the pair (v, rho) while the goal quantifies over nothing new, yet
-- the proof never extracts content from `h` beyond its rewrite form.
-- Demonstration: from `w` alone (plus the world equation) the same equality
-- `wahr? ... = true` follows; `h` contributes only the transport.
import Grammatik.VertragOrtB

namespace GabbroAudit45D

open Gabbro.Grammatik

-- The conclusion is already `w v rho` up to the `hs` rewrite: `h` is not
-- needed as a truth source, only as a transported spelling.
example (P : Programm D) (f : D.Fn)
    (s0 : World D) (sigma : World D) (rho : Env D (D.params f))
    (v : ErgVal D (D.erg f))
    (hs : s0 = sigma)
    (w : QEnsuresB P f sigma) :
    wahr? (eval sigma (P.ensures f) sigma (ergEnv (D.erg f) v rho)) = true := by
  have he : eval s0 (P.ensures f) sigma (ergEnv (D.erg f) v rho) =
      eval sigma (P.ensures f) sigma (ergEnv (D.erg f) v rho) := by
    rw [hs]
  have hw := w v rho
  exact hw

#print axioms Gabbro.Grammatik.ensAmRueck_gibt_qensures_pkt

/-
CUTS:
- No claim the lemma is false. The audit point is pattern (a)-adjacent:
  the conclusion is the premise `w` at (v, rho) transported along `hs`;
  the place-check `h` supplies no independent content (any `h`-shaped
  proof of the transported spelling would do, including `w v rho`
  itself). The "link" therefore does not lift place truth to quantified
  truth; it restates quantified truth at one point.
-/
