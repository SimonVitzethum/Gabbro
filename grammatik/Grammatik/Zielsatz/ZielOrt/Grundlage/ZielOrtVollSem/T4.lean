/- Part 4 of 4 of `ZielOrtVollSem` (split by instrumente/teile/lean-teilen.py; the umbrella `ZielOrtVollSem.lean` imports all parts). -/
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollSem.T3

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## CUTS:

  What is proved: the covered fragment `vOk K` (every form but `regLies`,
  `regLiesElse`, `awaits`; indirect calls where `K` admits the pointer's
  signature), its decided form `programmImFragmentV` with soundness
  (`kandB_kandP`, `programmImFragmentV_ok`) and monotonicity (`vOk_mono`),
  the inclusion of the old fragment (`programmImFragmentV_of`); the frame
  semantics
  `weiterZ`/`semV` of EVERY residue of G, with the pass-through lemmas
  (`weiterZ_logik`, `weiterZ_zurueck`, `weiterZ_grund`,
  `weiterZ_hardware`) and the end-block refinement (`weiterZ_ende_folgt`);
  the preorder `ZErg.folgt`; the residue predicate `GRest.okV`.

  What is NOT here: the replay itself (`ZielOrtVollBeweis.lean`).
-/

#print axioms Gabbro.Grammatik.programmImFragmentV_of
#print axioms Gabbro.Grammatik.programmImFragmentV_ok
#print axioms Gabbro.Grammatik.weiterZ_zurueck
#print axioms Gabbro.Grammatik.weiterZ_ende_folgt
#print axioms Gabbro.Grammatik.ZErg.folgt_trans


end Gabbro.Grammatik
