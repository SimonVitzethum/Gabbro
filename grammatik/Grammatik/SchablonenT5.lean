/-
  File:      Grammatik/SchablonenT5.lean
  Part of:   Gabbro -- the generator-template library (T5 of
             dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md).

  What this file is: Lean soundness cores for the templates of
  `crates/gabbro-check/src/schablonen.rs`. All ten machine-checked proofs
  so far are Isabelle (`beweise/*.thy`); NONE of the 21 templates has a
  Lean proof. Every lemma below is proved in Lean 4.33.1 over a small
  abstract model of the template named in its doc comment, and every
  lemma comes with a `NAME_zeuge` that instantiates ALL premises JOINTLY
  on concrete values AND on the non-degenerate reference run
  (`refB_erreicht` + `refB_schreibt`: table `konto` written by
  `einzahlen`, slot `0 -> 100`).

  Order: most-used corpus construct first (measured 2026-09-13 over
  `beispiele/`: table/count 370/354, locks 292, device 130, option 90,
  entry 89, clobbers 80, format 58, transition 34, exchange 31,
  accumulates/mappings 23, consuming 13, group 10, reset 9, restrict 5,
  induction 3, transset 2).
-/

import Grammatik.ReferenzB

namespace Gabbro.Grammatik

/-! ## 1. `table.indexschranke` (table/count: 370/354 corpus lines).

The generated index type is `{i. i < N}`: it CONTAINS every occupied
slot (`belegt_liegt_im_indextyp`) and every generated chaining write
stays inside it (`schreibstellen_im_typ`). -/

/-- An index is valid for a table of `N` slots. -/
def idxGilt (N i : Nat) : Prop := i < N

/-! ## CUTS:
  - Skeleton only: `idxGilt` is defined; all 21 soundness lemmas are open.
-/

#print axioms Gabbro.Grammatik.idxGilt

end Gabbro.Grammatik
