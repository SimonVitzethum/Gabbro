/-
  File:      Grammatik/ZielOrtAx.lean
  Subject:   `ziel_ort_voll_ax` -- `ziel_ort_voll` over the STRENGTHENED user
             obligation `KoerperGutA` (the body triple against every oracle
             that respects the declared axiom frames AND meets the axioms'
             declared ensures `Q`), with the hardware premise `AxVertragO Q O`
             and the locality `AxEnsLokal Q`.

  The acting-thread lemma, the rely, the start and the step are the ones of
  `ZielOrtVoll.lean`, over the replay of `ZielOrtAxBeweis.lean`; the only
  changes are the invariants (`FadenA`/`ZielInvA`), the obligation, and the
  two hypotheses threaded to where the obligation is applied or an axiom
  answer is recorded.
-/

import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAx.T1
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAx.T2
