/-
  File:      Grammatik/ZielOrtRahmen.lean
  Subject:   `ziel_ort_rahmen` -- `ziel_ort_geraet` over the WEAKER user
             obligation `KoerperGutR`: the body triple against call handlers
             that respect the callees' contracts AND their declared frames
             (`RespektiertRahmen`, `ZielOrtRahmenSem.lean`). A caller may use
             that a callee changes only what its signature declares written.

  The acting-thread lemma, the rely, the start and the step are the ones of
  `ZielOrtGeraet.lean`, over the replay of `ZielOrtRahmenBeweis.lean`. The one
  new input is the machine's frame fact `rufG_rahmen` (a separate invariant
  of every reachable machine): at every pop, the return world agrees with
  the callee's entry world on the caller's footprint outside the callee's
  declared writes; `popR_kopf` records the call answer with that frame.
-/

import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmen.T1
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmen.T2
