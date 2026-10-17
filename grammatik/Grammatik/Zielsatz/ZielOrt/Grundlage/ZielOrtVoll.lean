/-
  File:      Grammatik/ZielOrtVoll.lean
  Subject:   `ziel_ort_voll` -- the acting thread keeps its replay under every
             rule of G, the other threads keep theirs by the rely, and the
             theorem.

  The replay invariants and the steps that record or pop are in
  `ZielOrtVollBeweis.lean`; the frame semantics of every residue in
  `ZielOrtVollSem.lean`.
-/

import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll.T1
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll.T2
