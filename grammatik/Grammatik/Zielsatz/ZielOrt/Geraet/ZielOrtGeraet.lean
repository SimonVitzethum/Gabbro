/-
  File:      Grammatik/ZielOrtGeraet.lean
  Subject:   `ziel_ort_geraet` -- `ziel_ort_voll` with the device forms:
             register reads (with and without `else`), `awaits`, and (as
             before) register writes, `transition`, `exchange`; the acting
             thread keeps its replay under every rule of G, the other threads
             keep theirs by the rely over the widened footprint.

  The replay invariants and steps are in `ZielOrtGeraetBeweis.lean`, the
  hardware class, the widened fragment and footprint, and the frame
  semantics of the device forms in `ZielOrtGeraetSem.lean`.
-/

import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraet.T1
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraet.T2
