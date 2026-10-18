/-
  File:      Grammatik/ReferenzB.lean
  Subject:   REFERENCE FIXTURE (attempt B) -- one shared table, one lock,
              two functions, reached runs on both machines that move memory.

  Design: `refD` has one table `konto` (2 slots, one `.int 0 100` field),
  one lock `m` guarding it (`braucht`), and two functions over `Bool` ids:
  `einzahlen` (`true`: one `.int 0 10` param, no result, writes) and `lies`
  (`false`: no params, returns `.int 0 100`, reads). The `einzahlen` body is
  straight-line `write; call lies; ret` so that, from `RufStartD`, thread 1
  fires `nimmt`, a writing `blatt`, `ruf`, `rueck` in that order (the call
  machine never unfolds compounds, so no `ite` appears: the write stores the
  constant cap `100`, the upper branch of the `min`).

  Later lanes build their rule-13 witnesses on `refD`/`refP`/`refO`/`refSp0`
  and the two reached runs below.
-/

import Grammatik.Korrespondenz.Allgemein.ReferenzB.T1
import Grammatik.Korrespondenz.Allgemein.ReferenzB.T2
import Grammatik.Korrespondenz.Allgemein.ReferenzB.T3
