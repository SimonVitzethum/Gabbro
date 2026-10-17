/-
  File:      Grammatik/HoareRegeln.lean
  Subject:   SEQUENTIAL HOARE RULES OVER execBlock, blocks WITHOUT calls.

  `HTripel` is partial correctness over the actual sequential semantics:
  starting from any world/env where `Pre` holds, if the block ends normally
  (`.ok σ' ρ'`), then `Post` holds there. Contracts hold at their place
  with the actual values; pre/post are predicates over the actual world
  AND environment, never quantified over environments.

  `BlockOhneRuf` says a block performs no call: no `call`/`callInd` in any
  statement, no `bindCall`/`bindCallInd`/`bindCallElse` in any block spine,
  and nested blocks preserve the property. Lemma `ohneRuf_Runabhaengig`
  proves the meaning: on such blocks `execBlock` is independent of the
  call-meaning parameter `R`.
-/

import Grammatik.Logik.Ruf.Hoare.HoareRegeln.T1
import Grammatik.Logik.Ruf.Hoare.HoareRegeln.T2
import Grammatik.Logik.Ruf.Hoare.HoareRegeln.T3
import Grammatik.Logik.Ruf.Hoare.HoareRegeln.T4
