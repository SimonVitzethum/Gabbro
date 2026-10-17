/-
  File:      Grammatik/RufAdaequatG.lean
  Subject:   ADEQUACY OF THE CALL MACHINE G -- the machine computes what the
             sequential semantics computes (single thread, call-free bodies).

  Why: the Hoare rules (`HoareRegeln.lean`, `HoareRuf.lean`) are stated over
  `execStmt`/`execBlock`/`execEnd`. A contract proved with them talks about
  MACHINE runs only if the machine `RufSchrittG` computes the sequential
  result. This file proves that for the covered fragment: a head frame
  whose residue is `.ende b` for a call-free end block `b`, run by steps of
  its own thread only, pops with a `rueck` event carrying EXACTLY the value
  `execEnd` returns, and the shared memory ends where `execEnd` ends.

  The proof is a simulation, mutual over `Stmt`/`Block`/`Arms`/`GrundArms`
  like `execStmt`: a block `b` in `dann b k` position, started at world `σ`
  and environment `ρ`, runs to the continuation `k` at the world and
  environment `execBlock` returns (`.ok`), or pops the frame with the value
  `execBlock` returns (`.zurueck`).

  Main results: `rufG_adaequat` (TARGET A), `rufG_adaequat_R` (A under any
  call handler), `rufG_adaequat_umkehr` (TARGET B: every f-only run that
  pops the frame logs the value `execEnd` returns -- proved through a frame
  semantics `semR` that each of the 70 step rules preserves,
  `schrittErhalt`), with witnesses `rufG_adaequat_zeuge`,
  `rufG_adaequat_umkehr_zeuge`. Two findings against G's rules were
  machine-checked here (`traverse` with a false invariant; `ruf` re-entering
  the callee after `rueck`); both rule families are repaired in
  `RufMaschineG.lean`, and the findings became agreement theorems
  (`trav_falsch_steht`, `trav_einig`, `ruf_fortsetzung`). Bodies WITH calls:
  `RufAdaequatRufG.lean`.
-/

import Grammatik.Logik.Ruf.RufAdaequatG.T1
import Grammatik.Logik.Ruf.RufAdaequatG.T2
import Grammatik.Logik.Ruf.RufAdaequatG.T3
import Grammatik.Logik.Ruf.RufAdaequatG.T4
import Grammatik.Logik.Ruf.RufAdaequatG.T5
import Grammatik.Logik.Ruf.RufAdaequatG.T6
import Grammatik.Logik.Ruf.RufAdaequatG.T7
import Grammatik.Logik.Ruf.RufAdaequatG.T8
import Grammatik.Logik.Ruf.RufAdaequatG.T9
import Grammatik.Logik.Ruf.RufAdaequatG.T10
import Grammatik.Logik.Ruf.RufAdaequatG.T11
import Grammatik.Logik.Ruf.RufAdaequatG.T12
