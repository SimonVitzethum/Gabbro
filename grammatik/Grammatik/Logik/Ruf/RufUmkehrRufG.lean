/-
  File:      Grammatik/RufUmkehrRufG.lean
  Subject:   THE CONVERSE FOR BODIES WITH CALLS -- every run of one thread of
             the call machine G that pops a frame logs exactly the value the
             sequential semantics (with the body-running handler `rufRumpf`)
             returns, for bodies with direct calls and bind-calls.

  Why: `RufAdaequatG.lean` proves the converse (`rufG_adaequat_umkehr`) for
  call-free bodies; `RufAdaequatRufG.lean` proves the forward direction
  with calls (`rufG_adaequat_ruf`). Here the converse is extended by calls:
  while the frame of `fn` is on the stack, the frames above it form a
  pending call chain; each callee's frame result is DEMANDED by the frames
  below it (`Anspruch`), and every machine step keeps the demand of the top
  frame (`schrittErhaltK`, `invK_schritt`). When the run pops the frame of
  `fn` for the first time, its logged value is the sequential one
  (`rufG_adaequat_ruf_umkehr`).

  The fragment is the call-free, oracle-free fragment of the G converse
  plus `call` (block and `ende` position) and `let x = g(…)`: `StmtR`/
  `BlockR`/`EndR` restricted by the syntactic check `kOk` (no loops, no
  `leave`/`next`, no error channel, no indirect call, no oracle form). The
  depth `n` is any depth at which the body is covered (`TiefK P A n`),
  i.e. at least the nesting depth of the calls; nothing else bounds the run.
-/

import Grammatik.Logik.Ruf.RufUmkehrRufG.T1
import Grammatik.Logik.Ruf.RufUmkehrRufG.T2
import Grammatik.Logik.Ruf.RufUmkehrRufG.T3
import Grammatik.Logik.Ruf.RufUmkehrRufG.T4
import Grammatik.Logik.Ruf.RufUmkehrRufG.T5
import Grammatik.Logik.Ruf.RufUmkehrRufG.T6
