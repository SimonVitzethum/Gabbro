/-
  File:      Grammatik/RufAdaequatRufG.lean
  Subject:   ADEQUACY OF THE CALL MACHINE G FOR BODIES WITH CALLS (Target 4) --
             the sequential semantics, run with the handler `rufRumpf` that
             executes the callee's BODY, is realised by steps of one thread of
             the repaired machine, by induction on the nesting depth.

  Why: `RufAdaequatG.lean` proves adequacy for CALL-FREE bodies. A call is
  where the machine differs structurally from `execStmt` (a frame push, the
  callee's steps, a pop), and where G was wrong (`ruf` repeated the call
  after `rueck`; a verbatim pop could restore a WAITING caller and
  deadlock; the error channel of `let x = g(…) else { … }` had no rule;
  all repaired in `RufMaschineG.lean`). This file extends the covered
  fragment by direct calls in block position (`call` in `dann`), at `ende`
  position and bind-calls (`let x = g(…)`, with or without an else block,
  both paths), by callees answering a reason (`retGrund`), by the loops
  `traverse`, bounded `retry` and `forever` (with its budget), and by
  `leave`/`next` (the machine peels the scaffolding the loop body built and
  fires the loop shim), and proves: a body in the extended fragment whose
  callees' bodies are themselves in the fragment one level down
  (`Tief P A n`), started at the thread's world, returns in the machine
  exactly what `execEnd O passes (rufRumpf P O passes n)` returns
  (`rufG_adaequat_ruf`), for every nesting depth `n`.

  The handler: `rufRumpf n f σ ρ` runs `P.rumpf f` with `execEnd` and handler
  `rufRumpf (n - 1)`; depth `0` is `logik (abstieg f)` like `rufAt`. It is
  NOT `rufAt`: `rufAt` also checks `requires`/`ensures`/invariants and READS
  their places (trace events); the machine checks no contract, so the
  handler that the machine realises is the bare body run.
-/

import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T1
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T2
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T3
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T4
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T5
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T6
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T7
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T8
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T9
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T10
