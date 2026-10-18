/- Part 10 of 10 of `RufAdaequatRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatRufG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T9

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## CUTS:
  What is proved: TARGET 4 (`rufG_adaequat_ruf`) -- for a body in the
  fragment `EndR`/`StmtR`/`BlockR` (the covered fragment of
  `RufAdaequatG.lean` plus direct `call` in block and `ende` position,
  `let x = g(…)`, `let x = g(…) else { … }` with BOTH its paths,
  `retGrund` (a callee answering a reason), `traverse`, bounded `retry`
  with its overflow block, `forever` with its `passes` budget, and
  `leave`/`next` inside loop bodies), whose callees are admitted at
  nesting depth `n` (`Tief`), the machine realises `execEnd` with the
  body-running handler `rufRumpf n`, by induction on `n` (`rufOk_tief`,
  whose callee obligation `RufOk` now has an error-channel half); the
  call-free fragment embeds at every depth (`endG_tief`). The premise
  `hnw : caller.wartend = false` is new (the repaired verbatim pops demand
  it). Joint witnesses on non-degenerate programs
  (`rufG_adaequat_ruf_zeuge`, `…_bind`, `…_schleife`, and new:
  `rufG_adaequat_ruf_zeuge_leave` -- a `forever` pass writes and leaves
  through an `if`, `traverse` iterations take `next` through an `if`;
  `rufG_adaequat_ruf_zeuge_sonst` -- both paths of `let … else`, the error
  path through `rueckConsGrund`). The former deadlock finding is an
  agreement (`wartet_einig`; with the value half, `wartet_einig_voll` in
  `RufUmkehrRufG.lean`), and a NOTE (`befund_vertrag`). What is NOT proved:

  - Indirect calls (`callInd`, `bindCallInd`): the callee is the pointer's
    VALUE, so the admission is a premise over every function of the
    signature; `D.Fn` is an arbitrary type in the model (no finiteness),
    so such a premise is not over finitely many functions -- not done.
  - `axiomCall`/`bindAxiom` (the oracle's effect on the world), and
    `ret`/`retGrund`/`let … else` under a `locks` body (`mr = false`: the
    machine pops without the `gibt` that `execStmt`'s `locks` appends).
    Else branches (`sonst`, `err`) stand at loop level `false` only: an
    exit through an else branch inside a loop body jumps to `ende` and
    discards the loop shim (G's CUTS).
  - A `traverse`/`retry`/`forever` whose invariant/`until` read or budget
    makes `traverseLauf`/`retryLauf`/`foreverLauf` end in `logik`/
    `hardware` is outside the normal and return outcomes proved here (the
    machine is stuck there: `trav_falsch_steht`; `ewig 0` and a false
    `forever` invariant have no rule).
  - Contracts: `rufRumpf` checks no `requires`/`ensures`/invariant and the
    machine neither; `exec` (through `rufAt`) does, and reads their places.
    So the adequacy is against `rufRumpf`, not `rufAt` (`befund_vertrag`).
  - Adequacy is existential (SOME f-only run realises the result). The
    converse (ALL runs up to the first pop) is `RufUmkehrRufG.lean`, for
    the loop-free, error-channel-free part of the fragment.
  - The log is described only as `rueck … :: (ext ++ log)`: the calls'
    events `ext` are not characterised (they are balanced
    `eintritt`/`rueck`/`grund` pairs by `rufG_treu`'s invariant).
  - Depth: `Tief P A n` admits callees by depth; recursion deeper than `n`
    is `logik (abstieg f)` sequentially and no claim is made.
-/

#print axioms Gabbro.Grammatik.rufOk_tief
#print axioms Gabbro.Grammatik.rufG_adaequat_ruf
#print axioms Gabbro.Grammatik.endG_tief
#print axioms Gabbro.Grammatik.rufG_adaequat_ruf_zeuge
#print axioms Gabbro.Grammatik.rufG_adaequat_ruf_zeuge_bind
#print axioms Gabbro.Grammatik.rufG_adaequat_ruf_zeuge_schleife
#print axioms Gabbro.Grammatik.rufG_adaequat_ruf_zeuge_leave
#print axioms Gabbro.Grammatik.rufG_adaequat_ruf_zeuge_sonst
#print axioms Gabbro.Grammatik.travOkR
#print axioms Gabbro.Grammatik.travRetR
#print axioms Gabbro.Grammatik.foreverOkR
#print axioms Gabbro.Grammatik.foreverRetR
#print axioms Gabbro.Grammatik.retryAbbR
#print axioms Gabbro.Grammatik.blockAbbR
#print axioms Gabbro.Grammatik.wartet_einig
#print axioms Gabbro.Grammatik.befund_vertrag
#print axioms Gabbro.Grammatik.stmtOkR
#print axioms Gabbro.Grammatik.endRetR


end Gabbro.Grammatik
