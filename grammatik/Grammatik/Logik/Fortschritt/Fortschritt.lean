/-
  Gabbro/Grammatik/Fortschritt.lean

  **Progress up to named stops** (`Zielsatz.FortschrittG`, SATZKARTE §19.2).

  On every reachable machine of G, every thread is finished, waits for a
  lock another thread holds, stands at a named stop of one of three kinds
  (`Zielsatz.HaltBenannt`: `flagge`, a wait for a publication; `budget`, a
  spent `forever` budget; `hardware`, an axiom or register answer outside
  its declaration -- since 2026-09-15, verdict F3), or can step. The proof is a case analysis over
  every head shape of a frame residue against the rules of G
  (`RufMaschineG.lean`): at each shape either some rule fires (the `w_*`
  step builders of `RufAdaequatG.lean`/`RufAdaequatRufG.lean`) or one of
  the stops (finished, waiting, a named stop) applies.

  Three shapes had no rule and no stop, and are excluded by an invariant of
  every run (`FortInvG`, carried through every rule like `schrittMerk`):

  1. **The caller's shape at a pop** (SATZKARTE §13.5 item 6). A pop needs
     a caller that can receive the answer: a value return into a caller
     that does not wait (`rueck`) or waits for a value of the callee's
     result type (`rueckBind`); a reason into a caller waiting in
     `let … else` with the callee's reason count (`rueckGrund`).
     `FormKette`: every suspended frame has the shape of the call that
     suspended it (`FormG`): not waiting and the callee has no reasons
     (`call`, `callInd`), waiting for `τ` with `erg callee = some τ` and no
     reasons (`bindCall`, `bindCallInd`), or waiting in `wartetSonst n`
     with `erg callee = some τ` and `gruende callee = n` (`bindCallElse`).
  2. **An abrupt exit without a loop.** `leave`/`next` fire only when the
     continuation reaches a loop shim through `dann`/`schrumpf`/`frei`/
     `abbruch` layers (`GRest.absorb`); an `ende` node never stands inside
     a loop (`fOk`: its loop flag is `false`), and every continuation of a
     loop-flagged residue absorbs.
  3. **An `else` residue that falls through.** `abbruch k` has no rule: the
     block in front of it must not end normally. Every block in front of an
     `abbruch` chain ends in a return, reason, `leave` or `next`
     (`Block.terminal`; `Endblock.alsBlock_terminal`), and no residue that
     becomes the head behind a finished block is such a chain
     (`GRest.blockiert`).

  The only premises: `GutO` (axiom leaves extend the trace by accesses,
  static holdings held), `StufenM` and a duplicate-free start trace (the
  `locks` rule's rank side conditions, `sperre_rang`), and
  `KeinLogikHaltG` at the machine -- the conjunct of the flagship that says
  no `logik` check fails (loop invariants, `state` transitions) -- and
  `BereichG` (since 2026-09-15, verdict F1): no float range check fails. An
  out-of-range float is `logik bereich` in the sequential semantics, which
  the body obligation excludes; `fadenS_bereich` carries that to every
  thread of every reachable machine, as `fadenS_prueft` does for the
  `logik` checks.
-/

import Grammatik.Logik.Fortschritt.Fortschritt.T1
import Grammatik.Logik.Fortschritt.Fortschritt.T2
import Grammatik.Logik.Fortschritt.Fortschritt.T3
