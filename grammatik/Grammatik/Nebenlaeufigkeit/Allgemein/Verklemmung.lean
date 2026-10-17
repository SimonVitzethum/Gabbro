/-
  File:      Grammatik/Verklemmung.lean
  Subject:   DEADLOCK FREEDOM FROM LOCK RANKS on machine G (SATZKARTE §13.5
             progress item 1, §16.3).

  The checker enforces the rank order (`H006`: a `locks L` ranks above every
  lock its holdings name, in the syntax `Stmt.locks … hr`) and forbids
  re-taking (`H003`); across calls the lock floors (`Signatur.boden`,
  `RufPasst.hx`/`hb`, `StufenOk`) carry the order to locks a caller holds
  and the callee does not name. G's `dannLocks` fires only if the lock is
  not held by the thread (`hself`), ranks above EVERY lock the thread holds
  (`hrang`, a check on the machine's held set, not on the syntax), and no
  other thread holds it (`RufFreiG`). Nothing proved that the first two
  side conditions ever hold; a thread at a `locks` head could be stuck for
  a reason no scheduler resolves.

  **The thread invariant** `RangInvG` (on every reachable machine,
  `rangInvG_erreichbar`): the held locks are duplicate-free, and down the
  stack every held lock is NAMED by a frame, or ranks below that frame's
  floor, or ranks at least the floor of the frame directly above (it was
  taken by a callee); every frame's signature locks are named by the frame
  below it, floors rise towards the head, and every `locks` still ahead of
  a frame ranks at least that frame's floor (`bodenM`, the residue form of
  `StufenOk`). The stack's bottom frame is the start function's.

  **The consequences.**
  * `sperre_rang`: at a `locks L` head every lock the thread holds ranks
    below `L` -- `hself` and `hrang` hold; `schritt_an_sperre`: the step
    fires unless another thread holds `L`.
  * `keine_verklemmungG`: on no reachable machine is every unfinished thread
    waiting for a lock another thread holds (given that start functions hold
    no lock by signature, and a complete list of locks): the waited-for lock
    of a waiting thread ranks strictly below the lock its holder waits for,
    and ranks are bounded on finitely many locks.
-/

import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung.T1
import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung.T2
import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung.T3
