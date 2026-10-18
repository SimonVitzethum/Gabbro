/-
  File:      Grammatik/Lebendigkeit.lean
  Subject:   A WAITING BOUND ON MACHINE G (PLAN-ZIELSATZ §8, liveness; KostenG
             TARGET 4): a thread standing at `locks L` takes `L` within
             `wartezeit L` scheduler steps -- under ONE named runtime assumption
             (a FIFO/ticket lock and a scheduler with fairness window `F`), a
             hold-time premise, and the facts the goal theorem supplies.

  THE RUNTIME ASSUMPTION (one entry of the ONE assumption list,
  `LaufzeitAnnahme R F`):
  * `FifoSperre R` -- a FIFO/ticket lock: the thread that takes `L` has stood
    at `locks L` at least since every other thread now standing there
    arrived. (Ties at the start machine are allowed either way.)
  * `FairF R F` -- bounded fairness: a thread that can step at every one of
    `F` consecutive scheduler steps takes one of them. `F` is a named
    constant of the scheduler (round robin over `T` runnable threads with one
    G step per turn: `F = T`).
  Runs are INFINITE (`PlanLauf`): a scheduler step is a step of machine G, or
  a stutter at a machine where no thread can step (a finished program). A
  stutter changes nothing.

  THE HOLD-TIME PREMISE (`Haltezeit R h k`): on every stretch of the run on
  which thread `u` holds `L`, `u` takes at most `h L` own steps, at most
  `k L` of them at a `locks` head (nested acquisitions). It is a PREMISE on
  the run, NOT derived: the checker decides `held <= N ops` (`K002`,
  kosten.rs `sperrbloecke`) in OPERATIONS with callees at their declared
  `costs`, and two bridges are missing -- (1) operations to G steps (KostenG
  TARGET 3 found that G takes steps the checker prices at `0`, findings
  F1-F9; `spiegel_stmt` goes the other way with a remainder `zusatz`), and
  (2) a bound for the `locks` BODY as a residue segment: `frame_schritte_
  beschraenkt` bounds a FRAME from entry to return (`Eintritt`/`aktivVor`),
  and a `locks` body is not a frame; its potential would have to be carried
  through the residue `.dann body (.frei L k)` across all 72 rules.

  THE BOUND, recursive over ranks (`wF`, fuel = the number of locks):
    S(L) = h(L)·F + k(L)·Wn(L)          one critical section of `L`
    Wn(L) = max { W(L') | rang L < rang L' }   a nested wait
    W(L) = (c(L) - 1)·(S(L) + F) + F     `c(L)` = the contenders for `L`
  Each own step of the holder is preceded by at most `F` scheduler steps
  (fairness) or, if it is a nested acquisition, by at most `Wn(L)` (the
  bound one rank up -- the holder stands at `locks L'` with `rang L < rang L'`
  by the rank invariant); a waiting thread sees at most `c(L) - 1` sections
  before its own (FIFO: every thread ahead of it takes `L` at most once),
  each followed by a free gap of fewer than `F` steps.

  THEOREMS.
  * `wartezeit_kern`: under `LaufzeitAnnahme`, `Haltezeit`, `AbschnittAktiv`
    (a lock holder can step or stands at a `locks` head), `Anwaerter`
    (the contenders), the rank invariant and lock exclusivity along the
    run: a thread at `locks L` at step `n0` takes `L` at a step
    `j < n0 + wartezeit L`, and holds `L` after it.
  * `wartezeit_schranke`: the same from the goal theorem's premises
    (`GutO`, `StufenM`, starts without signature locks, the run starting at a
    reachable machine, `KeinLogikHaltG` along the run -- a conjunct of
    `Ziel` -- and `BereichG` along the run, every float range check passes,
    from the body obligation, `bereichG_erreichbarL`) plus
    `HardwareImAbschnitt` (no named stop of any kind inside a critical
    section).
  * Machine-G facts used: `sperre_schritt` (a step at a `locks L` head takes
    `L`, and only if it is free), `schritt_sperre_art` (a step either stands
    at a `locks` head or does not grow the held set), `nimmt_an_sperre`.

  No `sorry`, no `axiom`, no `native_decide`; machine G and Spec.lean are
  unchanged.
-/

import Grammatik.Logik.Fortschritt.Lebendigkeit.T1
import Grammatik.Logik.Fortschritt.Lebendigkeit.T2
import Grammatik.Logik.Fortschritt.Lebendigkeit.T3
