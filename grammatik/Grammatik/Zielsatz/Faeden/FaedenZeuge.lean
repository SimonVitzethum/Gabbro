/-
  File:      Grammatik/Zielsatz/FaedenZeuge.lean -- the witnesses of the 2026-09-26 diff
             (threads created at run time; Opus agent A, OFFEN O21/O22).

  NON-DEGENERATE RUNS, memory-changing and multi-step, on the thread machine:
  * §2 `sj_lauf` -- a `start` spawns TWO threads, BOTH step (each writes the table) and
    finish, the starter waits for them while it holds nothing (`JoinWartet` in between,
    `sj_wartet_dazwischen`), the join fires only once both are finished, and the starter then
    takes two steps of its own (a call and a write) -- `sj_nicht_degeneriert`.
  * §3 `kw2_lauf` -- a `child` is spawned by a live parent and runs CONCURRENTLY with it: parent
    call, child write, parent write, and the parent never waits (`kw2_nicht_degeneriert`).
  * §4 `spawn_start_ziel`, `spawn_kind_ziel` -- THE GOAL ON SPAWN RUNS of an ACCEPTED unit:
    probe B's pool routine `haupt` (lock-guarded writer, ZielOrtZeuge.lean) as a run-time root
    (`gestartet`). The concrete checker accepts the units, (b)-(d) hold, and on a run in which
    the idle root starts two `haupt` threads (resp. a live `haupt` spawns a `haupt` child) and
    the spawned threads step and take the lock, `gabbro_ziel` gives every leg of `ZielF`.
  REFUSALS:
  * §5 `start_nicht_poolsicher_abgelehnt` -- a `start` of a root that writes a table unguarded
    (`hauptB` of the two-thread fixture) is refused by the checker Bool, at the pool component
    (the model side of `N462`); the same routine as an ordinary declared start is accepted.
  * §5 `kind_unter_sperre_abgelehnt` -- a `child` region inside `locks L` lifts to a root that
    needs `L` at entry (`wrap` of probe B, which holds the lock by signature); the Bool refuses
    it at the root component (`wurzelnB`, the model side of `N456`).
  * §5 `start_unter_sperre_kein_schritt` -- the model side of `N461`: no step makes a thread
    that holds a lock a joining starter; instantiated on probe B's run where thread 0 holds the
    lock (`start_unter_sperre_zeuge`).
-/
module

public import Grammatik.Zielsatz.Faeden.FaedenZeuge.Teil1
public import Grammatik.Zielsatz.Faeden.FaedenZeuge.Teil2
