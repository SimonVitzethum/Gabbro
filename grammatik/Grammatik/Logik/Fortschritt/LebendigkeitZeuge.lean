/-
  File:      Grammatik/LebendigkeitZeuge.lean
  Subject:   THE WITNESS for the waiting bound (`Lebendigkeit.lean`) on the
             two-thread fixture `mP` (MehrfadenZeuge.lean): a concrete
             scheduled run on which EVERY premise of `wartezeit_schranke`
             holds, with a concrete bound, and a thread that really waits.

  The run (`lLauf`, 23 steps of machine G, then stutters):
    steps 0-2   thread 0: `privA[0] = 7`, `privA[1] = 7`, unfold `locks`
    steps 3-4   thread 1: `privB[0] = 5`, unfold `locks`
    step  5     thread 0 takes the lock; thread 1 stands at `locks` from step 5
    steps 6-11  thread 0 holds it: call `setze(30)`, two writes, return,
                close, release (6 own steps while holding)
    steps 12-14 thread 0: close, call `pruefeA`, return -- finished
    step  15    thread 1 takes the lock (waited 10 scheduler steps)
    steps 16-22 thread 1: its critical section, then finished
    from 23     every thread is finished; the machine stutters.

  The constants: `F = 4` (fairness window), `h = 6` (own steps per critical
  section), `k = 0` (no nested lock), contenders `[0, 1]`. The bound:
  `wartezeit = (2 - 1) * (6 * 4 + 0 + 4) + 4 = 32` (`lW_eq`). Thread 1,
  standing at `locks` at step 5, takes the lock at step 15 < 5 + 32
  (`wartezeit_zeuge`), and the theorem itself says so (`lSchranke`).
-/
module

public import Grammatik.Logik.Fortschritt.LebendigkeitZeuge.Teil1
public import Grammatik.Logik.Fortschritt.LebendigkeitZeuge.Teil2
public import Grammatik.Logik.Fortschritt.LebendigkeitZeuge.Teil3
