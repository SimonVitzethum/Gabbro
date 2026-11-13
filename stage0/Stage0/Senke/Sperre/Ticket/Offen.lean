/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Offen.lean
  Subject:   What the ticket lock still owes (lock stage 2b, after the switch): the statements about the contended
              paths of the ticket code that the owner/count lock had and the ticket lock does not have yet.
-/
module
@[expose] public section


namespace Gabbro.Stage0.Senke

/-- The ticket lock is the emitted lock: `lowS` emits `locksCodeT` (`Ticket/Code.lean`), `locks_okT` (`Satz`) is the
    `locks` case of `lowS_ok`, `AgreeW.sync` answers `TicketKlasse`, `Umf` carries `TicketSync m L fp Ks H` against the
    thread's held set `H`, the mutual `lowS_ok`/`lowB_ok`/`lowEnd_ok` carry the tie `HeldIn H Λ bo`, `FunSpec.run`
    takes both, and the image starts every thread with `H = []`.

    The sequential simulation proves the uncontended paths only: a lock not in `H` is free (`HeldIn.frei`), no other
    writer runs between the instructions of one thread (`AgreeK`), and the waiters are zero (`TicketSync`). The
    statements below were proved for the owner/count lock (`nimm_contended`, `nimm_wait_entry`, `nimm_wait_retry`,
    `nimm_retry`, `nimm_retry_acquired`, `gib_waiters_entry`, `gib_waiters_return`, `futex_prepare`, `futex_entry`,
    `futex_return`, `LockInv`, with the witnesses of `ContendedProbe` and `WaitProbe`); they went with that code and are
    owed for the ticket code `nimmT`/`gibT`, each with a `_zeuge` on real encoded memory:
    - (1) **The wait of the take.** From `LS m0 m fp s a f n u w` at the check at index 10 of `nimmT` with my ticket
      `n ≠ u` (serving another ticket): the branch to the `WAIT` block at index 12; `addC` (12–18) leaves the waiters
      `w + 1`; `futexC (a + 8) 128` (19–26) builds the `futex_wait` request on the serving word with the serving ticket
      seen in slot `s + 5` and makes the call (entry and return under an explicit `FutexOK` response, no fairness);
      `addC` (27–33) leaves the waiters back at `w`; the jump at index 34 returns to `L1` (index 7). And the acquired
      case: after a release by the holder (serving = my ticket) the check at index 10 falls through to the jump at
      index 11 and on to the end (index 35) with the lock mine.
    - (2) **The retry of the ticket `cas`.** At index 4 the `cas` on the next word finds it changed (another thread took
      a ticket between index 1 and 4): the compare at index 5 gives 0 and the branch at index 6 returns to index 0;
      the following round takes the next ticket.
    - (3) **The wake of the give.** From `LS m0 m fp s a f (n + 1) n w` with waiters `w ≠ 0`: after the serving `cas`
      (0–4) the waiters are read (5–6) and the branch at index 7 falls into the `futex_wake` block 8–15
      (`futexC (a + 8) 129 0 (s + 10) (some 2147483647)`, every waiter), entry and return under `FutexOK`.
    - (4) **The stable invariant across threads.** The ticket analogue of `LockInv`, independent of the thread: at
      every stable boundary `next − serving` is the number of tickets taken and not yet served (one holder and the
      threads in `WAIT`), with the overflow of the modular counters excluded explicitly. -/
def ticketOffen : True := trivial

end Gabbro.Stage0.Senke
