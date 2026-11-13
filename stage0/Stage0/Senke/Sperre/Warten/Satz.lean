module
public import Stage0.Senke.Sperre.Warten.Futex
public import Stage0.Senke.Sperre.Warten.Invariant
public import Stage0.Senke.Sperre.Warten.Retry
public import Stage0.Senke.Sperre.Warten.Wait
public import Stage0.Senke.Sperre.Warten.Wake
public import Stage0.Senke.Sperre.Warten.RetryProbe
public import Stage0.Senke.Sperre.Warten.WaitProbe
public import Stage0.Senke.Sperre.Warten.WakeProbe

/-! Sequential ticket-lock waiting obligations supplied here:
* `FutexArgs`, `futex_prepare`, `futex_entry`, `futex_return` describe the actual
  request block and syscall; `add_waiters` runs the emitted counter CAS loop.
* `TicketInvW` and its draw/increment/decrement/give transport lemmas state the
  thread-independent word bounds, including an explicit strict draw-width duty.
* `nimmT_cas_hit` and `nimmT_cas_miss` split the draw CAS; `nimmT_check` connects
  a successful draw to the actual serving comparison.
* `nimmT_wait_entry`, `nimmT_wait_retry`, `gibT_waiters_entry`,
  `gibT_waiters_return` and `nimmT_acquired` cover the sequential waiting paths.
* Real encoded-memory witnesses inhabit the miss, WAIT entry/return/retry,
  acquired branch and give-with-a-waiter premises jointly.

Still owed: cross-thread stability of `TicketInvW` under a rely relation
(`TicketKlasse` pins the waiter word and is too strong); a lock theorem saying
that a thread runs or is blocked at a named point under interference; and the
correspondence of a futex-blocked runner thread to the model's lock waiting.
An explicit kernel answer and resumed `LS` do not prove eventual return,
eventual acquisition, fairness, or any of those concurrent obligations.

Code corrections to the brief: index five overwrites the draw CAS result, so
slot five is ZERO on a miss at index zero; the raw observed next word exists
only between indices four and five. A draw also needs room in the strict
32-bit outstanding-ticket bound, not just the number-of-threads bound. -/
