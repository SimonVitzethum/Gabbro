/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Code.lean
  Subject:   The ticket-lock code (lock stage 2a): the three words of a lock at `a` are the next ticket, the ticket
             now served and the waiter count. `nimmT`: take a ticket by `cas` on the next word, again until it holds;
             when the serving word holds my ticket, done, else waiters + 1, `futex_wait` on the serving word,
             waiters - 1, again. `gibT`: serving + 1 by `cas` (a LOCKED store: a plain store followed by the load of
             the waiters could lose a wake-up); `futex_wake` when there are waiters.
-/
module
public import Stage0.Senke.Sperre.Code
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

/-- **Take the ticket lock** with words at `a`, scratch from slot `s` (to `s + 17`). -/
def nimmT (L : Lay D) (a s : Nat) : List II :=
  -- L0: my ticket: next + 1 by cas, again until it holds (7 instructions)
  [ci 1 ((s + 1 : Nat) : Int) a 0, ci 15 ((s + 2 : Nat) : Int) ((s + 1 : Nat) : Int) 0,
    ci 1 ((s + 4 : Nat) : Int) 1 0, ci 3 ((s + 3 : Nat) : Int) ((s + 2 : Nat) : Int) ((s + 4 : Nat) : Int),
    ci 22 ((s + 5 : Nat) : Int) ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int),
    ci 14 ((s + 5 : Nat) : Int) ((s + 5 : Nat) : Int) ((s + 2 : Nat) : Int),
    ci 19 ((s + 5 : Nat) : Int) (-(16 * 6)) 0] ++ -- back to L0 (index 0)
  -- L1: serving = my ticket? (5 instructions)
  [ci 1 ((s + 1 : Nat) : Int) ((a + 8 : Nat) : Int) 0, ci 15 ((s + 5 : Nat) : Int) ((s + 1 : Nat) : Int) 0,
    ci 14 ((s + 6 : Nat) : Int) ((s + 5 : Nat) : Int) ((s + 2 : Nat) : Int),
    ci 19 ((s + 6 : Nat) : Int) (16 * 2) 0, -- to WAIT (index 12)
    ci 18 (16 * 24) 0 0] ++ -- to END (index 35)
  -- WAIT: waiters + 1, futex_wait on the serving word, waiters - 1, again
  addC (a + 16) (s + 7) 1 ++ futexC (a + 8) 128 (s + 5) (s + 10) none ++ addC (a + 16) (s + 7) (-1) ++
  [ci 18 (-(16 * 27)) 0 0] -- back to L1 (index 7)

/-- **Give the ticket lock** with words at `a`, scratch from slot `s` (to `s + 17`). -/
def gibT (L : Lay D) (a s : Nat) : List II :=
  -- serving + 1 by cas; the waiters (8 instructions)
  [ci 1 ((s + 1 : Nat) : Int) ((a + 8 : Nat) : Int) 0, ci 15 ((s + 2 : Nat) : Int) ((s + 1 : Nat) : Int) 0,
    ci 1 ((s + 4 : Nat) : Int) 1 0, ci 3 ((s + 3 : Nat) : Int) ((s + 2 : Nat) : Int) ((s + 4 : Nat) : Int),
    ci 22 ((s + 5 : Nat) : Int) ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int),
    ci 1 ((s + 1 : Nat) : Int) ((a + 16 : Nat) : Int) 0, ci 15 ((s + 2 : Nat) : Int) ((s + 1 : Nat) : Int) 0,
    ci 19 ((s + 2 : Nat) : Int) (16 * 9) 0] ++ -- to END (index 16)
  futexC (a + 8) 129 0 (s + 10) (some 2147483647)

theorem nimmT_len (L : Lay D) (a s : Nat) : (nimmT L a s).length = 7 + 5 + 7 + 8 + 7 + 1 := by rfl
theorem gibT_len (L : Lay D) (a s : Nat) : (gibT L a s).length = 8 + 8 := by rfl

end Gabbro.Stage0.Senke
