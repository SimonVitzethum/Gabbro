/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Code.lean
  Subject:   The ticket-lock code (lock stage 2a): the three words of a lock at `a` are the next ticket, the ticket
             now served and the waiter count. `nimmT`: take a ticket by `cas` on the next word, again until it holds;
             when the serving word holds my ticket, done, else waiters + 1, `futex_wait` on the serving word,
             waiters - 1, again. `gibT`: serving + 1 by `cas` (a LOCKED store: a plain store followed by the load of
             the waiters could lose a wake-up); `futex_wake` when there are waiters. `gibTs`: the release chain of a
             scoped return (lock stage 3), and the two scoped return codes built on it (`retScopedC`,
             `retWhyScopedC`).
-/
module
public import Stage0.Senke.Sperre.Code
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Return
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

/-- The code of `locks Lk { body }` around the body's code `cb`, as `lowS` emits it: take; the body (its `leave` and
    `next` to the two stubs after the end, at `16 * 17` and
    `16 * 34` bytes from its end); give; over the stubs; the `leave` stub: give, on to the outer `leave` target
    `exL`; the `next` stub: give, on to `exN` (both from the end of this code). -/
def locksCodeT (L : Lay D) (a s : Nat) (cb : List II) (exL exN : Int) : List II :=
  nimmT L a s ++ cb ++ gibT L a s ++ [ci 18 (16 * (1 + 2 * ((gibT L a s).length + 1))) 0 0] ++
    gibT L a s ++ [ci 18 (16 + exL + 16 * ((gibT L a s).length + 1)) 0 0] ++
    gibT L a s ++ [ci 18 (16 + exN) 0 0]

theorem locksCodeT_len (L : Lay D) (a s : Nat) (cb : List II) (x y : Int) :
    (locksCodeT L a s cb x y).length = cb.length + 86 := by
  simp only [locksCodeT, List.length_append, nimmT_len, gibT_len, List.length_singleton]; omega

/-- **The release chain** of a scoped return: the give of every lock of `Ls`, in the order of `Ls` (the model's
    `List.foldl World.gibt`), scratch from slot `s`. -/
def gibTs (L : Lay D) (s : Nat) : List D.Lock → List II
  | [] => []
  | Lk :: Ls => gibT L (L.lk Lk) s ++ gibTs L s Ls

theorem gibTs_len (L : Lay D) (s : Nat) : (Ls : List D.Lock) → (gibTs L s Ls).length = 16 * Ls.length
  | [] => rfl
  | Lk :: Ls => by
    simp only [gibTs, List.length_append, gibT_len, gibTs_len L s Ls, List.length_cons]
    omega

/-- **The scoped normal return** after the result's code left it at `source`, in the model's order: the result into
    the internal slots; the ensures and owed-invariant check `ens` (it reads the world, so it runs while every scope is
    still held); the release chain of `scopes` (scratch from `retTop`, above the internal result and its status, so
    the saved value survives it); the publication and `ret`, which read only the frame. -/
def retScopedC (L : Lay D) (layout : FrameLayout) (source : Nat) (ens : List II) (scopes : List D.Lock) :
    List II :=
  copyWords (resultWords layout.result) layout.internalResult source ++ ens ++
    gibTs L (retTop layout) scopes ++ publishC layout

/-- **The scoped reason return**: the reason is a constant (no read of the world), so the release chain comes first
    (scratch from `retTop`), then the ordinary reason code. -/
def retWhyScopedC (L : Lay D) (layout : FrameLayout) (reason : Nat) (scopes : List D.Lock) : List II :=
  gibTs L (retTop layout) scopes ++ retWhyC layout reason

end Gabbro.Stage0.Senke
