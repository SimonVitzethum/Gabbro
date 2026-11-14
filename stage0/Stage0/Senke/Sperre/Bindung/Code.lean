/- The execution-image wait binding. Linux alone emits OS requests. -/
module
public import Stage0.Senke.Sperre.Code
@[expose] public section

namespace Gabbro.Stage0.Senke
open Runner.IR

/-- `futex (a, op, v)` with `v` from slot `v`, the request block from `q`: 8 instructions. -/
def futexC (a op : Nat) (v q : Nat) (vConst : Option Int) : List II :=
  [ci 1 q 202 0, ci 1 ((q + 1 : Nat) : Int) a 0, ci 1 ((q + 2 : Nat) : Int) op 0,
    (match vConst with
     | some k => ci 1 ((q + 3 : Nat) : Int) k 0
     | none => ci 2 ((q + 3 : Nat) : Int) v 0),
    ci 1 ((q + 4 : Nat) : Int) 0 0, ci 1 ((q + 5 : Nat) : Int) 0 0, ci 1 ((q + 6 : Nat) : Int) 0 0,
    ci 23 ((q + 7 : Nat) : Int) q 0]

/-- Equal-width binding cells keep all ticket-code offsets independent of the
    environment. Freestanding padding is a one-instruction forward jump. -/
def bindingCell (strategy : LockWait) (hosted : II) : II :=
  match strategy with
  | .futex => hosted
  | .spin => ci 18 16 0 0

/-- The syscall block has a fixed width in both images. In a freestanding image
    every cell is a forward jump; no syscall or request number is present. -/
def waitBindingC (strategy : LockWait) (a op v q : Nat) (value : Option Int) : List II :=
  (futexC a op v q value).map (bindingCell strategy)

/-- On contention the freestanding binding returns directly to the serving read
    (index 12 to 7). A retry has a fixed instruction bound; it never registers a
    sleeper. Linux enters the existing waiter-counter CAS loop instead. -/
def waitEntry (strategy : LockWait) (a s : Nat) : II :=
  match strategy with
  | .futex => ci 1 ((s + 7 : Nat) : Int) ((a + 16 : Nat) : Int) 0
  | .spin => ci 18 (-80) 0 0

end Gabbro.Stage0.Senke
