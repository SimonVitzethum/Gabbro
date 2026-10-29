/-
  File:      stage0/Stage0/Senke/Welt/Lay.lean
  Subject:   Where the world lies in memory: every column of a table (field `f` of table `t`, its elements one after the
             other from `col t f`) and every global (`ga g`, one word); how each gate is bound (`tor`); where the threads' stacks
             lie (`sb`, `st`) and the words of each lock (`lk`).

  Every element of every column is one word, also in a column of bytes: a system call's buffer is packed into
  bytes at the call (`PLAN-SELF-HOSTING.md` §2.1.4), so every cell of the world is one aligned word. All of it lies
  in `[lo, hi)`.
-/
import Grammatik.Kern.Semantik.Semantik

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik

/-- A gate bound on this machine (`Stage0/Tor/Bindung.lean`): its system-call number, the parameter each of the six
    argument registers carries (`none`: the register is not used), and the `-errno` of each case of its reason. -/
structure TorB where
  nr : Nat
  regs : List (Option Nat)
  fehler : List (Int × Nat)
  deriving DecidableEq, Repr

structure Lay (D : Deklaration) where
  /-- Code addresses, shared by function pointer words and call targets. -/
  fa : D.Fn → Nat := fun _ => 0
  col : (t : D.Tab) → D.Feld t → Nat
  ga : D.Glob → Nat
  lo : Nat
  hi : Nat
  /-- The binding of each gate, if it has one on this machine. -/
  tor : D.Ax → Option TorB
  /-- The field of a table a gate's buffer carries: its bytes, one per element. -/
  byte : (t : D.Tab) → Option (D.Feld t)
  /-- The first thread's stack (its first byte), and the bytes of one stack: thread `j` has the `j`-th. -/
  sb : Nat := 0
  st : Nat := 1
  /-- The three words of a lock (owner, count, waiters) from this address, above the world, below `sye`. -/
  lk : D.Lock → Nat := fun _ => 0
  sye : Nat := 0

/-- The words of every lock lie between the world's end and `sye`, three words each, apart from each other. -/
def LaySync {D : Deklaration} (L : Lay D) : Prop :=
  (∀ Lk, L.hi ≤ L.lk Lk ∧ L.lk Lk + 24 ≤ L.sye) ∧
    ∀ Lk Lk', Lk ≠ Lk' → L.lk Lk + 24 ≤ L.lk Lk' ∨ L.lk Lk' + 24 ≤ L.lk Lk

/-- The address of element `k` of the column `f` of table `t`. -/
def Lay.elem {D : Deklaration} (L : Lay D) (t : D.Tab) (f : D.Feld t) (k : Nat) : Nat := L.col t f + 8 * k

end Gabbro.Stage0.Senke
