/- Typed world storage: each cell occupies its complete canonical value span.
   Logical pointer values remain distinct from checked physical layout addresses. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Layout
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik

/-- A gate bound on this machine (`Stage0/Tor/Bindung.lean`): its system-call number, the parameter each of the six
    argument registers carries (`none`: the register is not used), and the `-errno` of each case of its reason. -/
structure TorB where
  nr : Nat
  regs : List (Option Nat)
  fehler : List (Int × Nat)
  /-- The hidden argument register for the canonical result area, if declared. -/
  resultArea : Option Nat := none
  deriving DecidableEq, Repr

structure Lay (D : Deklaration) where
  /-- Code addresses, shared by function pointer words and call targets. -/
  fa : D.Fn → Nat := fun _ => 0
  /-- Extra cells supplied by an open table region; zero in static images. This is a
      representation capacity, never the source table count or an allocation guarantee. -/
  regionCells : D.Tab → Nat := fun _ => 0
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
def Lay.elem {D : Deklaration} (L : Lay D) (t : D.Tab) (f : D.Feld t) (k : Nat) : Nat := L.col t f + 8 * valueWords (D.typ t f) * k

/-- Cells represented by supplied regions, extending storage only for open tables. -/
def Lay.count {D : Deklaration} (L : Lay D) (t : D.Tab) : Int :=
  D.count t + if D.offen t then (L.regionCells t : Int) else 0

/-- Every previously represented bounded cell remains represented. -/
theorem Lay.bounded {D : Deklaration} (L : Lay D) {t : D.Tab} {k : Int}
    (h : k < D.count t) : k < L.count t := by
  unfold Lay.count
  split <;> omega

end Gabbro.Stage0.Senke
