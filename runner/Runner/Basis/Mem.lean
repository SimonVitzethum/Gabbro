/-! # The flat byte memory shared by `S0IR` and the x86-64 model

Both machines read and write the SAME memory through the SAME functions: a byte map with a read and a write
permission per byte. An access that touches a byte without the permission is a fault, and a fault ends the run on
both sides (a Linux process without a signal handler dies). Because the definitions are shared, the simulation of
the runner (`Runner/Beweis/`) relates memories by equality. -/

namespace Runner

abbrev W := BitVec 64
abbrev B := BitVec 8

structure Mem where
  b : W → B
  rd : W → Bool
  wr : W → Bool

namespace Mem

/-- Every byte of `[a, a + n)` satisfies `p`. -/
def all (p : W → Bool) (a : W) : Nat → Bool
  | 0 => true
  | n + 1 => all p a n && p (a + BitVec.ofNat 64 n)

/-- The little-endian value of the `n` bytes at `a`. -/
def le (m : Mem) (a : W) : Nat → Nat
  | 0 => 0
  | n + 1 => le m a n + (m.b (a + BitVec.ofNat 64 n)).toNat * 256 ^ n

def rd8 (m : Mem) (a : W) : Option B :=
  if m.rd a then some (m.b a) else none

def rd32 (m : Mem) (a : W) : Option (BitVec 32) :=
  if all m.rd a 4 then some (BitVec.ofNat 32 (le m a 4)) else none

def rd64 (m : Mem) (a : W) : Option W :=
  if all m.rd a 8 then some (BitVec.ofNat 64 (le m a 8)) else none

/-- Writes the low `n` bytes of `v` at `a`, little-endian; no permission check. -/
def write (m : Mem) (a : W) (n v : Nat) : Mem :=
  { m with b := fun x => if (x - a).toNat < n then BitVec.ofNat 8 (v / 256 ^ (x - a).toNat) else m.b x }

def wr64 (m : Mem) (a v : W) : Option Mem :=
  if all m.wr a 8 then some (write m a 8 v.toNat) else none

/-- Compare-and-swap of the word at `a` (a locked read-modify-write: it needs both permissions, also when the
    comparison fails). Answers the old word and the new memory. -/
def cas (m : Mem) (a e n : W) : Option (W × Mem) :=
  if all m.rd a 8 && all m.wr a 8 then
    let old := BitVec.ofNat 64 (le m a 8)
    some (old, if old = e then write m a 8 n.toNat else m)
  else none

end Mem
end Runner
