/-
  File:      Arm/Isa/Monad.lean
  Subject:   The effect interface of one sequential Arm instruction: the same calls the Sail Arm
             model makes (register reads and writes, memory accesses with their ordering,
             barriers, exceptions), as a free monad. FROZEN vocabulary shared by the
             instruction agents (11-15): do not rename or remove anything.
  Sail:      sail-arm/arm-v9.4-a/src/interface.sail and mem.sail (memory accessors),
             sail/lib/concurrency_interface (the events a multicore model consumes).
-/
import Arm.Basic

namespace Arm

/-- Exceptions an instruction can raise (a coarse tag; the system agent refines it). -/
inductive Exc where
  | undefined
  | svc (imm : BitVec 16)
  | dataAbort (addr : Addr)
  | alignment (addr : Addr)
  | pcAlignment
  | other (code : Nat)
  deriving DecidableEq, Repr

/-- One sequential instruction as a tree of effects ending in a result. -/
inductive Eff (α : Type) where
  | ret    : α → Eff α
  | rdX    : Nat → (BitVec 64 → Eff α) → Eff α
  | wrX    : Nat → BitVec 64 → Eff α → Eff α
  | rdV    : Nat → (BitVec 128 → Eff α) → Eff α
  | wrV    : Nat → BitVec 128 → Eff α → Eff α
  | rdPC   : (BitVec 64 → Eff α) → Eff α
  | wrPC   : BitVec 64 → Eff α → Eff α
  | rdNZCV : (BitVec 4 → Eff α) → Eff α
  | wrNZCV : BitVec 4 → Eff α → Eff α
  | rdSys  : String → (BitVec 64 → Eff α) → Eff α
  | wrSys  : String → BitVec 64 → Eff α → Eff α
  | rdMem  : Access → (Nat → Eff α) → Eff α
  | wrMem  : Access → Nat → Eff α → Eff α
  | bar    : Barrier → Eff α → Eff α
  | raise  : Exc → Eff α

def Eff.bind {α β : Type} : Eff α → (α → Eff β) → Eff β
  | .ret a,       f => f a
  | .rdX n k,     f => .rdX n fun v => (k v).bind f
  | .wrX n v k,   f => .wrX n v (k.bind f)
  | .rdV n k,     f => .rdV n fun v => (k v).bind f
  | .wrV n v k,   f => .wrV n v (k.bind f)
  | .rdPC k,      f => .rdPC fun v => (k v).bind f
  | .wrPC v k,    f => .wrPC v (k.bind f)
  | .rdNZCV k,    f => .rdNZCV fun v => (k v).bind f
  | .wrNZCV v k,  f => .wrNZCV v (k.bind f)
  | .rdSys s k,   f => .rdSys s fun v => (k v).bind f
  | .wrSys s v k, f => .wrSys s v (k.bind f)
  | .rdMem a k,   f => .rdMem a fun v => (k v).bind f
  | .wrMem a v k, f => .wrMem a v (k.bind f)
  | .bar b k,     f => .bar b (k.bind f)
  | .raise e,     _ => .raise e

instance : Monad Eff where
  pure := .ret
  bind := Eff.bind

end Arm

/-
CUTS: vocabulary only. The monad laws are NOT proved. The register file is deliberately coarse
(X0-X30, V0-V31, PC, NZCV, named system registers); finer state is added by the instruction
agents through `rdSys`/`wrSys` names taken from the Sail source.
-/
