/-
  File:      Arm/Mem/Event.lean
  Subject:   Events, finite relations and candidate executions of the Arm multicore model.
             FROZEN vocabulary shared by the memory-model agents (06-10): do not rename or
             remove anything; extend only through your own files.
-/
import Arm.Basic

namespace Arm

/-- What one event does. -/
inductive EvKind where
  | read (a : Access)
  | write (a : Access)
  | barrier (b : Barrier)
  deriving DecidableEq, Repr

/-- One event of a candidate execution. `id` is unique inside one `Exec`. -/
structure Ev where
  id   : Nat
  core : CoreId
  kind : EvKind
  val  : Nat        -- value read or written; 0 for barriers
  deriving DecidableEq, Repr

/-- Finite relation on event ids. Lists keep every litmus test decidable. -/
abbrev Rel := List (Nat × Nat)

def Rel.comp (r s : Rel) : Rel :=
  r.flatMap fun p => (s.filter fun q => q.1 == p.2).map fun q => (p.1, q.2)

def Rel.inv (r : Rel) : Rel := r.map fun p => (p.2, p.1)

def Rel.dedup (r : Rel) : Rel := r.eraseDups

/-- Transitive closure by `fuel` rounds; `fuel >= number of events` is complete. -/
def Rel.tc (r : Rel) : Nat → Rel
  | 0 => r.dedup
  | n + 1 => ((r.tc n) ++ (r.tc n).comp r).dedup

/-- Acyclic for an execution of `n` events. -/
def Rel.acyclic (r : Rel) (n : Nat) : Bool := !((r.tc n).any fun p => p.1 == p.2)

/-- A candidate execution: events plus the relations every Arm axiom is stated over. -/
structure Exec where
  evs  : List Ev
  po   : Rel   -- program order, per core, TRANSITIVELY closed
  addr : Rel   -- address dependency (read to access)
  data : Rel   -- data dependency (read to write)
  ctrl : Rel   -- control dependency (read to every po-later event)
  rf   : Rel   -- reads-from: write id to read id
  co   : Rel   -- coherence order: per location, TRANSITIVELY closed
  rmw  : Rel   -- read id to write id of one exclusive or atomic pair
  deriving Repr

def Exec.size (x : Exec) : Nat := x.evs.length

def Exec.ev? (x : Exec) (i : Nat) : Option Ev := x.evs.find? fun e => e.id == i

end Arm

/-
CUTS: vocabulary only; no axiom, no theorem. Well-formedness of `Exec` is NOT stated here
(agent 06 owns `Arm/Mem/Exec.lean`).
-/
