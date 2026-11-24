/-
  File:      core/Core/Ast/Semantik/Runtime/Speicherplan/Zelle.lean
  Subject:   THE MEMORY OF A UNIT (MK-02). A location of the shared memory is a cell of a region (memory
             comes from outside as a region, never from a number), the word of a lock, or the one location of
             the outside events; a lock is its number in the plan; an address space is its number. These are the
             types of the unit's machine states, so that the forms read and write shared memory over the memory
             of M3 and the locks of M4 instead of a one-point location type. The three kinds of location are
             distinct constructors: a program cell can never alias a lock word or an outside event.
-/
module

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- **A location of the shared memory.** `region slot offset` is the cell at `offset` of the region
    with the object number `slot`; `sperre l` is the word of the lock `l`, which the lock protocol
    reads and writes; `aussen` is the location the catalogue events are recorded at. -/
inductive Zelle where
  | region (slot offset : Nat)
  | sperre (l : Nat)
  | aussen
  deriving DecidableEq, Repr

/-- The object number of a location for the authority check: the region slot of a region cell; a lock
    word and the event location belong to no region. -/
def Zelle.objekt : Zelle → Nat
  | .region slot _offset => slot
  | .sperre _lock => 0
  | .aussen => 0

/-- **The memory plan of a unit**: the number of its locks, the number of its address spaces and the
    initial content of the cells of the regions it is granted. A unit that declares nothing has the
    empty plan: no lock, no address space, every cell `0`. -/
structure Speicherplan where
  sperren : Nat
  raeume : Nat
  anfang : Nat → Nat → Int

/-- The plan of a unit that declares no lock, no address space and no initial content. -/
def Speicherplan.leer : Speicherplan := ⟨0, 0, fun _ _ => 0⟩

/-- Two plans side by side: the locks and spaces of the second are numbered behind those of the first;
    the initial content of the first wins. -/
def Speicherplan.anhaengen (a b : Speicherplan) : Speicherplan :=
  ⟨a.sperren + b.sperren, a.raeume + b.raeume, a.anfang⟩

namespace Speicherplan

/-- The initial content of a cell: the declared content of a region cell, `0` for every other
    location (a lock word starts free, the event location holds no event). -/
def initial (p : Speicherplan) : Zelle → Int
  | .region slot offset => p.anfang slot offset
  | .sperre _ => 0
  | .aussen => 0

/-- **The three kinds of location never alias.** -/
theorem zelle_arten_verschieden (slot offset l : Nat) :
    Zelle.region slot offset ≠ Zelle.sperre l ∧ Zelle.region slot offset ≠ Zelle.aussen ∧
      Zelle.sperre l ≠ Zelle.aussen :=
  ⟨fun same => Zelle.noConfusion same, fun same => Zelle.noConfusion same,
    fun same => Zelle.noConfusion same⟩

end Speicherplan

end Gabbro.Core.Ast.Semantik
