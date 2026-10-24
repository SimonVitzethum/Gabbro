import Grammatik.Bausteine.Arena.Ownership.State

/-!
Opt-in storage without a declaration-time element ceiling. `extent` bounds the
finite support of ONE state, not a whole execution. Bounded and unbounded regions
share allocation, release, ownership grants and scoped loans. Provider refusal is
an ordinary result at EVERY allocation, including reuse; no availability axiom is
introduced. This is the storage component, not yet a new admitted G construct.
-/

namespace Gabbro.Grammatik.ArenaStorage

open ArenaOwnership (Frame Handle Cell)

/-- Absence of a ceiling is explicit; existing bounded declarations retain a bound. -/
inductive Capacity where
  | bounded (maximum : Nat)
  | unbounded
  deriving DecidableEq, Repr

def Capacity.permits : Capacity → Nat → Bool
  | .bounded maximum, n => decide (n ≤ maximum)
  | .unbounded, _ => true

/-- Region-branded reference. There is deliberately no public integer constructor. -/
structure Ref (region : Type) where
  private mk ::
  handle : Handle
  deriving DecidableEq, Repr

/-- Payload type and region identity cannot be changed by an access operation. -/
structure Heap (region : Type) (α : Type) where
  extent : Nat
  free : List Nat
  rights : ArenaOwnership.State
  payload : Int → Option α

def Heap.empty : Heap region α := ⟨0, [], .empty, fun _ => none⟩

/-- Finite support, exact payload/rights agreement, and a disjoint LIFO free list. -/
structure Heap.Valid (H : Heap region α) (capacity : Capacity) : Prop where
  rights : H.rights.valid
  support : ∀ i c, H.rights.cells i = some c → 0 ≤ i ∧ i < (H.extent : Int)
  coherent : ∀ i, (H.payload i).isSome = (H.rights.cells i).isSome
  free_nodup : H.free.Nodup
  free_empty : ∀ i ∈ H.free, i < H.extent ∧ H.rights.cells (i : Int) = none
  capacity : capacity.permits H.extent = true

def Heap.put (H : Heap region α) (i : Int) (v : Option α) : Heap region α :=
  { H with payload := fun j => if j = i then v else H.payload j }

def Heap.candidate (H : Heap region α) : Nat := H.free.headD H.extent

def Heap.nextExtent (H : Heap region α) : Nat :=
  if H.free.isEmpty then H.extent + 1 else H.extent

def Heap.remainingFree (H : Heap region α) : List Nat := H.free.tail

def Heap.install (H : Heap region α) (rights : ArenaOwnership.State) (value : α) : Heap region α :=
  ⟨H.nextExtent, H.remainingFree, rights,
    fun i => if i = (H.candidate : Int) then some value else H.payload i⟩

/-- `available` is the fallible provider's answer, not a hardware assumption.
The same refusal path applies to a fresh slot and a reused slot. -/
def Heap.allocate (H : Heap region α) (capacity : Capacity) (available : Bool)
    (frame : Frame) (value : α) : Option (Heap region α × Ref region) := do
  if available && capacity.permits H.nextExtent then do
    let (rights, handle) ← H.rights.allocate frame (H.candidate : Int)
    some (H.install rights value, ⟨handle⟩)
  else none

/-- Both continuations are explicit: no allocation operation silently traps on OOM. -/
def Heap.allocateThen (H : Heap region α) (capacity : Capacity) (available : Bool)
    (frame : Frame) (value : α)
    (success : Heap region α → Ref region → β) (failure : Heap region α → β) : β :=
  match H.allocate capacity available frame value with
  | none => failure H
  | some (H', reference) => success H' reference

def Heap.read (H : Heap region α) (frame : Frame) (reference : Ref region) : Option α :=
  if H.rights.access frame reference.handle then H.payload reference.handle.slot else none

def Heap.write (H : Heap region α) (frame : Frame) (reference : Ref region) (value : α) :
    Option (Heap region α) :=
  if H.rights.access frame reference.handle then some (H.put reference.handle.slot (some value))
  else none

def Heap.release (H : Heap region α) (frame : Frame) (reference : Ref region) :
    Option (Heap region α) := do
  let rights ← H.rights.release frame reference.handle
  some { (H.put reference.handle.slot none) with
    rights := rights
    free := reference.handle.slot.toNat :: H.free }

def Heap.move (H : Heap region α) (source target : Frame) (reference : Ref region) :
    Option (Heap region α × Ref region) := do
  let (rights, handle) ← H.rights.move source target reference.handle
  some ({ H with rights := rights }, ⟨handle⟩)

def Heap.lend (H : Heap region α) (source target : Frame) (reference : Ref region) :
    Option (Heap region α) := do
  let rights ← H.rights.lend source target reference.handle
  some { H with rights := rights }

def Heap.endLoan (H : Heap region α) (frame : Frame) (reference : Ref region) :
    Option (Heap region α) := do
  let rights ← H.rights.endLoan frame reference.handle
  some { H with rights := rights }

/-- A finite executable reset check, including owners in suspended frames. -/
def Heap.canReset (H : Heap region α) (frame : Frame) : Bool :=
  (List.range H.extent).all fun i =>
    match H.rights.cells (i : Int) with
    | none => true
    | some c => decide (c.owner = frame ∧ c.loans = [])

def Heap.reset (H : Heap region α) (frame : Frame) : Option (Heap region α) :=
  if H.canReset frame then
    some ⟨0, [], H.rights.reset, fun _ => none⟩
  else none

end Gabbro.Grammatik.ArenaStorage
