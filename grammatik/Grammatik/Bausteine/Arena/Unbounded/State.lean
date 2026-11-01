module
public import Grammatik.Bausteine.Arena.Ownership.State
@[expose] public section


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

@[no_expose] instance : DecidableEq (Ref region)
  | ⟨a⟩, ⟨b⟩ => if h : a = b then isTrue (by subst h; rfl) else isFalse (fun e => h (by cases e; rfl))

@[no_expose] instance : Repr (Ref region) := ⟨fun r n => reprPrec r.handle n⟩


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
@[no_expose] def Heap.allocate (H : Heap region α) (capacity : Capacity) (available : Bool)
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

@[no_expose] def Heap.move (H : Heap region α) (source target : Frame) (reference : Ref region) :
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

section Facts

variable {region α : Type} {H H' : Heap region α} {capacity : Capacity}

-- The allocator facts live beside the non-exposed `Heap.allocate` (its private `Ref.mk` keeps the body hidden).

theorem Heap.candidate_facts (hv : H.Valid capacity) :
    H.rights.cells (H.candidate : Int) = none ∧ H.candidate < H.nextExtent ∧
      H.extent ≤ H.nextExtent ∧ H.remainingFree.Nodup ∧
      (∀ i ∈ H.remainingFree, i < H.nextExtent ∧ H.rights.cells (i : Int) = none ∧
        i ≠ H.candidate) := by
  cases hf : H.free with
  | nil =>
    have he : H.rights.cells (H.extent : Int) = none := by
      cases hc : H.rights.cells (H.extent : Int) with
      | none => rfl
      | some c => have hh := hv.support _ _ hc; omega
    simpa [Heap.candidate, Heap.nextExtent, Heap.remainingFree, hf] using he
  | cons i rest =>
    have hi := hv.free_empty i (by simp only [hf, List.mem_cons, true_or])
    have hn := List.nodup_cons.mp (hf ▸ hv.free_nodup)
    refine ⟨by simpa [Heap.candidate, hf] using hi.2,
      by simpa [Heap.candidate, Heap.nextExtent, hf] using hi.1,
      by simp only [nextExtent, hf, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, Std.le_refl], by simpa [Heap.remainingFree, hf] using hn.2, ?_⟩
    intro j hj
    have hj' : j ∈ rest := by simpa [Heap.remainingFree, hf] using hj
    have hh := hv.free_empty j (by simp only [hf, List.mem_cons, hj', or_true])
    exact ⟨by simpa [Heap.nextExtent, hf] using hh.1, hh.2,
      by simpa [Heap.candidate, hf] using fun e : j = i => hn.1 (e ▸ hj')⟩

/-- Exact decomposition of an allocator answer, retaining its original grant. -/
theorem Heap.allocate_parts {available : Bool} {frame : Frame} {value : α} {r : Ref region}
    (he : H.allocate capacity available frame value = some (H', r)) :
    available = true ∧ capacity.permits H.nextExtent = true ∧
      H.rights.allocate frame (H.candidate : Int) = some (H'.rights, r.handle) ∧
      H' = H.install H'.rights value := by
  unfold Heap.allocate at he
  split at he
  · rename_i hg
    have hg' : available = true ∧ capacity.permits H.nextExtent = true := by
      simpa only [Bool.and_eq_true] using hg
    cases hr : H.rights.allocate frame (H.candidate : Int) with
    | none => simp only [hr, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at he
    | some pair =>
      rcases pair with ⟨rights, handle⟩
      simp only [hr] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨hg'.1, hg'.2, rfl, rfl⟩
  · cases he

theorem Heap.allocate_exists (hv : H.Valid capacity) (frame : Frame) (value : α)
    (hc : capacity.permits H.nextExtent = true) :
    ∃ H' r, H.allocate capacity true frame value = some (H', r) := by
  have hf := (H.candidate_facts hv).1
  simp only [allocate, hc, Bool.and_self, ↓reduceIte, ArenaOwnership.State.allocate, hf, Option.bind_eq_bind,
  Option.bind_some, Option.some.injEq, Prod.mk.injEq, exists_and_left, exists_eq', and_true]

theorem Heap.allocate_refused (H : Heap region α) (capacity : Capacity) (frame : Frame) (value : α) :
    H.allocate capacity false frame value = none := by simp only [allocate, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- Under the invariant there are precisely provider refusal and capacity exhaustion. -/
theorem Heap.allocate_none_iff (hv : H.Valid capacity) (available : Bool)
    (frame : Frame) (value : α) :
    H.allocate capacity available frame value = none ↔
      available = false ∨ capacity.permits H.nextExtent = false := by
  cases ha : available <;> cases hc : capacity.permits H.nextExtent <;>
    simp only [allocate, hc, Bool.and_self, Bool.false_eq_true, ↓reduceIte, or_self, Bool.and_true, Bool.true_eq_false, or_false, Bool.and_false, or_true, ArenaOwnership.State.allocate, (H.candidate_facts hv).1, Option.bind_eq_bind, Option.bind_some, reduceCtorEq]


/-- Exact decomposition of a successful move (the body of `Heap.move` stays hidden with its private `Ref.mk`). -/
theorem Heap.move_parts {f g : Frame} {r r' : Ref region}
    (he : H.move f g r = some (H', r')) :
    ∃ rights, H.rights.move f g r.handle = some (rights, r'.handle) ∧ H' = { H with rights := rights } := by
  unfold Heap.move at he
  cases hr : H.rights.move f g r.handle with
  | none => simp only [hr, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at he
  | some pair =>
    rcases pair with ⟨rights, handle⟩
    simp only [hr] at he
    cases he
    exact ⟨rights, rfl, rfl⟩

end Facts

end Gabbro.Grammatik.ArenaStorage
