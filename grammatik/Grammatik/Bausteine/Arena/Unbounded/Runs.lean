import Grammatik.Bausteine.Arena.Unbounded.Lifetime

namespace Gabbro.Grammatik.ArenaStorage

open ArenaOwnership (Frame)

variable {region α : Type}

/-- Actual successful operations of this allocator, from one fixed empty region.
Availability is explicit in the constructor; it is not asserted for every provider. -/
inductive Allocations (frame : Frame) (value : α) : Nat → Heap region α → Prop where
  | empty : Allocations frame value 0 .empty
  | next {n H H' reference} : Allocations frame value n H →
      H.allocate .unbounded true frame value = some (H', reference) →
      Allocations frame value (n + 1) H'

theorem Allocations.invariant {frame : Frame} {value : α} {n : Nat} {H : Heap region α}
    (hr : Allocations frame value n H) :
    H.Valid .unbounded ∧ H.extent = n ∧ H.free = [] ∧
      (∀ i : Nat, i < n → H.payload (i : Int) = some value) := by
  induction hr with
  | empty => exact ⟨Heap.empty_valid _, rfl, rfl, by intro i hi; omega⟩
  | @next n H H' reference _ he ih =>
    obtain ⟨hv, hext, hfree, hfull⟩ := ih
    have hp := Heap.allocate_parts he
    have hx : H'.extent = n + 1 := by
      have hh := congrArg Heap.extent hp.2.2.2
      simpa [Heap.install, Heap.nextExtent, hfree, hext] using hh
    have hf : H'.free = [] := by
      have hh := congrArg Heap.free hp.2.2.2
      simpa [Heap.install, Heap.remainingFree, hfree] using hh
    refine ⟨(Heap.allocate_valid hv he).1, hx, hf, ?_⟩
    intro i hi
    have hh := congrFun (congrArg Heap.payload hp.2.2.2) (i : Int)
    by_cases hin : i = n
    · simpa [Heap.install, Heap.candidate, hfree, hext, hin] using hh
    · simpa [Heap.install, Heap.candidate, hfree, hext, show (i : Int) ≠ (n : Int) by omega,
        hfull i (by omega)] using hh

theorem Allocations.exists (frame : Frame) (value : α) (n : Nat) :
    ∃ H : Heap region α, Allocations frame value n H := by
  induction n with
  | zero => exact ⟨.empty, .empty⟩
  | succ n ih =>
    obtain ⟨H, hr⟩ := ih
    obtain ⟨H', reference, he⟩ := Heap.allocate_exists (Allocations.invariant hr).1 frame value rfl
    exact ⟨H', .next hr he⟩

/-- A single fixed policy and operation can retain more actual payload cells than
ANY proposed static bound. The declaration and the payload type do not grow. -/
theorem no_static_memory_bound (frame : Frame) (value : α) (bound : Nat) :
    ∃ H : Heap region α, Allocations frame value (bound + 1) H ∧
      bound < H.extent ∧ ∀ i : Nat, i ≤ bound → H.payload (i : Int) = some value := by
  obtain ⟨H, hr⟩ := Allocations.exists frame value (bound + 1)
  have hi := Allocations.invariant hr
  exact ⟨H, hr, by omega, fun i hi' => hi.2.2.2 i (by omega)⟩

/-- Despite that absence of a static bound, EVERY valid state has finite support. -/
theorem Heap.finite_payload_support {H : Heap region α} {capacity : Capacity}
    (hv : H.Valid capacity) (i : Int) (hi : i < 0 ∨ (H.extent : Int) ≤ i) :
    H.payload i = none := by
  cases hp : H.payload i with
  | none => rfl
  | some value =>
    have hh := hv.coherent i
    rw [hp] at hh
    cases hc : H.rights.cells i with
    | none => simp [hc] at hh
    | some c =>
      have hb := hv.support i c hc
      omega

/-- The opt-in does not remove or reinterpret the default bounded policy. -/
theorem Heap.bounded_extent {H : Heap region α} {maximum : Nat}
    (hv : H.Valid (.bounded maximum)) : H.extent ≤ maximum := by
  simpa [Capacity.permits] using hv.capacity

/-- Outcomes keep OOM separate from completing a finite allocation sequence. -/
inductive BatchResult (region α : Type) where
  | complete (heap : Heap region α) (references : List (Ref region))
  | outOfMemory (heap : Heap region α) (references : List (Ref region))

/-- A supplied finite request list always terminates, even for an always-refusing
provider. Failure returns the prefix already allocated; it never restarts forever. -/
def allocateList (capacity : Capacity) (provider : Nat → Bool) (frame : Frame) :
    Nat → Heap region α → List (Ref region) → List α → BatchResult region α
  | _, H, references, [] => .complete H references.reverse
  | request, H, references, value :: rest =>
    H.allocateThen capacity (provider request) frame value
      (fun H' reference => allocateList capacity provider frame (request + 1) H'
        (reference :: references) rest)
      (fun H => .outOfMemory H references.reverse)

def BatchResult.heap : BatchResult region α → Heap region α
  | .complete H _ | .outOfMemory H _ => H

theorem allocateList_valid (capacity : Capacity) (provider : Nat → Bool) (frame : Frame)
    (values : List α) (request : Nat) (H : Heap region α) (references : List (Ref region))
    (hv : H.Valid capacity) :
    (allocateList capacity provider frame request H references values).heap.Valid capacity := by
  induction values generalizing request H references with
  | nil => exact hv
  | cons value rest ih =>
    simp only [allocateList, Heap.allocateThen]
    cases he : H.allocate capacity (provider request) frame value with
    | none => exact hv
    | some pair =>
      exact ih (request + 1) pair.1 (pair.2 :: references) (Heap.allocate_valid hv he).1

theorem allocateList_refused (capacity : Capacity) (frame : Frame) (H : Heap region α)
    (value : α) (rest : List α) :
    allocateList capacity (fun _ => false) frame 0 H [] (value :: rest) =
      .outOfMemory H [] := by
  simp [allocateList, Heap.allocateThen, Heap.allocate_refused]

end Gabbro.Grammatik.ArenaStorage
