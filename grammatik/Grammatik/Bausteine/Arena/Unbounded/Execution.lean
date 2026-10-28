import Grammatik.Bausteine.Arena.Unbounded.Runs

namespace Gabbro.Grammatik.ArenaStorage

open ArenaOwnership (Frame)

variable {region α : Type} {capacity : Capacity} {H H' : Heap region α}

/-- Operational steps include the provider's explicit refusal. Invalid rights
do not manufacture a memory access; their operation returns `none`. -/
inductive Step (capacity : Capacity) : Heap region α → Heap region α → Prop where
  | allocate {H H' available frame value reference} :
      H.allocate capacity available frame value = some (H', reference) → Step capacity H H'
  | refused {H available frame value} :
      H.allocate capacity available frame value = none → Step capacity H H
  | read {H frame reference value} : H.read frame reference = some value → Step capacity H H
  | write {H H' frame reference value} : H.write frame reference value = some H' → Step capacity H H'
  | release {H H' frame reference} : H.release frame reference = some H' → Step capacity H H'
  | move {H H' source target reference reference'} :
      H.move source target reference = some (H', reference') → Step capacity H H'
  | lend {H H' source target reference} :
      H.lend source target reference = some H' → Step capacity H H'
  | endLoan {H H' frame reference} : H.endLoan frame reference = some H' → Step capacity H H'
  | reset {H H' frame} : H.reset frame = some H' → Step capacity H H'

theorem Step.preserves (hv : H.Valid capacity) (hs : Step capacity H H') : H'.Valid capacity := by
  cases hs with
  | allocate he => exact (Heap.allocate_valid hv he).1
  | refused => exact hv
  | read => exact hv
  | write he => exact (Heap.write_valid hv he).1
  | release he => exact (Heap.release_valid hv he).1
  | move he => exact (Heap.move_valid hv he).1
  | lend he => exact (Heap.lend_valid hv he).1
  | endLoan he => exact Heap.endLoan_valid hv he
  | reset he => exact (Heap.reset_valid hv he).1

inductive Reachable (capacity : Capacity) : Heap region α → Prop where
  | empty : Reachable capacity .empty
  | next {H H' : Heap region α} : Reachable capacity H → Step capacity H H' → Reachable capacity H'

theorem Reachable.valid (hr : Reachable capacity H) : H.Valid capacity := by
  induction hr with
  | empty => exact Heap.empty_valid _
  | next _ hs ih => exact hs.preserves ih

theorem Allocations.reachable {frame : Frame} {value : α} {n : Nat}
    (hr : Allocations frame value n H) : Reachable .unbounded H := by
  induction hr with
  | empty => exact .empty
  | next _ he ih => exact .next ih (.allocate he)

theorem Heap.access_bounded (hv : H.Valid capacity) {frame : Frame} {reference : Ref region}
    (ha : H.rights.access frame reference.handle) :
    0 ≤ reference.handle.slot ∧ reference.handle.slot < (H.extent : Int) := by
  unfold ArenaOwnership.State.access at ha
  cases hc : H.rights.cells reference.handle.slot with
  | none => simp only [hc] at ha
  | some c => exact hv.support _ c hc

/-- Memory safety for arbitrary mixed executions of the storage component:
every successful read has live rights and a finite in-bounds backing cell. -/
theorem Reachable.read_safe (hr : Reachable capacity H) {frame : Frame} {reference : Ref region}
    {value : α} (he : H.read frame reference = some value) :
    H.rights.access frame reference.handle ∧
      0 ≤ reference.handle.slot ∧ reference.handle.slot < (H.extent : Int) :=
  ⟨Heap.read_requires_access he, Heap.access_bounded hr.valid (Heap.read_requires_access he)⟩

/-- A live grant always has a payload; access cannot silently read an absent cell. -/
theorem Heap.access_has_payload (hv : H.Valid capacity) {frame : Frame} {reference : Ref region}
    (ha : H.rights.access frame reference.handle) : ∃ value, H.read frame reference = some value := by
  have hc : (H.rights.cells reference.handle.slot).isSome = true := by
    unfold ArenaOwnership.State.access at ha
    split at ha
    · contradiction
    · rename_i c he; simp only [he, Option.isSome_some]
  have hp := hv.coherent reference.handle.slot
  rw [hc] at hp
  cases he : H.payload reference.handle.slot with
  | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hp
  | some value => exact ⟨value, by simp only [read, ha, ↓reduceIte, he]⟩

theorem Heap.write_requires_access {frame : Frame} {reference : Ref region} {value : α}
    (he : H.write frame reference value = some H') : H.rights.access frame reference.handle := by
  unfold Heap.write at he
  split at he
  · assumption
  · cases he

/-- Exclusive scoped loans also prevent a read/write race between frames. -/
theorem Heap.read_write_exclusive {f g : Frame} {r : Ref region} {x y : α}
    (hr : H.read f r = some x) (hw : H.write g r y = some H') : f = g :=
  ArenaOwnership.State.access_unique (Heap.read_requires_access hr) (Heap.write_requires_access hw)

theorem Heap.release_twice_none {frame other : Frame} {r : Ref region}
    (hv : H.Valid capacity) (he : H.release frame r = some H') : H'.release other r = none := by
  have hn : ¬ H'.rights.access other r.handle := by
    intro ha
    obtain ⟨v, hv'⟩ := Heap.access_has_payload (Heap.release_valid hv he).1 ha
    rw [(Heap.release_valid hv he).2 other] at hv'
    contradiction
  have ho : ¬ H'.rights.owns other r.handle := fun ha => hn (ArenaOwnership.State.owner_access ha)
  simp only [release, ArenaOwnership.State.release, ho, ↓reduceIte, Option.bind_eq_bind, Option.bind_none]

/-- Returning a scoped loan restores the exact original heap and owning grant. -/
theorem Heap.lend_endLoan {f g : Frame} {r : Ref region}
    (he : H.lend f g r = some H') : H'.endLoan g r = some H := by
  unfold Heap.lend at he
  cases hr : H.rights.lend f g r.handle with
  | none => simp only [hr, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at he
  | some rights =>
    simp only [hr] at he
    cases he
    have hh := ArenaOwnership.State.lend_endLoan f g r.handle hr
    simp only [Heap.endLoan]
    rw [hh]
    rfl

end Gabbro.Grammatik.ArenaStorage
