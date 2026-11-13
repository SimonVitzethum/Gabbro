module

public import Grammatik.Nebenlaeufigkeit.Async.Syntax
import Lean.Elab.Tactic.Omega

namespace Gabbro.Grammatik.Async.Executor

/-! Arithmetic and data specification of the library's owner-only ring.
    These generic facts are not a G/GX certificate for Library.gab. -/

/-- With two bounded indices, one subtraction suffices; no wrapping machine
    arithmetic is required. This is the library's exact tail calculation. -/
@[expose] public def slot {capacity : Nat} (head offset : Fin capacity) : Fin capacity :=
  ⟨if head.val + offset.val < capacity then head.val + offset.val
    else head.val + offset.val - capacity, (by
      have := head.isLt
      have := offset.isLt
      split <;> omega)⟩

public theorem slot_injective {capacity : Nat} (head : Fin capacity)
    {left right : Fin capacity} (same : slot head left = slot head right) : left = right := by
  apply Fin.ext
  have h := congrArg Fin.val same
  have := head.isLt
  have := left.isLt
  have := right.isLt
  dsimp only [slot] at h
  split at h <;> split at h <;> omega

public structure Ring (capacity : Nat) (Value : Type) where
  head : Fin capacity
  count : Nat
  bounded : count ≤ capacity
  cells : Fin capacity → Value

/-- Capacity refusal returns no replacement state: nothing is consumed. -/
@[expose] public def enqueue {capacity : Nat} (ring : Ring capacity Value) (value : Value) :
    Option (Ring capacity Value) :=
  if room : ring.count < capacity then
    some {
      head := ring.head
      count := ring.count + 1
      bounded := (by omega)
      cells := fun index => if index = slot ring.head ⟨ring.count, room⟩ then value
        else ring.cells index }
  else none

@[expose] public def nextHead {capacity : Nat} (head : Fin capacity) : Fin capacity :=
  ⟨if head.val + 1 < capacity then head.val + 1 else 0, (by
    have := head.isLt
    split <;> omega)⟩

@[expose] public def dequeue {capacity : Nat} (ring : Ring capacity Value) :
    Option (Value × Ring capacity Value) :=
  if 0 < ring.count then
    some (ring.cells ring.head,
      { head := nextHead ring.head
        count := ring.count - 1
        bounded := (by have := ring.bounded; omega)
        cells := ring.cells })
  else none

public theorem enqueue_full {capacity : Nat} (ring : Ring capacity Value) (value : Value)
    (full : ring.count = capacity) : enqueue ring value = none := by
  simp only [enqueue, full, Nat.lt_irrefl, ↓reduceDIte]

public theorem enqueue_count {capacity : Nat} (ring target : Ring capacity Value) (value : Value)
    (success : enqueue ring value = some target) : target.count = ring.count + 1 := by
  unfold enqueue at success
  split at success
  · cases success
    rfl
  · cases success

/-- A successful insertion cannot overwrite an older live queue position. -/
public theorem enqueue_preserves_older {capacity : Nat} (ring target : Ring capacity Value)
    (value : Value) (offset : Fin capacity) (older : offset.val < ring.count)
    (success : enqueue ring value = some target) :
    target.cells (slot ring.head offset) = ring.cells (slot ring.head offset) := by
  unfold enqueue at success
  split at success
  · rename_i room
    have distinct : slot ring.head offset ≠ slot ring.head ⟨ring.count, room⟩ := by
      intro equal
      have same := congrArg Fin.val (slot_injective ring.head equal)
      dsimp only at same
      omega
    cases success
    simp only [if_neg distinct]
  · cases success

public theorem dequeue_value {capacity : Nat} (ring : Ring capacity Value) (nonempty : 0 < ring.count) :
    (dequeue ring).map Prod.fst = some (ring.cells ring.head) := by
  simp only [dequeue, nonempty, ↓reduceIte, Option.map_some]

public theorem slot_wrap_zeuge : (slot (capacity := 4) ⟨3, (by decide)⟩ ⟨2, (by decide)⟩).val = 1 := rfl

@[expose] public def ringFixture : Ring 4 Nat := ⟨⟨3, (by decide)⟩, 2, (by decide), fun i => i.val + 10⟩

public theorem ring_nonempty_zeuge :
    (dequeue ringFixture).map (fun pair => (pair.1, pair.2.head.val, pair.2.count)) =
      some (13, 0, 1) := by decide

public theorem ring_enqueue_zeuge :
    (enqueue ringFixture 99).map (fun ring =>
      (ring.count, ring.cells ⟨1, (by decide)⟩, ring.cells ⟨3, (by decide)⟩)) =
      some (3, 99, 13) := by decide

end Gabbro.Grammatik.Async.Executor
