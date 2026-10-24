import Grammatik.Bausteine.Arena.Unbounded.Linked
import Mathlib.Computability.TuringMachine.Computable

/-! Executable region-reference storage for Mathlib TM2. Each stack has a
distinct region brand and uses the same linked-cell allocator. The interpreter
contains no unbounded natural/list value encoding a stack in its finite control.
This is a storage backend, not yet a compiler to G's admitted source constructs. -/

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.TM2Heap

open ArenaStorage
open ArenaOwnership (Frame)

inductive Region {K : Type} (k : K) where | storage

structure OneStack (region α : Type) where
  memory : Linked.Memory region α
  head : Option (Ref region)

structure Store {K : Type} (Γ : K → Type) where
  regions : ∀ k, OneStack (Region k) (Γ k)

variable {K : Type} {Γ : K → Type} [DecidableEq K]

def Store.empty : Store Γ := ⟨fun _ => ⟨.empty, none⟩⟩

def Store.put (S : Store Γ) (k : K) (stack : OneStack (Region k) (Γ k)) : Store Γ :=
  ⟨Function.update S.regions k stack⟩

def Store.Represents (S : Store Γ) (frame : Frame) (values : ∀ k, List (Γ k)) : Prop :=
  ∀ k, (S.regions k).memory.Valid .unbounded ∧
    Linked.Represents (S.regions k).memory frame (S.regions k).head (values k)

omit [DecidableEq K] in
theorem Store.empty_represents (frame : Frame) : (Store.empty : Store Γ).Represents frame (fun _ => []) :=
  fun _ => ⟨Heap.empty_valid _, Linked.represents_empty _⟩

def Store.push (S : Store Γ) (available : Bool) (frame : Frame) (k : K) (value : Γ k) : Option (Store Γ) := do
  let (memory, reference) ← Linked.push (S.regions k).memory available frame (S.regions k).head value
  some (S.put k ⟨memory, some reference⟩)

def Store.peek (S : Store Γ) (frame : Frame) (k : K) : Option (Option (Γ k)) :=
  Linked.peek (S.regions k).memory frame (S.regions k).head

def Store.pop (S : Store Γ) (frame : Frame) (k : K) : Option (Store Γ × Option (Γ k)) := do
  let (memory, head, value) ← Linked.pop (S.regions k).memory frame (S.regions k).head
  some (S.put k ⟨memory, head⟩, value)

theorem Store.put_represents {S : Store Γ} {frame : Frame} {values : ∀ k, List (Γ k)}
    (hr : S.Represents frame values) (k : K) (stack : OneStack (Region k) (Γ k)) (xs : List (Γ k))
    (hv : stack.memory.Valid .unbounded) (hc : Linked.Represents stack.memory frame stack.head xs) :
    (S.put k stack).Represents frame (Function.update values k xs) := by
  intro j
  by_cases hj : j = k
  · subst j
    simpa [Store.put] using And.intro hv hc
  · simpa [Store.put, Function.update_of_ne hj] using hr j

theorem Store.push_correct {S : Store Γ} {frame : Frame} {values : ∀ k, List (Γ k)}
    (hr : S.Represents frame values) (k : K) (value : Γ k) :
    ∃ S', S.push true frame k value = some S' ∧
      S'.Represents frame (Function.update values k (value :: values k)) := by
  obtain ⟨memory, reference, he⟩ := Heap.allocate_exists (hr k).1 frame
    (Linked.Node.mk value (S.regions k).head) rfl
  have hh := Linked.push_represents (hr k).1 (hr k).2 he
  exact ⟨S.put k ⟨memory, some reference⟩, by simp [Store.push, Linked.push, he],
    Store.put_represents hr k _ _ hh.1 hh.2⟩

theorem Store.push_spec {S S' : Store Γ} {frame : Frame} {values : ∀ k, List (Γ k)} {available : Bool}
    (hr : S.Represents frame values) (k : K) (value : Γ k)
    (he : S.push available frame k value = some S') :
    S'.Represents frame (Function.update values k (value :: values k)) := by
  unfold Store.push at he
  cases hp : Linked.push (S.regions k).memory available frame (S.regions k).head value with
  | none => simp [hp] at he
  | some pair =>
    rcases pair with ⟨memory, reference⟩
    simp only [hp] at he
    cases he
    have hh := Linked.push_represents (hr k).1 (hr k).2 hp
    exact Store.put_represents hr k _ _ hh.1 hh.2

omit [DecidableEq K] in
theorem Store.peek_correct {S : Store Γ} {frame : Frame} {values : ∀ k, List (Γ k)}
    (hr : S.Represents frame values) (k : K) : S.peek frame k = some (values k).head? :=
  Linked.peek_represents (hr k).2

theorem Store.pop_correct {S : Store Γ} {frame : Frame} {values : ∀ k, List (Γ k)}
    (hr : S.Represents frame values) (k : K) :
    ∃ S', S.pop frame k = some (S', (values k).head?) ∧
      S'.Represents frame (Function.update values k (values k).tail) := by
  obtain ⟨memory, head, he, hv, hc⟩ := Linked.pop_represents (hr k).1 (hr k).2
  exact ⟨S.put k ⟨memory, head⟩, by simp [Store.pop, he], Store.put_represents hr k _ _ hv hc⟩

end Gabbro.Grammatik.Berechenbarkeit.Storage.TM2Heap
