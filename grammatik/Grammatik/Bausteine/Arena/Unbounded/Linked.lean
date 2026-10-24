import Grammatik.Bausteine.Arena.Unbounded.Frame

/-! Linked storage for finite-control machines. Control holds one optional region
reference, not a natural-number encoding of an entire unbounded stack. Each cell
contains one value and one reference; push really allocates and pop really frees.
All operations reuse the storage component and its existing ownership ledger. -/

namespace Gabbro.Grammatik.ArenaStorage.Linked

open ArenaOwnership (Frame)

structure Node (region α : Type) where
  value : α
  next : Option (Ref region)

abbrev Memory (region α : Type) := Heap region (Node region α)

variable {region α : Type}

def push (H : Memory region α) (available : Bool) (frame : Frame)
    (head : Option (Ref region)) (value : α) : Option (Memory region α × Ref region) :=
  H.allocate .unbounded available frame ⟨value, head⟩

/-- `some (_, _, none)` is an empty stack; `none` is invalid rights/storage.
The representation theorem excludes invalid rights on well-formed stacks. -/
def pop (H : Memory region α) (frame : Frame) (head : Option (Ref region)) :
    Option (Memory region α × Option (Ref region) × Option α) :=
  match head with
  | none => some (H, none, none)
  | some reference => do
    let node ← H.read frame reference
    let H' ← H.release frame reference
    some (H', node.next, some node.value)

def peek (H : Memory region α) (frame : Frame) (head : Option (Ref region)) : Option (Option α) :=
  match head with
  | none => some none
  | some reference => (H.read frame reference).map (fun node => some node.value)

/-- A finite chain of distinct, owned storage cells with exact payload links.
Other stacks may occupy the same heap; this judgment describes only this chain. -/
inductive Chain (H : Memory region α) (frame : Frame) :
    Option (Ref region) → List (Ref region × α) → Prop where
  | empty : Chain H frame none []
  | cell {reference value next entries} :
      H.rights.owns frame reference.handle →
      H.read frame reference = some ⟨value, next⟩ →
      Chain H frame next entries →
      (∀ entry ∈ entries, entry.1.handle.slot ≠ reference.handle.slot) →
      Chain H frame (some reference) ((reference, value) :: entries)

theorem Chain.owned {H : Memory region α} {frame : Frame} {head entries}
    (hc : Chain H frame head entries) :
    ∀ entry ∈ entries, H.rights.owns frame entry.1.handle := by
  induction hc with
  | empty => simp
  | cell ho _ _ _ ih =>
    intro entry he
    rcases List.mem_cons.mp he with rfl | he
    · exact ho
    · exact ih _ he

theorem Chain.transport {H H' : Memory region α} {frame : Frame} {head entries}
    (hc : Chain H frame head entries)
    (hf : ∀ entry ∈ entries, H'.AgreesAt H entry.1.handle.slot) : Chain H' frame head entries := by
  induction hc with
  | empty => exact .empty
  | @cell reference value next entries ho hr hc hn ih =>
    have hh := hf (reference, value) (by simp)
    refine .cell (hh.owns rfl ho) ((hh.read frame reference rfl).trans hr)
      (ih (fun entry he => hf entry (List.mem_cons_of_mem _ he))) hn

theorem push_correct {H H' : Memory region α} {frame : Frame} {head entries value available reference}
    (hv : H.Valid .unbounded) (hc : Chain H frame head entries)
    (he : push H available frame head value = some (H', reference)) :
    H'.Valid .unbounded ∧ Chain H' frame (some reference) ((reference, value) :: entries) := by
  have hp := Heap.allocate_valid hv he
  refine ⟨hp.1, .cell (next := head) hp.2.1 ?_ ?_ ?_⟩
  · simp [Heap.read, ArenaOwnership.State.owner_access hp.2.1, hp.2.2.2]
  · apply hc.transport
    intro entry he'
    exact Heap.allocate_frame he _ (Heap.owned_candidate_ne hv (hc.owned _ he'))
  · intro entry he'
    rw [hp.2.2.1]
    exact Heap.owned_candidate_ne hv (hc.owned _ he')

theorem push_refused (H : Memory region α) (frame : Frame) (head : Option (Ref region)) (value : α) :
    push H false frame head value = none := Heap.allocate_refused H _ frame _

/-- Nonempty pop returns exactly the head value and frees its cell, while the
remaining chain and unrelated allocations keep their exact grants and bytes. -/
theorem pop_correct {H : Memory region α} {frame : Frame} {reference value entries}
    (hv : H.Valid .unbounded)
    (hc : Chain H frame (some reference) ((reference, value) :: entries)) :
    ∃ H' next, pop H frame (some reference) = some (H', next, some value) ∧
      H'.Valid .unbounded ∧ Chain H' frame next entries ∧
      (∀ f, H'.read f reference = none) ∧
      (∀ i, i ≠ reference.handle.slot → H'.AgreesAt H i) := by
  cases hc with
  | @cell _ _ actualNext _ ho hr ht hn =>
    obtain ⟨H', he⟩ := Heap.release_exists ho
    refine ⟨H', actualNext, by simp [pop, hr, he], (Heap.release_valid hv he).1,
      ?_, (Heap.release_valid hv he).2, fun i hi => Heap.release_frame he i hi⟩
    exact ht.transport (fun entry hm => Heap.release_frame he _ (hn entry hm))

def Represents (H : Memory region α) (frame : Frame) (head : Option (Ref region)) (values : List α) : Prop :=
  ∃ entries, Chain H frame head entries ∧ entries.map Prod.snd = values

theorem represents_empty (frame : Frame) :
    Represents (Heap.empty : Memory region α) frame none [] := ⟨[], .empty, rfl⟩

theorem push_represents {H H' : Memory region α} {frame : Frame} {head values value available reference}
    (hv : H.Valid .unbounded) (hr : Represents H frame head values)
    (he : push H available frame head value = some (H', reference)) :
    H'.Valid .unbounded ∧ Represents H' frame (some reference) (value :: values) := by
  obtain ⟨entries, hc, hvalues⟩ := hr
  have hh := push_correct hv hc he
  exact ⟨hh.1, (reference, value) :: entries, hh.2, by simp [hvalues]⟩

theorem peek_represents {H : Memory region α} {frame : Frame} {head values}
    (hr : Represents H frame head values) : peek H frame head = some values.head? := by
  obtain ⟨entries, hc, rfl⟩ := hr
  cases hc with
  | empty => rfl
  | cell _ hr _ _ => simp [peek, hr]

theorem pop_represents {H : Memory region α} {frame : Frame} {head values}
    (hv : H.Valid .unbounded) (hr : Represents H frame head values) :
    ∃ H' head', pop H frame head = some (H', head', values.head?) ∧
      H'.Valid .unbounded ∧ Represents H' frame head' values.tail := by
  obtain ⟨entries, hc, rfl⟩ := hr
  cases hc with
  | empty => exact ⟨H, none, rfl, hv, [], .empty, rfl⟩
  | @cell reference value next entries ho hread hc hn =>
    have hchain := Chain.cell ho hread hc hn
    obtain ⟨H', head', hpop, hv', hc', _, _⟩ := pop_correct hv hchain
    exact ⟨H', head', hpop, hv', entries, hc', rfl⟩

/-- Finite observation reads actual linked cells and never assumes a list oracle. -/
def readAll (H : Memory region α) (frame : Frame) :
    Nat → Option (Ref region) → Option (List α)
  | _, none => some []
  | 0, some _ => none
  | fuel + 1, some reference => do
    let node ← H.read frame reference
    let rest ← readAll H frame fuel node.next
    some (node.value :: rest)

theorem Chain.readAll {H : Memory region α} {frame : Frame} {head entries}
    (hc : Chain H frame head entries) (fuel : Nat) (hbound : entries.length ≤ fuel) :
    readAll H frame fuel head = some (entries.map Prod.snd) := by
  induction hc generalizing fuel with
  | empty => cases fuel <;> rfl
  | cell _ hr _ _ ih =>
    cases fuel with
    | zero => simp at hbound
    | succ fuel =>
      simp [Linked.readAll, hr, ih fuel (by simpa using hbound)]

end Gabbro.Grammatik.ArenaStorage.Linked
