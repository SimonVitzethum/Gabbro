import Grammatik.Bausteine.Arena.Unbounded.State

namespace Gabbro.Grammatik.ArenaStorage

open ArenaOwnership (Frame Handle Cell)

variable {region α : Type} {H H' : Heap region α} {capacity : Capacity}

theorem Heap.empty_valid (capacity : Capacity) : (Heap.empty : Heap region α).Valid capacity := by
  refine ⟨ArenaOwnership.State.empty_valid, ?_, ?_, .nil, ?_, ?_⟩
  · intro i c h; cases h
  · intro i; rfl
  · intro i h; cases h
  · cases capacity <;> simp only [Capacity.permits, empty, Nat.zero_le, decide_true]

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

theorem Heap.allocate_valid {available : Bool} {frame : Frame} {value : α} {r : Ref region}
    (hv : H.Valid capacity) (he : H.allocate capacity available frame value = some (H', r)) :
    H'.Valid capacity ∧ H'.rights.owns frame r.handle ∧
      r.handle.slot = (H.candidate : Int) ∧ H'.payload r.handle.slot = some value := by
  obtain ⟨_, hcap, hr, hinstall⟩ := Heap.allocate_parts he
  obtain ⟨hvalid, hown⟩ := ArenaOwnership.State.allocate_valid hv.rights frame _ hr
  obtain ⟨hempty, hlt, hmono, hnd, hfree⟩ := H.candidate_facts hv
  have heq := hr
  simp only [ArenaOwnership.State.allocate, hempty] at heq
  have hpair := Option.some.inj heq
  have hrights := (congrArg Prod.fst hpair).symm
  have hhandle := (congrArg Prod.snd hpair).symm
  have hcells := congrArg ArenaOwnership.State.cells hrights
  have hslot : r.handle.slot = (H.candidate : Int) := congrArg Handle.slot hhandle
  have hext : H'.extent = H.nextExtent := congrArg Heap.extent hinstall
  have hfrees : H'.free = H.remainingFree := congrArg Heap.free hinstall
  have hpayload : H'.payload = fun i =>
      if i = (H.candidate : Int) then some value else H.payload i := congrArg Heap.payload hinstall
  refine ⟨?_, hown, hslot, ?_⟩
  · constructor
    · exact hvalid
    · intro i c hc
      rw [hcells] at hc
      rw [hext]
      by_cases hi : i = (H.candidate : Int)
      · subst i; exact ⟨by omega, by omega⟩
      · have hh := hv.support i c (by simpa [ArenaOwnership.State.put, hi] using hc)
        exact ⟨hh.1, by omega⟩
    · intro i
      rw [hpayload, hcells]
      by_cases hi : i = (H.candidate : Int)
      · simp only [hi, ↓reduceIte, Option.isSome_some, ArenaOwnership.State.put]
      · simpa [ArenaOwnership.State.put, hi] using hv.coherent i
    · rw [hfrees]; exact hnd
    · intro i hi
      rw [hfrees] at hi
      obtain ⟨hi, hc, hne⟩ := hfree i hi
      rw [hext, hcells]
      exact ⟨hi, by simpa [ArenaOwnership.State.put, show (i : Int) ≠ H.candidate by omega] using hc⟩
    · rw [hext]; exact hcap
  · rw [hpayload, hslot]
    simp only [↓reduceIte]

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

theorem Heap.read_requires_access {frame : Frame} {r : Ref region} {value : α}
    (he : H.read frame r = some value) : H.rights.access frame r.handle := by
  unfold Heap.read at he
  split at he
  · assumption
  · cases he

/-- Two different frames cannot both access the same allocation. -/
theorem Heap.access_exclusive {f g : Frame} {r : Ref region} {x y : α}
    (hf : H.read f r = some x) (hg : H.read g r = some y) : f = g :=
  ArenaOwnership.State.access_unique (Heap.read_requires_access hf) (Heap.read_requires_access hg)

end Gabbro.Grammatik.ArenaStorage
