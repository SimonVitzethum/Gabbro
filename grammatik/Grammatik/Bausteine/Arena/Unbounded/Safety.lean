module
public import Grammatik.Bausteine.Arena.Unbounded.State
@[expose] public section


namespace Gabbro.Grammatik.ArenaStorage

open ArenaOwnership (Frame Handle Cell)

variable {region α : Type} {H H' : Heap region α} {capacity : Capacity}

theorem Heap.empty_valid (capacity : Capacity) : (Heap.empty : Heap region α).Valid capacity := by
  refine ⟨ArenaOwnership.State.empty_valid, ?_, ?_, .nil, ?_, ?_⟩
  · intro i c h; cases h
  · intro i; rfl
  · intro i h; cases h
  · cases capacity <;> simp only [Capacity.permits, empty, Nat.zero_le, decide_true]

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
