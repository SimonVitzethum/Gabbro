import Grammatik.Bausteine.Arena.Unbounded.Execution

namespace Gabbro.Grammatik.ArenaStorage

open ArenaOwnership (Frame)

variable {region α : Type} {H H' : Heap region α} {capacity : Capacity}

/-- Local framing includes both payload and its exact live grant. -/
def Heap.AgreesAt (H' H : Heap region α) (slot : Int) : Prop :=
  H'.rights.cells slot = H.rights.cells slot ∧ H'.payload slot = H.payload slot

theorem Heap.AgreesAt.owns {slot : Int} (hf : H'.AgreesAt H slot)
    {frame : Frame} {reference : Ref region} (hs : reference.handle.slot = slot)
    (ho : H.rights.owns frame reference.handle) : H'.rights.owns frame reference.handle := by
  unfold ArenaOwnership.State.owns at ho ⊢
  simpa only [hs, hf.1] using ho

theorem Heap.AgreesAt.read {slot : Int} (hf : H'.AgreesAt H slot)
    (frame : Frame) (reference : Ref region) (hs : reference.handle.slot = slot) :
    H'.read frame reference = H.read frame reference := by
  have ha : H'.rights.access frame reference.handle ↔ H.rights.access frame reference.handle := by
    unfold ArenaOwnership.State.access
    rw [hs, hf.1]
  by_cases ho : H.rights.access frame reference.handle
  · simp only [Heap.read, ha.mpr ho, ↓reduceIte, hs, hf.2, ho]
  · have hn : ¬ H'.rights.access frame reference.handle := fun hh => ho (ha.mp hh)
    simp only [Heap.read, hn, ↓reduceIte, ho]

theorem Heap.allocate_frame {available : Bool} {frame : Frame} {value : α} {reference : Ref region}
    (he : H.allocate capacity available frame value = some (H', reference)) (i : Int)
    (hne : i ≠ (H.candidate : Int)) : H'.AgreesAt H i := by
  have hp := Heap.allocate_parts he
  have hr := hp.2.2.1
  constructor
  · unfold ArenaOwnership.State.allocate at hr
    split at hr
    · cases hr
    · have hh := congrArg Prod.fst (Option.some.inj hr)
      dsimp only at hh
      rw [← hh]
      simp only [ArenaOwnership.State.put, hne, ↓reduceIte]
  · have hh := congrFun (congrArg Heap.payload hp.2.2.2) i
    simpa [Heap.install, hne] using hh

/-- Every currently owned allocation is distinct from the selected free/fresh slot. -/
theorem Heap.owned_candidate_ne (hv : H.Valid capacity) {frame : Frame} {reference : Ref region}
    (ho : H.rights.owns frame reference.handle) : reference.handle.slot ≠ (H.candidate : Int) := by
  intro heq
  unfold ArenaOwnership.State.owns at ho
  rw [heq, (H.candidate_facts hv).1] at ho
  exact ho

theorem Heap.release_exists {frame : Frame} {reference : Ref region}
    (ho : H.rights.owns frame reference.handle) : ∃ H', H.release frame reference = some H' := by
  simp only [release, ArenaOwnership.State.release, ho, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
  Option.some.injEq, exists_eq']

theorem Heap.release_frame {frame : Frame} {reference : Ref region}
    (he : H.release frame reference = some H') (i : Int) (hne : i ≠ reference.handle.slot) :
    H'.AgreesAt H i := by
  unfold Heap.release at he
  cases hr : H.rights.release frame reference.handle with
  | none => simp only [hr, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at he
  | some rights =>
    simp only [hr] at he
    cases he
    have ho := ArenaOwnership.State.release_requires_owner hr
    have hh : rights = H.rights.put reference.handle.slot none := by
      simpa [ArenaOwnership.State.release, ho] using hr.symm
    exact ⟨by simp only [hh, ArenaOwnership.State.put, hne, ↓reduceIte], by simp only [put, hne, ↓reduceIte]⟩

end Gabbro.Grammatik.ArenaStorage
