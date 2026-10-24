import Grammatik.Bausteine.Arena.Unbounded.Safety

namespace Gabbro.Grammatik.ArenaStorage

open ArenaOwnership (Frame Handle Cell)

variable {region α : Type} {H H' : Heap region α} {capacity : Capacity}

/-- Changing grants or the scoped borrower never duplicates payload storage. -/
theorem Heap.Valid.withRights (hv : H.Valid capacity) (rights : ArenaOwnership.State)
    (hr : rights.valid) (hs : ∀ i, (rights.cells i).isSome = (H.rights.cells i).isSome) :
    ({ H with rights := rights } : Heap region α).Valid capacity := by
  refine ⟨hr, ?_, fun i => (hv.coherent i).trans (hs i).symm,
    hv.free_nodup, ?_, hv.capacity⟩
  · intro i c hc
    have hh : (H.rights.cells i).isSome = true := by rw [← hs i, hc]; rfl
    cases ho : H.rights.cells i with
    | none => simp [ho] at hh
    | some old => exact hv.support i old ho
  · intro i hi
    obtain ⟨hb, he⟩ := hv.free_empty i hi
    refine ⟨hb, ?_⟩
    have hh := hs (i : Int)
    rw [he] at hh
    cases hc : rights.cells (i : Int) <;> simp_all

theorem Heap.write_valid {frame : Frame} {r : Ref region} {value : α}
    (hv : H.Valid capacity) (he : H.write frame r value = some H') :
    H'.Valid capacity ∧ H'.read frame r = some value := by
  unfold Heap.write at he
  split at he
  · rename_i ha
    cases he
    have hc : (H.rights.cells r.handle.slot).isSome = true := by
      unfold ArenaOwnership.State.access at ha
      split at ha
      · contradiction
      · rename_i c hc; simp [hc]
    refine ⟨⟨hv.rights, hv.support, ?_, hv.free_nodup, hv.free_empty, hv.capacity⟩, ?_⟩
    · intro i
      by_cases hi : i = r.handle.slot
      · subst i; simpa [Heap.put] using hc.symm
      · simpa [Heap.put, hi] using hv.coherent i
    · simp [Heap.read, Heap.put, ha]
  · cases he

theorem Heap.release_valid {frame : Frame} {r : Ref region}
    (hv : H.Valid capacity) (he : H.release frame r = some H') :
    H'.Valid capacity ∧ (∀ g, H'.read g r = none) := by
  unfold Heap.release at he
  cases hr : H.rights.release frame r.handle with
  | none => simp [hr] at he
  | some rights =>
    simp only [hr] at he
    cases he
    have ho := ArenaOwnership.State.release_requires_owner hr
    have hcell : ∃ c, H.rights.cells r.handle.slot = some c := by
      unfold ArenaOwnership.State.owns at ho
      cases hc : H.rights.cells r.handle.slot with
      | none => simp [hc] at ho
      | some c => exact ⟨c, rfl⟩
    obtain ⟨c, hc⟩ := hcell
    obtain ⟨h0, hbound⟩ := hv.support _ _ hc
    have hnat : (r.handle.slot.toNat : Int) = r.handle.slot := Int.toNat_of_nonneg h0
    have hrights : rights = H.rights.put r.handle.slot none := by
      simpa [ArenaOwnership.State.release, ho] using hr.symm
    have hnmem : r.handle.slot.toNat ∉ H.free := by
      intro hm
      have hh := (hv.free_empty _ hm).2
      rw [hnat, hc] at hh
      contradiction
    refine ⟨?_, ?_⟩
    · refine ⟨(ArenaOwnership.State.release_valid hv.rights frame r.handle hr).1,
        ?_, ?_, List.nodup_cons.mpr ⟨hnmem, hv.free_nodup⟩, ?_, hv.capacity⟩
      · intro i c hi
        rw [hrights] at hi
        by_cases hs : i = r.handle.slot
        · simp [ArenaOwnership.State.put, hs] at hi
        · exact hv.support i c (by simpa [ArenaOwnership.State.put, hs] using hi)
      · intro i
        simp only [Heap.put]
        rw [hrights]
        by_cases hs : i = r.handle.slot
        · simp [ArenaOwnership.State.put, hs]
        · simpa [ArenaOwnership.State.put, hs] using hv.coherent i
      · intro i hi
        rcases List.mem_cons.mp hi with hi | hi
        · subst i
          exact ⟨by change r.handle.slot.toNat < H.extent; omega,
            by simp [hrights, ArenaOwnership.State.put, hnat]⟩
        · obtain ⟨hb, hz⟩ := hv.free_empty i hi
          exact ⟨hb, by simpa [hrights, ArenaOwnership.State.put,
            show (i : Int) ≠ r.handle.slot by intro eq; rw [eq, hc] at hz; contradiction] using hz⟩
    · intro g
      have hn := (ArenaOwnership.State.release_valid hv.rights frame r.handle hr).2 g
      simp [Heap.read, hn]

theorem Heap.move_valid {f g : Frame} {r r' : Ref region}
    (hv : H.Valid capacity) (he : H.move f g r = some (H', r')) :
    H'.Valid capacity ∧ H'.rights.owns g r'.handle ∧ (∀ k, H'.read k r = none) := by
  unfold Heap.move at he
  cases hr : H.rights.move f g r.handle with
  | none => simp [hr] at he
  | some pair =>
    rcases pair with ⟨rights, handle⟩
    simp only [hr] at he
    cases he
    have hp := ArenaOwnership.State.move_valid hv.rights f g r.handle hr
    refine ⟨hv.withRights rights hp.1 ?_, hp.2.1, ?_⟩
    · intro i
      unfold ArenaOwnership.State.move at hr
      split at hr
      · rename_i hg
        have hcell : (H.rights.cells r.handle.slot).isSome = true := by
          have ho := hg.1
          unfold ArenaOwnership.State.owns at ho
          split at ho
          · contradiction
          · rename_i c hc; simp [hc]
        have hh := congrArg Prod.fst (Option.some.inj hr)
        dsimp only at hh
        rw [← hh]
        by_cases hi : i = r.handle.slot
        · subst i; simp [ArenaOwnership.State.put, hcell]
        · simp [ArenaOwnership.State.put, hi]
      · cases hr
    · intro k; simp [Heap.read, hp.2.2.1 k]

theorem Heap.lend_valid {f g : Frame} {r : Ref region}
    (hv : H.Valid capacity) (he : H.lend f g r = some H') :
    H'.Valid capacity ∧ H'.rights.access g r.handle ∧ ¬ H'.rights.owns g r.handle ∧
      H'.read f r = none := by
  unfold Heap.lend at he
  cases hr : H.rights.lend f g r.handle with
  | none => simp [hr] at he
  | some rights =>
    simp only [hr] at he
    cases he
    have hp := ArenaOwnership.State.lend_valid hv.rights f g r.handle hr
    refine ⟨hv.withRights rights hp.1 ?_, hp.2.1, hp.2.2.1, ?_⟩
    · intro i
      unfold ArenaOwnership.State.lend at hr
      split at hr
      · cases hr
      · rename_i c hc
        split at hr
        · have hh := Option.some.inj hr
          rw [← hh]
          by_cases hi : i = r.handle.slot
          · subst i; simp [ArenaOwnership.State.put, hc]
          · simp [ArenaOwnership.State.put, hi]
        · cases hr
    · simp [Heap.read, hp.2.2.2]

theorem Heap.endLoan_valid {f : Frame} {r : Ref region}
    (hv : H.Valid capacity) (he : H.endLoan f r = some H') : H'.Valid capacity := by
  unfold Heap.endLoan at he
  cases hr : H.rights.endLoan f r.handle with
  | none => simp [hr] at he
  | some rights =>
    simp only [hr] at he
    cases he
    apply hv.withRights rights (ArenaOwnership.State.endLoan_valid hv.rights f r.handle hr)
    intro i
    unfold ArenaOwnership.State.endLoan at hr
    split at hr
    · cases hr
    · rename_i c hc
      split at hr
      · cases hr
      · split at hr
        · have hh := Option.some.inj hr
          rw [← hh]
          by_cases hi : i = r.handle.slot
          · subst i; simp [ArenaOwnership.State.put, hc]
          · simp [ArenaOwnership.State.put, hi]
        · cases hr

/-- The finite reset checker is equivalent to the existing all-frames ownership rule. -/
theorem Heap.canReset_iff (hv : H.Valid capacity) (frame : Frame) :
    H.canReset frame = true ↔ H.rights.canReset frame := by
  simp only [Heap.canReset, List.all_eq_true, List.mem_range]
  constructor
  · intro hall i c hc
    obtain ⟨h0, hb⟩ := hv.support i c hc
    have hi : i.toNat < H.extent := by omega
    have hh := hall i.toNat hi
    simpa [Int.toNat_of_nonneg h0, hc] using hh
  · intro hall i hi
    cases hc : H.rights.cells (i : Int) with
    | none => rfl
    | some c => simpa using hall _ _ hc

theorem Heap.reset_valid {frame : Frame} (hv : H.Valid capacity)
    (he : H.reset frame = some H') :
    H'.Valid capacity ∧ (∀ f r, H'.read f r = none) ∧ H'.rights.next = H.rights.next := by
  unfold Heap.reset at he
  split at he
  · cases he
    refine ⟨⟨ArenaOwnership.State.reset_valid _, ?_, ?_, .nil, ?_, ?_⟩, ?_, rfl⟩
    · intro i c hc; cases hc
    · intro i; rfl
    · intro i hi; cases hi
    · cases capacity <;> simp [Capacity.permits]
    · intro f r
      simp [Heap.read, ArenaOwnership.State.reset, ArenaOwnership.State.access]
  · cases he

theorem Heap.reset_blocked_by_other {f g : Frame} {r : Ref region}
    (hv : H.Valid capacity) (ho : H.rights.owns g r.handle) (hne : g ≠ f) :
    H.reset f = none := by
  have hn := ArenaOwnership.State.reset_blocked_by_other ho hne
  have hc : H.canReset f = false := by
    cases he : H.canReset f with
    | false => rfl
    | true => exact False.elim (hn ((H.canReset_iff hv f).mp he))
  simp [Heap.reset, hc]

/-- Numeric slot reuse cannot revive an earlier allocation or consuming-call alias. -/
theorem Heap.reuse_no_revival {available : Bool} {frame : Frame} {value : α} {r old : Ref region}
    (he : H.allocate capacity available frame value = some (H', r))
    (hs : old.handle.slot = (H.candidate : Int)) (hg : old.handle.grant < H.rights.next) :
    ∀ f, H'.read f old = none := by
  have hr := (Heap.allocate_parts he).2.2.1
  intro f
  have hn := ArenaOwnership.State.reuse_no_revival hr hs hg f
  simp [Heap.read, hn]

end Gabbro.Grammatik.ArenaStorage
