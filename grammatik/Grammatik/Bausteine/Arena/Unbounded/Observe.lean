import Grammatik.Bausteine.Arena.Unbounded.Linked
import Mathlib.Data.List.Nodup

namespace Gabbro.Grammatik.ArenaStorage.Linked

open ArenaOwnership (Frame)

variable {region α : Type} {H : Memory region α} {frame : Frame} {head entries}

theorem Chain.slots_nodup (hv : H.Valid .unbounded) (hc : Chain H frame head entries) :
    (entries.map (fun entry => entry.1.handle.slot.toNat)).Nodup := by
  induction hc with
  | empty => exact .nil
  | @cell reference value next entries ho hr hc hn ih =>
    refine List.nodup_cons.mpr ⟨?_, ih⟩
    intro hm
    obtain ⟨entry, he, heq⟩ := List.mem_map.mp hm
    have hb := Heap.access_bounded hv (ArenaOwnership.State.owner_access ho)
    have hb' := Heap.access_bounded hv (ArenaOwnership.State.owner_access (hc.owned _ he))
    dsimp only at heq
    have hs := congrArg (fun n : Nat => (n : Int)) heq
    rw [Int.toNat_of_nonneg hb'.1, Int.toNat_of_nonneg hb.1] at hs
    exact hn entry he hs

/-- A well-formed linked chain is no longer than its finite backing extent. -/
theorem Chain.length_le_extent (hv : H.Valid .unbounded) (hc : Chain H frame head entries) :
    entries.length ≤ H.extent := by
  have hh := (Chain.slots_nodup hv hc).length_le_of_subset (l₂ := List.range H.extent) (by
    intro i hi
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hi
    have hb := Heap.access_bounded hv (ArenaOwnership.State.owner_access (hc.owned _ he))
    simp only [List.mem_range]
    omega)
  simpa using hh

/-- The observer's fuel comes from the actual finite heap, not a trusted oracle
or a caller-supplied guess about the stack's contents. -/
theorem readAll_extent (hv : H.Valid .unbounded) {values : List α}
    (hr : Represents H frame head values) : readAll H frame H.extent head = some values := by
  obtain ⟨entries, hc, rfl⟩ := hr
  exact hc.readAll H.extent (hc.length_le_extent hv)

end Gabbro.Grammatik.ArenaStorage.Linked
