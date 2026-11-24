module

public import Core.Ast.LowLevel.Mem.Obligations

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

def PartitionPost (before after : MemFrame) (region : MemRegion) (slot point : Nat) : Prop :=
  ∃ left right : MemRegion,
    after.result = some (.partition left right) ∧
    left.extent = ⟨region.extent.von, point⟩ ∧ right.extent = ⟨point, region.extent.bis⟩ ∧
    left.backing = region.backing ∧ right.backing = region.backing ∧
    after.regions = before.regions.set slot (some left) ++ [some right] ∧
    left.extent.getrennt right.extent ∧
    ∀ addr, region.extent.drin addr ↔ left.extent.drin addr ∨ right.extent.drin addr

def SplitAtMeaningAussage : Prop :=
  ∀ target s c slot point,
    (heldMemRegion target s c slot = none →
      (MemInstruction.splitRegion slot point).evaluate target s c = none) ∧
    ∀ region, heldMemRegion target s c slot = some region →
      (region.extent.von < point ∧ point < region.extent.bis →
        ∃ next, (MemInstruction.splitRegion slot point).evaluate target s c = some next ∧
          PartitionPost (s.lokal c) next region slot point) ∧
      (¬ (region.extent.von < point ∧ point < region.extent.bis) →
        (MemInstruction.splitRegion slot point).evaluate target s c = none)

def SplitPagesMeaningAussage : Prop :=
  ∀ target s c slot pages,
    (heldMemRegion target s c slot = none →
      (MemInstruction.splitPages slot pages).evaluate target s c = none) ∧
    ∀ region, heldMemRegion target s c slot = some region →
      let granule := target.seitengranule
      let point := region.extent.von + pages * granule
      (region.extent.von % granule = 0 ∧ 0 < pages ∧ point < region.extent.bis →
        ∃ next, (MemInstruction.splitPages slot pages).evaluate target s c = some next ∧
          PartitionPost (s.lokal c) next region slot point ∧
          point % granule = 0 ∧ point - region.extent.von = pages * granule) ∧
      (¬ (region.extent.von % granule = 0 ∧ 0 < pages ∧ point < region.extent.bis) →
        (MemInstruction.splitPages slot pages).evaluate target s c = none)

def MergeMeaningAussage : Prop :=
  ∀ target s c first second,
    ((heldMemRegion target s c first = none ∨ heldMemRegion target s c second = none) →
      (MemInstruction.mergeRegions first second).evaluate target s c = none) ∧
    ∀ left right, heldMemRegion target s c first = some left →
      heldMemRegion target s c second = some right →
      let adjacent := first ≠ second ∧ left.extent.von < left.extent.bis ∧
        right.extent.von < right.extent.bis ∧
        (left.extent.bis = right.extent.von ∨ right.extent.bis = left.extent.von)
      (adjacent → ∃ next joined,
        (MemInstruction.mergeRegions first second).evaluate target s c = some next ∧
        next.result = some (.merged joined) ∧
        next.regions = ((s.lokal c).regions.set first (some joined)).set second none ∧
        next.regions[second]?.join = none ∧ joined.backing = left.backing ++ right.backing ∧
        ∀ addr, joined.extent.drin addr ↔ left.extent.drin addr ∨ right.extent.drin addr) ∧
      (¬ adjacent → (MemInstruction.mergeRegions first second).evaluate target s c = none)

private theorem partition_post (frame : MemFrame) (slot : Nat) (region : MemRegion) (point : Nat)
    (inside : region.extent.von < point ∧ point < region.extent.bis) :
    PartitionPost frame (frame.partition slot region point) region slot point := by
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl (Nat.le_refl _), ?_⟩
  intro addr
  change region.extent.von ≤ addr ∧ addr < region.extent.bis ↔
    (region.extent.von ≤ addr ∧ addr < point) ∨ (point ≤ addr ∧ addr < region.extent.bis)
  -- The use of the split point inside the region is supplied by each operation.
  omega

theorem splitAt_meaning : SplitAtMeaningAussage := by
  intro target s c slot point
  constructor
  · intro missing
    simp only [MemInstruction.evaluate, missing, Option.bind_none]
  · intro region held
    constructor
    · intro inside
      exact ⟨_, by simp only [MemInstruction.evaluate, held, Option.bind_some, if_pos inside],
        partition_post (s.lokal c) slot region point inside⟩
    · intro outside
      simp only [MemInstruction.evaluate, held, Option.bind_some, if_neg outside]

end Gabbro.Core.Ast.LowLevel
