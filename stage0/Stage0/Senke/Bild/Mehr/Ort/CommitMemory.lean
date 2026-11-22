module

public import Stage0.Senke.Bild.Mehr.Ort.Segment
public import Stage0.Senke.Bild.Mehr.Ort.LockFootprint
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner Runner.IR

variable {D : Deklaration}

/-- The bytes of all allocated cells belonging to the selected carriers. -/
def carrierFootprint (layout : Lay D) (carriers : D.Tab ⊕ D.Glob → Prop) (byte : W) : Prop :=
  ∃ cell : Zelle D, cell.da layout ∧ carriers cell.carrier ∧
    cell.adr layout ≤ byte.toNat ∧ byte.toNat < cell.adr layout + cell.bytes

theorem carrierFootprint_iff {layout : Lay D} {carriers : D.Tab ⊕ D.Glob → Prop}
    (separated : LayDis layout) {cell : Zelle D} (allocated : cell.da layout) {byte : W}
    (first : cell.adr layout ≤ byte.toNat) (last : byte.toNat < cell.adr layout + cell.bytes) :
    carrierFootprint layout carriers byte ↔ carriers cell.carrier := by
  constructor
  · rintro ⟨other, present, selected, before, after⟩
    have same : cell = other := by
      by_contra ne
      rcases separated.spans cell other allocated present ne with left | right <;> omega
    exact same.symm ▸ selected
  · intro selected
    exact ⟨cell, allocated, selected, first, last⟩

/-- A commit publishes the selected bytes and keeps the existing
    access permissions and all bytes outside the chosen carriers. -/
noncomputable def commitBytes (before after : Mem) (selected : W → Prop) : Mem := by
  classical
  exact { before with b := fun byte => if selected byte then after.b byte else before.b byte }

private theorem valueAt_congr_bytes {layout : Lay D} {before after : Mem}
    {address : Nat} {ty : Ty} {value : Wert D ty}
    (bound : address + 8 * valueWords ty < 2 ^ 64)
    (agrees : ∀ byte, address ≤ byte.toNat → byte.toNat < address + 8 * valueWords ty →
      after.b byte = before.b byte ∧ after.rd byte = before.rd byte)
    (encoded : ValueAt layout before (BitVec.ofNat 64 address) 0 ty value) :
    ValueAt layout after (BitVec.ofNat 64 address) 0 ty value := by
  refine ⟨encoded.1, fun index present => ?_⟩
  have indexFits : index < valueWords ty := by simpa only [encodeWords_length] using present
  have slotAddress : slot (BitVec.ofNat 64 address) (BitVec.ofNat 64 (0 + index)) =
      BitVec.ofNat 64 (address + 8 * index) := by
    simp only [Nat.zero_add, slot]
    change BitVec.ofNat 64 address + BitVec.ofNat 64 index * BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    congr 1
    omega
  have byteEq (offset : Nat) (inside : offset < 8) :=
    agrees (BitVec.ofNat 64 (address + 8 * index) + BitVec.ofNat 64 offset)
      (by rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
      (by rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
  have same : after.rd64 (BitVec.ofNat 64 (address + 8 * index)) =
      before.rd64 (BitVec.ofNat 64 (address + 8 * index)) := by
    simp only [Mem.rd64, Mem.all_congr (fun j hj => (byteEq j hj).2),
      Mem.le_congr (fun j hj => (byteEq j hj).1)]
  rw [slotAddress, same]
  have old := encoded.2 index present
  rwa [slotAddress] at old

/-- A segment's physical writes can be committed using its carrier set.
    The exact typed values of every other carrier remain those of the
    current committed world, including nested aggregates and pointers. -/
theorem weltAt_commitBytes {layout : Lay D} {before after : Mem}
    {original observed committed : World D} {carriers : D.Tab ⊕ D.Glob → Prop}
    (inside : LayIn layout) (separated : LayDis layout)
    (beforeWorld : WeltAt before layout original)
    (afterWorld : WeltAt after layout observed)
    (reads : after.rd = before.rd)
    (changed : OrtGleich carriers observed committed)
    (unchanged : ∀ carrier, ¬ carriers carrier → TraegerGleich committed.speicher original.speicher carrier) :
    WeltAt (commitBytes before after (carrierFootprint layout carriers)) layout committed := by
  let memory := commitBytes before after (carrierFootprint layout carriers)
  have copy {cell : Zelle D} (allocated : cell.da layout) {ty : Ty} {value : Wert D ty}
      (size : cell.bytes = 8 * valueWords ty)
      (bound : cell.adr layout + cell.bytes < 2 ^ 64) :
      (if carriers cell.carrier then ValueAt layout after (BitVec.ofNat 64 (cell.adr layout)) 0 ty value
        else ValueAt layout before (BitVec.ofNat 64 (cell.adr layout)) 0 ty value) →
      ValueAt layout memory (BitVec.ofNat 64 (cell.adr layout)) 0 ty value := by
    classical
    intro encoded
    by_cases chosen : carriers cell.carrier
    · rw [if_pos chosen] at encoded
      apply valueAt_congr_bytes (size ▸ bound) _ encoded
      intro byte first last
      have selected := (carrierFootprint_iff separated allocated first (size.symm ▸ last)).mpr chosen
      exact ⟨by simp only [memory, commitBytes, dif_pos selected, if_pos selected], congrFun reads.symm byte⟩
    · rw [if_neg chosen] at encoded
      apply valueAt_congr_bytes (size ▸ bound) _ encoded
      intro byte first last
      have excluded := fun selected => chosen ((carrierFootprint_iff separated allocated first (size.symm ▸ last)).mp selected)
      exact ⟨by simp only [memory, commitBytes, dif_neg excluded, if_neg excluded], rfl⟩
  classical
  refine ⟨?_, ?_, beforeWorld.2.2⟩
  · intro table field index allocated
    apply copy (cell := .elem table field index) allocated rfl
      (Nat.lt_of_le_of_lt (inside.1 table field index allocated).2 (Nat.lt_trans inside.2.2 (by decide)))
    change if carriers (.inl table) then _ else _
    split
    · next selected => rw [← changed.slots table selected]; exact afterWorld.1 table field index allocated
    · next excluded =>
      have values := unchanged (.inl table) excluded
      change committed.slots table = original.slots table at values
      rw [values]
      exact beforeWorld.1 table field index allocated
  · intro global
    apply copy (cell := .glob global) trivial rfl
      (Nat.lt_of_le_of_lt (inside.2.1 global).2 (Nat.lt_trans inside.2.2 (by decide)))
    change if carriers (.inr global) then _ else _
    split
    · next selected => rw [← changed.globs global selected]; exact afterWorld.2.1 global
    · next excluded =>
      have value := unchanged (.inr global) excluded
      change committed.globs global = original.globs global at value
      rw [value]
      exact beforeWorld.2.1 global

end Gabbro.Stage0.Senke.BildMehr
