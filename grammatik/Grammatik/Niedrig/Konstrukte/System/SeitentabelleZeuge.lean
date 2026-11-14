module

public import Grammatik.Niedrig.Konstrukte.Zeugen
public import Grammatik.Niedrig.Konstrukte.System.Fixture

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct.Witness

open Niedrig

/-- Both table carriers are observed. The finite first table has eight cells;
    the second is OPEN. Each typed byte represents a frame identity here. -/
def projectedTables (world : World D) : Uebersetzung.Tables := fun table index =>
  if table = 0 then
    if index < 8 then .leaf (world.slots false (index : Int) ()).n.toNat pagePermissions else .absent
  else if table = 1 then .leaf (world.slots true (index : Int) ()).n.toNat pagePermissions else .absent

theorem written_other_index (index : Nat) (different : index ≠ 0) :
    written.slots false (index : Int) () = before.slots false (index : Int) () := by
  have nonzero : (index : Int) ≠ 0 := by omega
  change (if (index : Int) = 0 then (⟨42, by decide, by decide⟩ : Zahl 0 255)
    else before.slots false (index : Int) ()) = before.slots false (index : Int) ()
  exact if_neg nonzero

theorem page_table_encoding_zeuge :
    PageTableEncodingDuty projectedTables before written 0 0 (.leaf 42 pagePermissions) := by
  funext table index
  by_cases sameTable : table = 0
  · subst table
    by_cases sameIndex : index = 0
    · subst index
      rfl
    · have other := written_other_index index sameIndex
      simp only [projectedTables, Uebersetzung.setEntry, ↓reduceIte, if_neg sameIndex, other]
  · have other : written.slots true (index : Int) () = before.slots true (index : Int) () :=
      viewPutStep_other view layout () 0 ⟨42, by decide, by decide⟩
      resources (fun _ => true) putChecked before true (by decide) (index : Int) ()
    simp only [projectedTables, Uebersetzung.setEntry, if_neg sameTable, other]

theorem page_table_write_sim_zeuge :
    ClassSimRel authority layout receipt.next
      (pageTablePutStep view layout () 0 ⟨42, by decide, by decide⟩
        resources (fun _ => true) putChecked rfl before) := by
  have simulation : ClassSimRel authority layout receipt.next before := by
    apply classSimRel_of_simRel borrowed_sim_zeuge
    intro v member
    have same : v = view := by
      change v ∈ [view] at member
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
    subst v
    exact ⟨⟨rfl, rfl, rfl⟩, by decide⟩
  exact pageTablePutStep_sim simulation view (List.mem_cons_self ..) rfl rfl () 0
    ⟨42, by decide, by decide⟩ resources (fun _ => true) putChecked (by intro lock; exact lock.elim)

theorem page_table_effect_zeuge :
    projectedTables written 0 0 = .leaf 42 pagePermissions ∧
    projectedTables written 1 0 = projectedTables before 1 0 :=
  ⟨pageTablePutStep_hit page_table_encoding_zeuge,
    pageTablePutStep_other page_table_encoding_zeuge 1 0 (by decide)⟩

end Gabbro.Grammatik.LowLevel.Construct.Witness
