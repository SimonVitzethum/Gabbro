module

public import Grammatik.Niedrig.Witnesses.Fixture

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Witness

def readView : View D := { writableView with rights := readOnlyRights }

def readResult : ViewResult authority initial :=
  { view := readView
    admission :=
      { span := List.mem_cons_self ..
        owner := rfl
        epoch := ⟨rfl, rfl⟩
        lender := rfl
        bounds := ⟨by change 100 ≤ 100; omega, by change 100 + 4 ≤ 100 + 8; omega⟩
        memoryClass := rfl
        permissions := ⟨.inl rfl, fun _ => rfl, (by intro h; cases h), rfl⟩
        alignment := ⟨by change 0 < 1; omega, rfl, rfl⟩
        mapping := rfl
        initialization := rfl
        compatible := (by intro w member; cases member) }
    owners := borrowedOwners
    borrowed := rfl }

def innerView : View D :=
  { readView with
    lender := OwnerWitness.child
    borrower := OwnerWitness.grandchild }

def nestedOwners : OwnerState D :=
  initialOwners.withLedger ((OwnerWitness.mintedLedger.put 0
    (some ⟨0, 0, OwnerWitness.root, [OwnerWitness.child]⟩)).put 0
    (some ⟨0, 0, OwnerWitness.root, [OwnerWitness.grandchild, OwnerWitness.child]⟩))

def innerResult : ViewResult authority readResult.next :=
  { view := innerView
    admission :=
      { span := List.mem_cons_self ..
        owner := rfl
        epoch := ⟨rfl, rfl⟩
        lender := rfl
        bounds := readResult.admission.bounds
        memoryClass := rfl
        permissions := readResult.admission.permissions
        alignment := readResult.admission.alignment
        mapping := rfl
        initialization := rfl
        compatible := (by
          intro w member
          change w ∈ [readView] at member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          subst w
          exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩) }
    owners := nestedOwners
    borrowed := rfl }

theorem shared_borrows_zeuge :
    ram_view authority initial start 4 readOnlyRights OwnerWitness.child = .ok readResult ∧
    ram_view authority readResult.next start 4 readOnlyRights OwnerWitness.grandchild =
      .ok innerResult := ⟨rfl, rfl⟩

/-- The overlapping-read theorem has a genuinely inhabited overlap premise. -/
theorem live_views_overlap_readonly_zeuge :
    innerView ∈ innerResult.next.views ∧ readView ∈ innerResult.next.views ∧
    innerView ≠ readView ∧ innerView.Overlaps readView ∧
    innerView.rights.write = false ∧ readView.rights.write = false := by
  have valid := ram_view_preserves (ram_view_preserves initial_valid readResult) innerResult
  have first : innerView ∈ innerResult.next.views := List.mem_cons_self ..
  have second : readView ∈ innerResult.next.views :=
    List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have different : innerView ≠ readView := by
    intro h
    have he := congrArg (fun v : View D => v.borrower.activation) h
    change 2 = 1 at he
    omega
  have overlap : innerView.Overlaps readView :=
    ⟨rfl, by change 100 < 100 + 4; omega, by change 100 < 100 + 4; omega⟩
  exact ⟨first, second, different, overlap,
    live_views_overlap_readonly valid first second different overlap⟩

theorem nested_return_zeuge :
    returnView authority innerResult.next = .ok readResult.next ∧
    returnView authority readResult.next = .ok initial :=
  ⟨ram_view_return (ram_view_preserves initial_valid readResult) innerResult,
    ram_view_return initial_valid readResult⟩

end Gabbro.Grammatik.LowLevel.Witness
