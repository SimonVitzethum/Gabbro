module

public import Grammatik.Niedrig.Erfuellbarkeit.Fixture

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

end Gabbro.Grammatik.LowLevel.Witness
