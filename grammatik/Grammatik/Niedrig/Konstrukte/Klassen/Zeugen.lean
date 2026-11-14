module

public import Grammatik.Niedrig.Konstrukte.Fixture
public import Grammatik.Niedrig.Konstrukte.Klassen.GeraetSaetze
public import Grammatik.Niedrig.Konstrukte.Klassen.Typisiert

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct.Witness

/-- Device and RAM occupy different backings even though their numeric byte
    ranges coincide. This exercises physical, rather than nominal, separation. -/
noncomputable def deviceSpan : Span D := { secondSpan with memoryClass := .device }

noncomputable def deviceAuthority : Authority D := { authority with spans := [span, deviceSpan] }

theorem deviceAuthority_valid : deviceAuthority.Valid := by
  refine ⟨⟨false, by decide⟩, by decide, ?_, ?_⟩
  · intro candidate member
    change candidate ∈ [span, deviceSpan] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨by decide, rfl, by decide⟩
  · apply List.Pairwise.cons
    · intro other member
      have same : other = deviceSpan := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
      subst other
      exact .inl (by decide)
    · exact List.Pairwise.cons (fun _ member => absurd member List.not_mem_nil) .nil

theorem deviceInitial_valid : initial.Valid deviceAuthority :=
  ⟨deviceAuthority_valid, owners_valid, initial_valid.2.2.1,
    (by intro v member; cases member), (by intro v member; cases member)⟩

noncomputable def deviceView : View D := { view with span := deviceSpan }

noncomputable def deviceReceipt : ClassViewResult deviceAuthority layout initial .device :=
  { view := deviceView
    checked := by decide
    owners := receipt.owners
    borrowed := rfl }

theorem deviceInitial_sim : ClassSimRel deviceAuthority layout initial before := by
  apply classSimRel_of_simRel (simRel_initial deviceInitial_valid rfl before)
  intro v member
  cases member

theorem deviceBorrow_sim_zeuge : ClassSimRel deviceAuthority layout deviceReceipt.next before :=
  bindClassViewStep_sim deviceInitial_sim deviceReceipt

theorem deviceBind_zeuge :
    bindClassViewB deviceAuthority layout initial .device deviceView = true ∧
    (bindClassViewStep deviceAuthority layout initial .device deviceView before).2 = before :=
  ⟨by decide, bindClassViewStep_world ..⟩

def mmio : MmioRegister D () :=
  { table := true
    backing := 9
    address := 100
    bytes := 1
    littleEndian := true
    readOrder := .acquire
    writeOrder := .release }

def mmioReadChecked : MmioReadOk deviceView layout () mmio := by decide

def mmioWriteChecked : MmioWriteOk deviceView layout () mmio := by decide

theorem mmio_width_order_zeuge :
    mmioReadB deviceView layout () mmio = true ∧
    mmioWriteB deviceView layout () mmio = true ∧
    mmioReadB deviceView layout () { mmio with bytes := 2 } = false ∧
    mmioReadB deviceView layout () { mmio with readOrder := .release } = false :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem mmio_promised_zeuge :
    (mmioReadStep oracle deviceView layout () mmio mmioReadChecked false before).value =
      .ok (.ok ⟨42, by decide, by decide⟩) :=
  mmioReadStep_promised oracle deviceView layout () mmio mmioReadChecked false before
    ⟨42, by decide, by decide⟩ rfl (by decide)

def brokenOracle : Orakel D := { oracle with regLiesL := fun _ _ => 13 }

theorem mmio_reason_zeuge :
    (mmioReadStep brokenOracle deviceView layout () mmio mmioReadChecked true before).value =
      .ok (.error ⟨13, by decide, by decide⟩) ∧
    (mmioReadStep brokenOracle deviceView layout () mmio mmioReadChecked false before).value =
      .error (.geraet ()) :=
  mmioReadStep_reason brokenOracle deviceView layout () mmio mmioReadChecked before
    ⟨13, by decide, by decide⟩ rfl (by decide)

theorem mmio_sim_zeuge :
    ClassSimRel deviceAuthority layout deviceReceipt.next
      (mmioReadStep oracle deviceView layout () mmio mmioReadChecked false before).world :=
  mmioReadStep_sim deviceBorrow_sim_zeuge oracle deviceView () mmio mmioReadChecked false

theorem nominal_backing_refusal_zeuge :
    bindViewB { span with space := { space with backing := 9 } } layout 2 100 4 1
      LowLevel.Witness.readWriteRights [0] = false ∧
    bindClassViewB deviceAuthority layout deviceReceipt.next .device
      { deviceView with lender := OwnerWitness.child, borrower := OwnerWitness.grandchild } = false :=
  ⟨by decide, by decide⟩

theorem class_failure_order_zeuge :
    classViewFailure deviceAuthority layout initial .device { deviceView with length := 9 } = .bounds ∧
    classViewFailure deviceAuthority layout initial .ordinaryRam deviceView = .memoryClass ∧
    classViewFailure deviceAuthority layout deviceReceipt.next .device
      { deviceView with lender := OwnerWitness.child, borrower := OwnerWitness.grandchild } = .conflictingLoan :=
  ⟨by decide, by decide, by decide⟩

/-- A second live, writable view is allowed only because it is in the other
    backing. Its lender is suspended; both returns restore real escrow. -/
noncomputable def nestedView : View D :=
  { view with lender := OwnerWitness.child, borrower := OwnerWitness.grandchild }

noncomputable def nestedReceipt : ClassViewResult deviceAuthority layout deviceReceipt.next .ordinaryRam :=
  { view := nestedView
    checked := by decide
    owners := deviceReceipt.next.owners.withLedger (deviceReceipt.next.owners.ledger.put 0
      (some ⟨0, 0, OwnerWitness.root, [OwnerWitness.grandchild, OwnerWitness.child]⟩))
    borrowed := rfl }

theorem nestedBorrow_sim_zeuge : ClassSimRel deviceAuthority layout nestedReceipt.next before :=
  bindClassViewStep_sim deviceBorrow_sim_zeuge nestedReceipt

theorem nested_return_both_zeuge :
    closeClassViewStep (.ok 42 : Except Nat Nat) deviceAuthority nestedReceipt.next before =
      (.ok (.ok 42, deviceReceipt.next), before) ∧
    closeClassViewStep (.error 7 : Except Nat Nat) deviceAuthority nestedReceipt.next before =
      (.ok (.error 7, deviceReceipt.next), before) :=
  closeClassViewStep_both deviceBorrow_sim_zeuge.valid nestedReceipt before 42 7

def recordLayout : ViewLayout view.span.table :=
  { fields := [()]
    complete := by intro field; cases field; exact List.mem_cons_self .. }

def typedChecked : TypedViewOk view layout recordLayout 0 4 resources := by decide

theorem typed_array_zeuge :
    typedViewB view layout recordLayout 0 4 resources = true ∧
    ((typedViewGetStep view layout recordLayout 0 4 resources typedChecked written).value
      ⟨0, by decide⟩ ()).n = 42 := ⟨by decide, rfl⟩

theorem typed_device_refusal_zeuge :
    typedViewB deviceView layout
      { fields := [()], complete := by intro field; cases field; exact List.mem_cons_self .. }
      0 1 resources = false := by decide

theorem distinct_carriers_zeuge :
    span.table ≠ secondSpan.table ∧ span.space.backing ≠ secondSpan.space.backing ∧
    span.space.nominal ≠ secondSpan.space.nominal ∧ D.offen secondSpan.table = true :=
  ⟨by decide, by decide, by decide, rfl⟩

end Gabbro.Grammatik.LowLevel.Construct.Witness
