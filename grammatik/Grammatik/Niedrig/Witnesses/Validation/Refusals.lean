module

public import Grammatik.Niedrig.Witnesses.NoBypass

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Witness

/-! ## N1: a forged span is refused as an authority failure -/

/-- A span that is not on the authority ledger: same table, foreign base. -/
def forgedSpan : Span D := { ram with base := 50 }

def forgedView : View D := { writableView with span := forgedSpan }

/-- `checkView` refuses the forged span with `.authority`, not `.bounds`. -/
theorem n1_forged_authority_zeuge :
    checkView authority initial forgedView = .error .authority := rfl

/-! ## N2: base plus length past the address width is refused as bounds -/

/-- 100 + 157 = 257 runs past both the span end (108) and 2 ^ 8. -/
theorem n2_wraparound_zeuge :
    ram_view authority initial start 157 readWriteRights OwnerWitness.child =
      .error .bounds := rfl

/-! ## N3: a view admitted at an old epoch is refused after the bump -/

/-- The fixture authority with its epoch bumped; spans stay at epoch 2. -/
def staleAuthority : Authority D := { authority with epoch := 3 }

theorem n3_stale_epoch_zeuge :
    staleAuthority.epoch = 3 ∧ writableResult.view.epoch = 2 ∧
    ram_view staleAuthority initial start 4 readWriteRights OwnerWitness.child =
      .error .authority := ⟨rfl, rfl, rfl⟩

/-! ## N10: device memory is refused the ordinary-RAM path -/

def deviceSpanView : View D :=
  { span := device
    base := 108
    length := 2
    rights := readOnlyRights
    lender := OwnerWitness.root
    borrower := OwnerWitness.child
    epoch := 2 }

theorem n10_device_via_ram_view_zeuge :
    checkView authority initial deviceSpanView = .error .memoryClass ∧
    ram_view authority initial deviceStart 2 readOnlyRights OwnerWitness.child =
      .error .memoryClass :=
  ⟨rfl, class_refusal_zeuge⟩

/-! ## N8: after the return, the written change admits no view-scoped step -/

theorem n8_hidden_shared_write_zeuge :
    returnView authority writableResult.next = .ok initial ∧
    ¬ ViewScopedStep authority layout initial inertMachine writtenMachine 0 :=
  ⟨return_zeuge, outside_views_zeuge⟩

#print axioms Gabbro.Grammatik.LowLevel.Witness.n1_forged_authority_zeuge
#print axioms Gabbro.Grammatik.LowLevel.Witness.n2_wraparound_zeuge
#print axioms Gabbro.Grammatik.LowLevel.Witness.n3_stale_epoch_zeuge
#print axioms Gabbro.Grammatik.LowLevel.Witness.n10_device_via_ram_view_zeuge
#print axioms Gabbro.Grammatik.LowLevel.Witness.n8_hidden_shared_write_zeuge

end Gabbro.Grammatik.LowLevel.Witness
