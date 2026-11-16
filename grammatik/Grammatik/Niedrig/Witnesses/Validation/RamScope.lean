module

public import Grammatik.Niedrig.Konstrukte.Fixture
public import Grammatik.Niedrig.Konstrukte.SichtScope

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct.Witness

/-! ## P1: one receipt carries a 42 write, its read-back, and the scope close -/

/-- The admission produces exactly this receipt, independently of the
    broader constructor-witness module. -/
theorem p1_bind_receipt :
    bindViewStep authority initial start 4 LowLevel.Witness.readWriteRights
        OwnerWitness.child before =
      (.ok receipt, before) := rfl

/-- 42 goes through the view, comes back, and the scope closes on one receipt. -/
theorem p1_ram_write_read_zeuge :
    (viewGetStep view layout () rfl 0 1 resources getChecked written).value.n = 42 ∧
    runViewScope authority initial start 4 LowLevel.Witness.readWriteRights
        OwnerWitness.child before
        (fun _ _ => ((.ok 42 : Except Nat Nat), receipt.next, written))
        (fun _ world => (.ok 0, world)) =
      (.ok ((.ok 42 : Except Nat Nat), initial), written) := by
  refine ⟨rfl, ?_⟩
  have produced := congrArg Prod.fst p1_bind_receipt
  simp only [bindViewStep] at produced
  simpa only [runViewScope, produced] using
    closeViewExitStep_success (.ok 42 : Except Nat Nat) written
      (ram_view_return initial_valid receipt)

#print axioms Gabbro.Grammatik.LowLevel.Construct.Witness.p1_bind_receipt
#print axioms Gabbro.Grammatik.LowLevel.Construct.Witness.p1_ram_write_read_zeuge

end Gabbro.Grammatik.LowLevel.Construct.Witness
