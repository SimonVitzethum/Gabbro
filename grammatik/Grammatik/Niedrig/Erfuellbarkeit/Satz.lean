/-
  Subject: Satisfiability of the authority, layout and boot premises (stream E7, owner rule of 2026-11-19).
-/
module

public import Grammatik.Niedrig.Erfuellbarkeit.Boot
public import Grammatik.Niedrig.Authority.Address

public section

namespace Gabbro.Grammatik.LowLevel.Witness

/-- **Satisfiability of the authority premises** (stream E7): one fixture jointly realizes a valid authority
    context, a correct address layout the authority realizes, a firmware entry with its boot obligation, a view
    write, a successful RAM view, its return, and the boot handoff -- and the view requests that must be refused
    (wrong memory class, out of bounds, conflicting loan) are refused. No source acceptance or goal-statement
    extension follows from this layer. -/
theorem authority_erfuellbar :
    initial.Valid authority ∧ LayoutOk layout ∧ authority.Realizes layout ∧
    FirmwareEntry contract authority initial ∧ BootObligation contract ∧
    Nonempty (ViewWrite authority writableResult.next layout before after) ∧
    ram_view authority initial start 4 readWriteRights OwnerWitness.child = .ok writableResult ∧
    ram_view authority initial deviceStart 2 readOnlyRights OwnerWitness.child = .error .memoryClass ∧
    ram_view authority initial start 9 readWriteRights OwnerWitness.child = .error .bounds ∧
    ram_view authority writableResult.next start 4 readOnlyRights OwnerWitness.grandchild =
      .error .conflictingLoan ∧
    returnView authority writableResult.next = .ok initial ∧
    contract.transition authority initial handoff.authority handoff.next :=
  ⟨initial_valid, layout_correct, layout_realizes, firmware_entry, boot_logic, ⟨write⟩,
    successful_view_zeuge, class_refusal_zeuge, bounds_refusal_zeuge, conflicting_loan_zeuge,
    return_zeuge, handoff_contract⟩

end Gabbro.Grammatik.LowLevel.Witness
