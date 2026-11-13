module

public import Grammatik.Niedrig.Witnesses.Layout
public import Grammatik.Niedrig.Witnesses.Shared

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Witness

def contract : BootContract D Privilege Bool :=
  { «entry» := fun a c => c.privilege = .firmware ∧ c.interrupt = true ∧ a.Realizes layout
    transition := fun a c a' c' => c.privilege = .firmware ∧ c.interrupt = true ∧
      c'.privilege = .user ∧ c'.interrupt = false ∧ a'.spans = a.spans
    root := fun a c => c.privilege = .user ∧ c.interrupt = false ∧ a.Realizes layout }

theorem boot_logic : BootObligation contract := by
  intro a c a' c' firmware transition
  refine ⟨transition.2.2.1, transition.2.2.2.1, ?_⟩
  intro span member
  rw [transition.2.2.2.2] at member
  exact firmware.2.2 span member

theorem firmware_entry : FirmwareEntry contract authority initial :=
  { contract := ⟨rfl, rfl, layout_realizes⟩
    valid := initial_valid
    initial := rfl
    unspent := rfl
    owned := initial_owned
    noViews := rfl }

def handoff : HandoffResult authority initial :=
  { into := OwnerWitness.child
    privilege := .user
    interrupt := false
    owners := initialOwners.withLedger OwnerWitness.movedLedger
    token := OwnerWitness.movedToken
    quiescent := rfl
    moved := rfl }

theorem handoff_contract :
    contract.transition authority initial handoff.authority handoff.next :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem handoff_zeuge :
    handoff.next.Valid handoff.authority ∧
    contract.root handoff.authority handoff.next ∧
    ¬ handoff.next.owners.access authority.names OwnerWitness.root authority.token :=
  ⟨handoff_preserves initial_valid handoff,
    boot_root_from_logic boot_logic firmware_entry handoff handoff_contract,
    handoff_old_context_spent initial_valid handoff OwnerWitness.root⟩

/-- All boot-step premises are jointly inhabited on the same two-span fixture. -/
theorem boot_step_zeuge :
    BootStep contract authority initial handoff.authority handoff.next ∧
    handoff.next.Valid handoff.authority ∧ authority.epoch ≤ handoff.authority.epoch := by
  have step : BootStep contract authority initial handoff.authority handoff.next :=
    .handoff handoff handoff_contract
  exact ⟨step, boot_step_preserves initial_valid step, boot_epoch_monotone step⟩

end Gabbro.Grammatik.LowLevel.Witness
