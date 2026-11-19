module

public import Grammatik.Niedrig.Erfuellbarkeit.Layout
public import Grammatik.Niedrig.Boot.Preservation
public import Grammatik.Niedrig.Erfuellbarkeit.Shared

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

end Gabbro.Grammatik.LowLevel.Witness
