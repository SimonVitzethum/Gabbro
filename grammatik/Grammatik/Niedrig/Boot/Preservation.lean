module

public import Grammatik.Niedrig.Boot.Transition

public section

namespace Gabbro.Grammatik.LowLevel

variable {D : Deklaration} {P I : Type} {a : Authority D} {c : Context D P I}

theorem handoff_preserves (hc : c.Valid a) (r : HandoffResult a c) :
    r.next.Valid r.authority := by
  have hg := OwnerState.transfer_grant (D := D) hc.2.1 r.moved
  have ha : r.authority.Valid := by
    refine ⟨?_, ?_, ?_, hc.1.2.2.2⟩
    · simpa only [HandoffResult.authority, hg.2.2.1] using hc.1.1
    · simpa only [HandoffResult.authority, hg.2.2.1, hg.2.2.2.1] using hc.1.2.1
    · intro span member
      have hs := hc.1.2.2.1 span member
      exact ⟨hs.1, hs.2.1.trans hg.2.2.1.symm, hs.2.2⟩
  refine ⟨ha, hg.1, ?_, ?_, ?_⟩
  · exact ⟨hg.2.1.1, hg.2.1.2.1,
      ArenaOwnership.State.owner_access (s := r.owners.ledger)
        (f := r.into) (h := r.token.handle) hg.2.1.2.2⟩
  · intro v member
    cases member
  · intro v member
    cases member

/-- The input grant is invalidated globally, including in suspended callers. -/
theorem handoff_old_context_spent (hc : c.Valid a) (r : HandoffResult a c)
    (frame : ArenaOwnership.Frame) : ¬ r.next.owners.access a.names frame a.token :=
  (OwnerState.transfer_grant (D := D) hc.2.1 r.moved).2.2.2.2.1 frame

theorem boot_step_preserves {b : BootContract D P I} {a' : Authority D} {c' : Context D P I}
    (hc : c.Valid a) (step : BootStep b a c a' c') : c'.Valid a' := by
  cases step with
  | software step => exact authority_step_preserves hc step
  | handoff r contract => exact handoff_preserves hc r

/-- Borrow/return keep epochs, and a fresh-grant handoff keeps the span epochs.
    Revocation/reuse, which need a strict increase, are deliberately left to L6. -/
theorem boot_epoch_monotone {b : BootContract D P I} {a' : Authority D} {c' : Context D P I}
    (step : BootStep b a c a' c') : a.epoch ≤ a'.epoch := by
  cases step <;> exact Nat.le_refl _

/-- The root condition follows from the user's transition proof, not from the
    fact that firmware supplied a good starting context. -/
theorem boot_root_from_logic {b : BootContract D P I} (logic : BootObligation b)
    (firmware : FirmwareEntry b a c) (r : HandoffResult a c)
    (contract : b.transition a c r.authority r.next) :
    b.root r.authority r.next :=
  logic a c r.authority r.next firmware.contract contract

end Gabbro.Grammatik.LowLevel
