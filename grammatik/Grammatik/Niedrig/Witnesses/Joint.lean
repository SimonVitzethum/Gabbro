module

public import Grammatik.Niedrig.Witnesses.Boot

public section

namespace Gabbro.Grammatik.LowLevel.Witness

theorem address_operations_zeuge :
    (AddressExpr.offset (.literal 100) 4 : AddressExpr space).eval = address space 104 ∧
    address space 256 = .error .range ∧ address space (-1) = .error .range ∧
    (addressDifference start deviceStart).n = -8 ∧
    (evalAddress (.offset (.literal 100) 4 : AddressExpr space) before).2 = before ∧
    (evalAddress (.literal 100 : AddressExpr space) before).1 =
      (evalAddress (.literal 100 : AddressExpr space) after).1 :=
  ⟨rfl, rfl, rfl, rfl, address_world_unchanged _ _, address_result_independent _ _ _⟩

theorem address_narrowing_zeuge :
    narrowAddress 6 (by omega) start = .error .range ∧
    address space 100 = .ok start ∧ start.location = (0, 100) := ⟨rfl, rfl, rfl⟩

theorem context_linearity_zeuge :
    List.Perm (OwnerBindings.resources (D := D) OwnerWitness.ghost)
      (OwnerBindings.resources OwnerWitness.renamedGhost) ∧
    ¬ writableResult.next.owners.access authority.names initial.frame authority.token ∧
    OwnerState.retire authority.names writableResult.next.owners writableResult.next.frame
      authority.token = none :=
  ⟨OwnerBindings.move_resource_perm (D := D)
      (show OwnerBindings.move OwnerWitness.ghost 10 11 = some OwnerWitness.renamedGhost from rfl),
    (ram_view_suspends initial_valid writableResult).1,
    (view_blocks_consumption initial_valid writableResult OwnerWitness.grandchild).1⟩

theorem context_accessor_unique_zeuge :
    initial.owners.access authority.names initial.frame authority.token ∧
    initial.frame = OwnerWitness.root :=
  ⟨initial_valid.2.2.1,
    OwnerState.access_unique (D := D) (g := OwnerWitness.root)
      initial_valid.2.2.1 initial_valid.2.2.1⟩

theorem ram_view_inside_span_zeuge :
    (0 : Nat) = writableResult.view.span.space.backing ∧
    writableResult.view.span.range.drin 100 :=
  ram_view_inside_span (D := D) writableResult (byte := (0, 100))
    ⟨rfl, by change 100 ≤ 100; omega, by change 100 < 100 + 4; omega⟩

theorem ram_view_nonwrapping_zeuge :
    writableResult.view.base + writableResult.view.length ≤ 2 ^ writableResult.view.span.space.width :=
  ram_view_nonwrapping initial_valid writableResult

theorem ram_view_request_zeuge :
    writableResult.view.span.space = space ∧ writableResult.view.base = start.byte ∧
    writableResult.view.length = 4 ∧ writableResult.view.rights = readWriteRights ∧
    writableResult.view.borrower = OwnerWitness.child :=
  ram_view_request successful_view_zeuge

theorem ram_view_progress_zeuge :
    AuthorityStep authority initial none initial ∧ initial.Valid authority := by
  have progress : AuthorityStep authority initial none initial := by
    simpa only [class_refusal_zeuge] using
      (ram_view_progress (a := authority) (c := initial) deviceStart 2
        readOnlyRights OwnerWitness.child)
  exact ⟨progress, authority_step_preserves initial_valid progress⟩

theorem empty_view_no_byte_zeuge :
    ¬ ({ writableView with length := 0 } : View D).Contains (0, 100) :=
  empty_view_no_byte ({ writableView with length := 0 } : View D) rfl (0, 100)

theorem protocol_zeuge :
    AuthorityStep authority initial (some writableResult.view) writableResult.next ∧
    writableResult.next.Valid authority ∧ writableResult.view.epoch = authority.epoch := by
  have step : AuthorityStep authority initial (some writableResult.view) writableResult.next :=
    .ram start 4 readWriteRights OwnerWitness.child writableResult successful_view_zeuge
  exact ⟨step, authority_step_preserves initial_valid step,
    authority_step_live_epoch initial_valid step (List.mem_cons_self ..)⟩

theorem view_only_from_ram_zeuge :
    ∃ (s : Space D) (start : Address s) (length : _) (rights : _) (borrower : _) (r : ViewResult authority initial),
      ram_view authority initial start length rights borrower = .ok r ∧
      writableResult.view = r.view ∧ writableResult.next = r.next :=
  view_only_from_ram protocol_zeuge.1

theorem context_no_drop_or_duplication_zeuge :
    Res.marke authority.token.mark authority.token.stage ∈
      OwnerBindings.resources (D := D) OwnerWitness.renamedGhost ∧
    (OwnerWitness.renamedGhost.map OwnerBinding.mark).Nodup :=
  context_no_drop_or_duplication (D := D) (a := authority) (c := initial)
    (result := some writableResult.view) (c' := writableResult.next)
    { protocol := protocol_zeuge.1
      before := OwnerWitness.ghost
      after := OwnerWitness.renamedGhost
      source := 10
      into := 11
      bound := List.mem_cons_self ..
      moved := rfl }

theorem returnView_preserves_zeuge : initial.Valid authority :=
  returnView_preserves (ram_view_preserves initial_valid writableResult) return_zeuge

/-- One fixture jointly realizes the authority/boot/layout/write premises and
    all required refusal cases. Shared.lean additionally inhabits real overlap.
    No source acceptance or goal-statement extension follows from this layer. -/
theorem joint_zeuge :
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
