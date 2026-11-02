module

public import Grammatik.Kern.Syntax.Marken.Owner.Fixture
public import Grammatik.Kern.Syntax.Marken.Owner.Escrow

@[expose] public section

namespace Gabbro.Grammatik.OwnerWitness

/-- These are kernel witnesses for the resource interfaces, not source export,
    canonical G/GX execution, software-provider correctness or Stage-0 lowering. -/
theorem validB_iff_zeuge : handoff.validB id D.stufen = true ∧ handoff.Valid id D.stufen :=
  ⟨by decide, (OwnerFlow.validB_iff id D.stufen handoff).mp (by decide)⟩

/-- Namespace transport preserves the exact input and returned stage lists. -/
theorem inputs_map_zeuge :
    (handoff.map Bool.not).inputs = handoff.inputs.map (Prod.map Bool.not id) :=
  OwnerFlow.inputs_map Bool.not handoff

theorem outputs_map_zeuge :
    (handoff.map Bool.not).outputs = handoff.outputs.map (Prod.map Bool.not id) :=
  OwnerFlow.outputs_map Bool.not handoff

theorem output_from_input_zeuge : ∃ before, (true, before) ∈ handoff.inputs :=
  OwnerFlow.output_from_input handoff (by decide : (true, 1) ∈ handoff.outputs)

theorem output_bounded_zeuge : id true = true ∧ 1 < D.stufen true :=
  OwnerFlow.output_bounded validB_iff_zeuge.2 (by decide : (true, 1) ∈ handoff.outputs)

theorem outputs_nodup_zeuge : (handoff.outputs.map Prod.fst).Nodup :=
  OwnerFlow.outputs_nodup validB_iff_zeuge.2

theorem loan_exact_stage : scoped.inputs = [(true, 0)] ∧ scoped.outputs = [(true, 0)] :=
  ⟨rfl, rfl⟩

theorem duplicate_stages_refused :
    ({ moves := [⟨true, 0, some 1⟩], loans := [(true, 1)] } : OwnerFlow Bool).validB
      id (fun _ => 3) = false := by decide

theorem ordinary_mark_refused :
    ({ loans := [(false, 0)] } : OwnerFlow Bool).validB id (fun _ => 3) = false := by decide

theorem stage_overflow_refused :
    ({ moves := [⟨true, 0, some 3⟩] } : OwnerFlow Bool).validB id (fun _ => 3) = false := by decide

theorem stage_rollback_refused :
    ({ moves := [⟨true, 1, some 0⟩] } : OwnerFlow Bool).validB id (fun _ => 3) = false := by decide

theorem move_valid_zeuge : OwnerBindings.Valid renamedGhost :=
  OwnerBindings.move_valid (by decide : OwnerBindings.move ghost 10 11 = some renamedGhost)

theorem move_resource_perm_zeuge :
    List.Perm (OwnerBindings.resources ghost) (OwnerBindings.resources renamedGhost) :=
  OwnerBindings.move_resource_perm (by decide : OwnerBindings.move ghost 10 11 = some renamedGhost)

theorem take_resources_zeuge :
    List.Perm (OwnerBindings.resources ghost) (Res.marke true 0 :: OwnerBindings.resources
      ([] : OwnerBindings D.Marke)) :=
  OwnerBindings.take_resources (by decide : OwnerBindings.take ghost 10 = some (⟨10, true, 0⟩, []))

theorem take_twice_refused : OwnerBindings.take ([] : OwnerBindings D.Marke) 10 = none := rfl

theorem restore_valid_zeuge : OwnerBindings.Valid ghost :=
  OwnerBindings.restore_valid
    (by decide : OwnerBindings.restore ([] : OwnerBindings D.Marke) ⟨10, true, 0⟩ = some ghost)

theorem duplicate_binding_refused :
    OwnerBindings.restore ghost ⟨11, true, 1⟩ = none := by decide

theorem missing_owner_guard_refused : ¬ darf D () [] := by
  intro h
  have impossible := h (.inr (true, 0)) (by decide)
  cases impossible

theorem ordinary_owner_production_refused (n s : Nat) : (true, s) ∉ (D.sigNr n).produziert :=
  D.eigner_nie_erzeugt n () true s (by decide)

theorem resource_from_binding_zeuge :
    ∃ b ∈ ghost, b.mark = true ∧ b.stage = 0 :=
  OwnerBindings.resource_from_binding ghost (by decide)

/-- The owner flow is part of the real canonical signature. -/
def handoffSignature : Signatur D.Tab D.Glob D.Lock D.Marke :=
  { D.signatur 0 with owner := handoff }

def consumeSignature : Signatur D.Tab D.Glob D.Lock D.Marke :=
  { D.signatur 0 with konsumiert := [(true, 0)] }

theorem checked_consume : RufPasst D contract consumeSignature [Res.marke true 0] where
  hw := fun _ h => h
  hg := fun g => nomatch g
  hk := ⟨[Res.marke true 0], List.Perm.refl _, List.Sublist.refl _⟩
  hh := fun L => nomatch L
  hx := fun L => nomatch L
  hb := by intro c h; cases h

theorem signature_valid_zeuge : OwnerSignature handoffSignature [true] where
  resolved := fun m hm => ⟨(), hm⟩
  valid := by decide
  ordinaryDisjoint := fun _ h => by cases h

theorem input_available_zeuge : Res.marke true 0 ∈ ([Res.marke true 0] : List (Res D)) :=
  checked_consume.input_available (by decide : (true, 0) ∈ consumeSignature.inputMarks)

theorem owner_nachSig_from_input_zeuge :
    ∃ before, Res.marke true before ∈ ([Res.marke true 0] : List (Res D)) :=
  owner_nachSig_from_input handoffSignature
    (fun m s ⟨t, ho⟩ => D.eigner_nie_erzeugt 0 t m s ho)
    [Res.marke true 0] (by
      intro p hp
      have he : p = (true, 0) := by simpa [handoffSignature, handoff, OwnerFlow.inputs] using hp
      subst p
      decide)
    ⟨(), by decide⟩ (by decide : Res.marke true 1 ∈ nachSig D handoffSignature [Res.marke true 0])

/-- The handoff flow is escrow-ready: valid over its mentioned identity,
    disjoint from ordinary consumption, with a declared eigner. -/
theorem escrow_handoff_ready_zeuge :
    handoffSignature.owner.EscrowReady
      (fun m => decide (m ∈ handoffSignature.owner.inputs.map Prod.fst))
      D.stufen (fun m => ∃ t, m ∈ D.eigner t) handoffSignature.konsumiert := by
  have e : (fun m => decide (m ∈ handoffSignature.owner.inputs.map Prod.fst)) = id := by
    funext m
    cases m <;> rfl
  rw [e]
  refine ⟨validB_iff_zeuge.2, ?_, ?_⟩
  · intro p hp
    have hk : handoffSignature.konsumiert = [] := rfl
    rw [hk] at hp
    exact (List.not_mem_nil p hp).elim
  · intro m hm
    have hm' : m = true := by
      simpa [handoffSignature, handoff, OwnerFlow.inputs] using hm
    subst hm'
    exact ⟨(), by decide⟩

/-- Static metadata IS now an admitted canonical owner call: with the input
    in hand, the escrow-ready handoff fits the contract. -/
theorem escrow_call_admitted_zeuge :
    RufPasst D contract handoffSignature [Res.marke true 0] where
  hw := fun t h => h
  hg := fun g => nomatch g
  hk := by
    have hi : handoffSignature.inputMarks = [(true, 0)] := rfl
    rw [hi]
    exact ⟨[Res.marke true 0], List.Perm.refl _, List.Sublist.refl _⟩
  hh := fun L => nomatch L
  hx := fun L => nomatch L
  hb := by intro c h; cases h
  ownerReady := escrow_handoff_ready_zeuge

/-- Without the input in hand the same call is refused: the escrow cannot
    move a binding the caller does not hold. -/
theorem escrow_call_missing_input_refused :
    ¬ RufPasst D contract handoffSignature [] := by
  intro h
  exact (List.not_mem_nil _ (h.owner_input_available (by decide))).elim

/-- The admitted call conserves owners: no duplication, and every returned
    owner has an explicit input. -/
theorem escrow_outputs_conserve_zeuge :
    (handoffSignature.owner.outputs.map Prod.fst).Nodup ∧
      (∀ m s, (m, s) ∈ handoffSignature.owner.outputs →
        ∃ before, (m, before) ∈ handoffSignature.owner.inputs) :=
  ⟨(OwnerFlow.escrow_outputs_conserve escrow_handoff_ready_zeuge).1,
    fun m s hm => (OwnerFlow.escrow_outputs_conserve escrow_handoff_ready_zeuge).2.1 m s hm⟩

/-- A moved owner can come back at the return: from the grandchild frame the
    transfer to the child frame succeeds with a fresh grant. -/
theorem escrow_move_return_exists_zeuge :
    ∃ s' t', OwnerState.transfer names movedTwice grandchild child movedTwiceToken =
      some (s', t') := by
  have hown := (OwnerState.transfer_grant mint_grant_zeuge.1 two_call_handoff).2.1
  obtain ⟨ledger', h', he⟩ := ArenaOwnership.State.move_exists hown.2.2 rfl
  have hne : grandchild ≠ child := by decide
  refine ⟨_, _, ?_⟩
  unfold OwnerState.transfer
  rw [if_pos ⟨hown, hne⟩, he]

theorem pointer_flow_mismatch_refused : ¬ SigPasst D.rang handoffSignature (D.signatur 0) := by
  intro h
  have he := congrArg OwnerFlow.inputs h.owner
  have impossible : [(true, 0)] = ([] : List (Bool × Nat)) := he
  cases impossible

theorem canonical_start_end_zeuge :
    Signatur.anfang D handoffSignature = [Res.marke true 0] ∧
    (Vertrag.vonSig D handoffSignature).ende = [Res.marke true 1] := ⟨rfl, rfl⟩

theorem owner_nachSig_ordinary_zeuge :
    Res.marke true 0 ∈ ([Res.marke true 0] : List (Res D)) :=
  owner_nachSig_ordinary (D.signatur 0)
    (fun m s ⟨t, ho⟩ => D.eigner_nie_erzeugt 0 t m s ho)
    rfl [Res.marke true 0] ⟨(), by decide⟩ (by decide)

theorem mint_step : OwnerState.recordMint names mint OwnerState.empty root = some (minted, token) := rfl

theorem mint_valid_zeuge : minted.Valid names :=
  OwnerState.mint_valid (OwnerState.empty_valid names) mint_step

theorem mint_grant_zeuge : minted.ledger.valid ∧ minted.owns names root token ∧
    minted.spent true = true ∧ minted.initial true = false :=
  OwnerState.mint_grant ArenaOwnership.State.empty_valid mint_step

theorem mint_spends_zeuge : minted.spent mint.mark = true := OwnerState.mint_spends mint_step

theorem mint_spent_refused_zeuge : OwnerState.recordMint names mint minted root = none :=
  OwnerState.mint_spent_refused names mint minted root mint_spends_zeuge

theorem nested_mint_refused : OwnerState.recordMint names mint OwnerState.empty child = none := rfl

theorem initial_plus_minted_refused :
    OwnerState.recordMint names mint { minted with initial := fun _ => true } root = none :=
  OwnerState.mint_initial_refused names mint _ root rfl

theorem transfer_step : OwnerState.transfer names minted root child token = some (moved, movedToken) := rfl

theorem transfer_grant_zeuge : moved.ledger.valid ∧ moved.owns names child movedToken ∧
    movedToken.mark = token.mark ∧ movedToken.stage = token.stage ∧
    (∀ frame, ¬ moved.access names frame token) ∧ moved.spent = minted.spent :=
  OwnerState.transfer_grant mint_grant_zeuge.1 transfer_step

theorem two_call_handoff :
    OwnerState.transfer names moved child grandchild movedToken = some (movedTwice, movedTwiceToken) := rfl

theorem cross_thread_move_refused : OwnerState.transfer names minted root foreignThread token = none := rfl

theorem borrow_step : OwnerState.borrow names minted root child token = some loaned := rfl

theorem borrow_grant_zeuge : loaned.ledger.valid ∧ loaned.access names child token ∧
    ¬ loaned.access names root token ∧ ¬ loaned.owns names child token ∧
    loaned.spent = minted.spent ∧ loaned.stage = minted.stage :=
  OwnerState.borrow_grant mint_grant_zeuge.1 borrow_step

theorem nested_borrow : OwnerState.borrow names loaned child grandchild token = some nested := rfl

theorem borrow_return_zeuge : OwnerState.returnBorrow names loaned child root token = some minted :=
  OwnerState.borrow_return mint_grant_zeuge.1 borrow_step

theorem nested_borrow_return : OwnerState.returnBorrow names nested grandchild child token = some loaned :=
  OwnerState.borrow_return borrow_grant_zeuge.1 nested_borrow

theorem borrower_restrictions_zeuge :
    OwnerState.retire names loaned child token = none ∧
    OwnerState.advance names loaned child token = none ∧
    OwnerState.transfer names loaned child grandchild token = none :=
  OwnerState.borrower_restrictions borrow_grant_zeuge.2.2.2.1 grandchild

theorem suspended_lender_refused : OwnerState.borrow names loaned root child token = none := rfl

theorem wrong_stage_return_refused :
    OwnerState.returnBorrow names loaned child root stageOneToken = none := rfl

theorem wrong_frame_return_refused : OwnerState.returnBorrow names nested child root token = none := rfl

theorem advance_step : OwnerState.advance names minted root token = some (stageOne, stageOneToken) := rfl

theorem advance_valid_zeuge : stageOne.Valid names :=
  OwnerState.advance_valid mint_valid_zeuge advance_step

theorem advance_grant_zeuge : stageOne.owns names root stageOneToken ∧ stageOneToken.mark = token.mark ∧
    stageOneToken.stage = token.stage + 1 ∧ stageOne.spent = minted.spent ∧
    (∀ frame, ¬ stageOne.access names frame token) := OwnerState.advance_grant advance_step

theorem retire_step : OwnerState.retire names minted root token = some retired := rfl

theorem retire_grant_zeuge : retired.ledger.valid ∧
    (∀ frame, ¬ retired.access names frame token) ∧ retired.spent = minted.spent :=
  OwnerState.retire_grant mint_grant_zeuge.1 retire_step

theorem retire_cannot_remint_zeuge : OwnerState.recordMint names mint retired root = none :=
  OwnerState.retire_cannot_remint mint_grant_zeuge.1 mint_spends_zeuge retire_step root

#print axioms owner_nachSig_from_input_zeuge
#print axioms mint_valid_zeuge
#print axioms transfer_grant_zeuge
#print axioms nested_borrow_return
#print axioms retire_cannot_remint_zeuge

end Gabbro.Grammatik.OwnerWitness
