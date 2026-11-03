module

public import Grammatik.Kern.Syntax.Marken.Owner.EscrowRun
public import Grammatik.Kern.Syntax.Marken.Owner.Escrow
public import Grammatik.Kern.Syntax.Marken.Owner.Ledger

@[expose] public section

namespace Gabbro.Grammatik.EscrowWitness

/-! ## Escrow call/return witnesses on the shared fixture

    Every C09 escrow call/return theorem with a ∀-over-syntax premise,
    instantiated on the shared fixture (`escrowD`, one owner mark, one
    caller, one callee): the push authorizes the borrow/transfer, the
    return restores it, and the ghost ledger is preserved across both
    steps. Each premise is discharged, none assumed. -/

/-- The start machine carries the minted base ledger. -/
theorem baseStartE : OwnerInvG escrowNames mintedE M0E [0] :=
  ownerInvG_start escrowNames mintedE progE spE initE [0] mintedValidE

/-- A canonical call push borrowing the loan: the callee frame gains the
    only accessor, the lender loses access, stages and spent authority
    are untouched. -/
theorem escrow_call_borrow_zeuge :
    loanedE.ledger.valid ∧ loanedE.access escrowNames calleeF tokenE ∧
    ¬ loanedE.access escrowNames callerF tokenE ∧
    ¬ loanedE.owns escrowNames calleeF tokenE ∧
    loanedE.spent = mintedE.spent ∧ loanedE.stage = mintedE.stage :=
  escrow_call_borrow pushE mintGrantE.1 borrowStepE

/-- A canonical call push transferring the loan: the callee frame gains a
    fresh grant for the same owner, every saved use of the old grant dies. -/
theorem escrow_call_transfer_zeuge :
    movedE.ledger.valid ∧ movedE.owns escrowNames calleeF movedTokenE ∧
    movedTokenE.mark = tokenE.mark ∧ movedTokenE.stage = tokenE.stage ∧
    (∀ frame, ¬ movedE.access escrowNames frame tokenE) ∧
    movedE.spent = mintedE.spent :=
  escrow_call_transfer pushE mintGrantE.1 transferStepE

/-- Preservation across the call push carrying escrow. -/
theorem escrow_push_preserved_zeuge : OwnerInvG escrowNames mintedE M1E [0] :=
  escrow_push_preserved pushE baseStartE

/-- Loans restore exactly: the checked borrow has its inverse at the
    matching return. -/
theorem escrow_loan_roundtrip_zeuge :
    popE.restore escrowNames loanedE tokenE = some mintedE :=
  escrow_loan_roundtrip pushE popE mintGrantE.1 borrowStepE

/-- A canonical return restoring the loan: precisely the saved identity
    and stage come back to the lender, on the normal channel. -/
theorem escrow_return_restore_zeuge :
    mintedE.ledger.valid ∧ mintedE.access escrowNames callerF tokenE ∧
    mintedE.spent = loanedE.spent ∧ mintedE.stage = loanedE.stage :=
  escrow_return_restore popE loanedGrantE.1 escrow_loan_roundtrip_zeuge

/-- A moved owner comes back at the return: the transfer computes. -/
theorem transferBackE : ∃ s' t',
    OwnerState.transfer escrowNames movedE calleeF callerF movedTokenE =
      some (s', t') :=
  ⟨_, _, rfl⟩

/-- A canonical return handing the moved owner back: a fresh grant for
    the same nominal identity at the lender. -/
theorem escrow_return_transfer_zeuge :
    ∃ s' t', s'.ledger.valid ∧ s'.owns escrowNames callerF t' ∧
    t'.mark = movedTokenE.mark ∧ t'.stage = movedTokenE.stage ∧
    (∀ frame, ¬ s'.access escrowNames frame movedTokenE) ∧
    s'.spent = movedE.spent := by
  obtain ⟨s', t', hback⟩ := transferBackE
  exact ⟨s', t', escrow_return_transfer popE movedGrantE.1 hback⟩

/-- A stage-changing move advances at the callee before the handoff back. -/
theorem advanceE : ∃ s' t',
    OwnerState.advance escrowNames movedE calleeF movedTokenE = some (s', t') :=
  ⟨_, _, rfl⟩

/-- The advance hands the same identity at the next stage, with the old
    stage unusable in every frame. -/
theorem escrow_return_advance_zeuge :
    ∃ s' t', s'.owns escrowNames calleeF t' ∧ t'.mark = movedTokenE.mark ∧
    t'.stage = movedTokenE.stage + 1 ∧ s'.spent = movedE.spent ∧
    (∀ frame, ¬ s'.access escrowNames frame movedTokenE) := by
  obtain ⟨s', t', hadv⟩ := advanceE
  exact ⟨s', t', escrow_return_advance hadv⟩

/-- A terminal move retires at the return: the grant computes away. -/
theorem retireE : ∃ s',
    OwnerState.retire escrowNames movedE calleeF movedTokenE = some s' :=
  ⟨_, rfl⟩

/-- The retirement keeps the ledger valid, leaves no accessor, and keeps
    mint authority spent. -/
theorem escrow_return_retire_zeuge :
    ∃ s', s'.ledger.valid ∧
    (∀ frame, ¬ s'.access escrowNames frame movedTokenE) ∧
    s'.spent = movedE.spent := by
  obtain ⟨s', hret⟩ := retireE
  exact ⟨s', escrow_return_retire movedGrantE.1 hret⟩

/-- Preservation across the canonical return carrying escrow. -/
theorem escrow_pop_preserved_zeuge : OwnerInvG escrowNames mintedE M2E [0] :=
  escrow_pop_preserved popE escrow_push_preserved_zeuge

/-- The admitted call conserves owners, in full: no duplication, every
    returned owner has an explicit input, every returned stage is in range. -/
theorem escrow_outputs_conserve_full_zeuge :
    (escrowSig.owner.outputs.map Prod.fst).Nodup ∧
    (∀ m s, (m, s) ∈ escrowSig.owner.outputs →
      ∃ before, (m, before) ∈ escrowSig.owner.inputs) ∧
    (∀ m s, (m, s) ∈ escrowSig.owner.outputs →
      (fun m => decide (m ∈ escrowSig.owner.inputs.map Prod.fst)) m = true ∧
        s < escrowD.stufen m) :=
  OwnerFlow.escrow_outputs_conserve escrowReadyE

/-- The admitted call supplies its concrete owner input. -/
theorem escrow_call_ready_run_zeuge :
    Res.vonMarke escrowD (true, 0) ∈ anfE :=
  escrow_call_ready hpE (by decide)

/-- The returned stage is present after the same admitted call. -/
theorem escrow_call_outputs_present_run_zeuge :
    Res.marke true 0 ∈ nachSig escrowD escrowSig anfE :=
  escrow_call_outputs_present escrowSig anfE (by decide)

/-- The ledger engine behind the borrow edge, on the same push. -/
theorem push_borrow_valid_run_zeuge :
    loanedE.ledger.valid ∧ loanedE.access escrowNames calleeF tokenE ∧
    ¬ loanedE.access escrowNames callerF tokenE ∧
    ¬ loanedE.owns escrowNames calleeF tokenE ∧
    loanedE.spent = mintedE.spent ∧ loanedE.stage = mintedE.stage :=
  push_borrow_valid pushE mintGrantE.1 borrowStepE

/-- The ledger engine behind the transfer edge, on the same push. -/
theorem push_transfer_valid_run_zeuge :
    movedE.ledger.valid ∧ movedE.owns escrowNames calleeF movedTokenE ∧
    movedTokenE.mark = tokenE.mark ∧ movedTokenE.stage = tokenE.stage ∧
    (∀ frame, ¬ movedE.access escrowNames frame tokenE) ∧
    movedE.spent = mintedE.spent :=
  push_transfer_valid pushE mintGrantE.1 transferStepE

/-- The ledger engine behind the restore edge, on the same return. -/
theorem pop_restore_valid_run_zeuge :
    mintedE.ledger.valid ∧ mintedE.access escrowNames callerF tokenE ∧
    mintedE.spent = loanedE.spent ∧ mintedE.stage = loanedE.stage :=
  pop_restore_valid popE loanedGrantE.1 escrow_loan_roundtrip_zeuge

/-- The ledger roundtrip behind the loan, on the same push and return. -/
theorem push_borrow_pop_restore_run_zeuge :
    popE.restore escrowNames loanedE tokenE = some mintedE :=
  push_borrow_pop_restore pushE popE mintGrantE.1 borrowStepE

/-- Projections of the checked escrow condition, on the fixture flow. -/
theorem escrowReady_valid_run_zeuge :
    escrowLoan.Valid (fun m => decide (m ∈ escrowLoan.inputs.map Prod.fst))
      escrowD.stufen :=
  escrowReady_valid escrowReadyE

theorem escrowReady_disjoint_run_zeuge :
    ∀ p ∈ ([] : List (Bool × Nat)), p.1 ∉ escrowLoan.inputs.map Prod.fst :=
  escrowReady_disjoint escrowReadyE

theorem escrowReady_resolved_run_zeuge :
    ∀ m ∈ escrowLoan.inputs.map Prod.fst, ∃ t, m ∈ escrowD.eigner t :=
  escrowReady_resolved escrowReadyE

theorem escrowReady_congr_run_zeuge :
    escrowLoan.EscrowReady
      (fun m => decide (m ∈ escrowLoan.inputs.map Prod.fst))
      escrowD.stufen (fun m => ∃ t, m ∈ escrowD.eigner t) [] :=
  escrowReady_congr rfl escrowReadyE

/-- Reachability of both edges from the start state. -/
theorem reachPushE : RufErreichbarG progE orakelE 0 M0E M1E :=
  RufErreichbarG.schritt _ _ 0 RufErreichbarG.start schrittPushE

theorem reachPopE : RufErreichbarG progE orakelE 0 M0E M2E :=
  RufErreichbarG.schritt _ _ 0 reachPushE schrittPopE

/-- Every machine this run reaches keeps the ghost ledger valid. -/
theorem ownerInvG_erreichbar_zeuge : OwnerInvG escrowNames mintedE M2E [0] :=
  ownerInvG_erreichbar escrowNames mintedE progE orakelE 0 M0E [0]
    mintedValidE M2E reachPopE

#print axioms escrow_loan_roundtrip_zeuge
#print axioms escrow_push_preserved_zeuge
#print axioms escrow_pop_preserved_zeuge

end Gabbro.Grammatik.EscrowWitness
