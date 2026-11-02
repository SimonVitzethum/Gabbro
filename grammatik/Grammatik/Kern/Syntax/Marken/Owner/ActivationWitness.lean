module

public import Grammatik.Kern.Syntax.Marken.Owner.Activation
public import Grammatik.Kern.Syntax.Marken.Owner.InvocationFlow
public import Grammatik.Kern.Syntax.Marken.Owner.Fixture
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T6
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T6a

@[expose] public section

namespace Gabbro.Grammatik.OwnerActivationWitness

/-- Reuse the canonical writing-call fixture; this is not an owner minter or
    an owner-flow admission witness. The callee changes actual table memory. -/
def invocation : OwnerInvocation rufDF where
  thread := 0
  before := (M0G.faeden 0).log
  callee := rufIncF
  arguments := rufRhoF
  entry := M0G.weltVon 0
  parent := 0
  ancestors := []
  active := rfl

theorem opened_active_zeuge : ownerActivations invocation.opened = [1, 0] :=
  invocation.opened_active

theorem different_frames_zeuge : invocation.caller ≠ invocation.frame :=
  invocation.different_frames

theorem push_zeuge : invocation.Push gP rufOF 0 M0G M1G where
  step := schritt1G
  beforeLog := rfl
  afterLog := rfl
  key := rfl
  stack := rfl

def return_zeuge : invocation.Return gP rufOF 0 M6G M7G where
  step := schritt7G
  nested := []
  event := .rueck rufIncF rufRhoF vF (M0G.weltVon 0) s1G
  beforeLog := rfl
  active := rfl
  outcome := Or.inl ⟨vF, s1G, rfl⟩
  afterLog := rfl
  stack := rfl

theorem restores_stack_zeuge :
    ownerActivations (M7G.faeden 0).log = ownerActivations invocation.before :=
  return_zeuge.restores_stack

/-- The exact same callee, argument environment and entry world may be called
    again. Its invocation serial is three, not the reused stack depth one. -/
def repeated : OwnerInvocation rufDF where
  thread := 0
  before := (M7G.faeden 0).log
  callee := rufIncF
  arguments := rufRhoF
  entry := M0G.weltVon 0
  parent := 0
  ancestors := []
  active := rfl

theorem repeated_equal_key_distinct_frames :
    repeated.callee = invocation.callee ∧ repeated.arguments = invocation.arguments ∧
    repeated.entry = invocation.entry ∧ repeated.frame ≠ invocation.frame ∧
    repeated.frame.activation = 3 := by
  refine ⟨rfl, rfl, rfl, ?_, rfl⟩
  intro he
  have impossible : (3 : Nat) = 1 := congrArg ArenaOwnership.Frame.activation he
  cases impossible

theorem ownerActivations_bounded_zeuge :
    ∀ n ∈ ownerActivations (M6G.faeden 0).log, n < (M6G.faeden 0).log.length :=
  ownerActivations_bounded _

theorem ownerActivations_nodup_zeuge : (ownerActivations (M6G.faeden 0).log).Nodup :=
  ownerActivations_nodup _

theorem ownerActivations_fresh_zeuge :
    (M7G.faeden 0).log.length ∉ ownerActivations (M7G.faeden 0).log :=
  ownerActivations_fresh _

/-- Check log annotation against the actual canonical log/stack invariant,
    on the same nonempty writing-call run used by push and return above. -/
theorem ownerActivations_length_zeuge :
    (ownerActivations (M6G.faeden 0).log).length = (RufFadenSchluesselG (M6G.faeden 0)).length :=
  ownerActivations_length (rufErreichbarG_passt gP rufOF 0 spF initF M6G reach6G 0)

/-- Generalized ledger operations accept real log serials with gaps, while
    the call-edge judgments above supply the actual invocation authorization. -/
def laterFrame : ArenaOwnership.Frame := ⟨0, 3⟩

theorem nonadjacent_transfer_zeuge :
    ∃ s t, OwnerState.transfer OwnerWitness.names OwnerWitness.minted OwnerWitness.root laterFrame
      OwnerWitness.token = some (s, t) := by
  refine ⟨OwnerWitness.minted.withLedger
    { (OwnerWitness.mintedLedger.put 0 (some ⟨0, 1, laterFrame, []⟩)) with next := 2 },
    { OwnerWitness.token with handle := ⟨0, 0, 1⟩ }, rfl⟩

theorem nonadjacent_borrow_return_zeuge :
    ∃ loaned, OwnerState.borrow OwnerWitness.names OwnerWitness.minted OwnerWitness.root laterFrame
      OwnerWitness.token = some loaned ∧
    OwnerState.returnBorrow OwnerWitness.names loaned laterFrame OwnerWitness.root OwnerWitness.token =
      some OwnerWitness.minted := by
  let loaned := OwnerWitness.minted.withLedger
    (OwnerWitness.mintedLedger.put 0 (some ⟨0, 0, OwnerWitness.root, [laterFrame]⟩))
  have hb : OwnerState.borrow OwnerWitness.names OwnerWitness.minted OwnerWitness.root laterFrame
      OwnerWitness.token = some loaned := rfl
  exact ⟨loaned, hb, OwnerState.borrow_return
    (OwnerState.mint_grant ArenaOwnership.State.empty_valid (by rfl :
      OwnerState.recordMint OwnerWitness.names OwnerWitness.mint OwnerState.empty OwnerWitness.root =
        some (OwnerWitness.minted, OwnerWitness.token))).1 hb⟩

#print axioms push_zeuge
#print axioms return_zeuge
#print axioms ownerActivations_length_zeuge

end Gabbro.Grammatik.OwnerActivationWitness
