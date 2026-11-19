/-
  Subject: Satisfiability of the owner premises (stream E3, owner rule of 2026-11-19).

  * `owner_erfuellbar`: a valid owner state, a mint of the declared owner mark, and a borrow and a transfer of the
    minted token into a second frame are jointly defined -- the premises of the conservation lemmas of
    `Owner/Conservation.lean` hold together.
  * `owner_aufruf_erfuellbar`: an owner invocation with a real push and a real return of machine G, in distinct
    caller and callee frames -- the premises of the dynamic escrow lemmas of `Owner/Escrow.lean` hold together.
-/
module

public import Grammatik.Kern.Syntax.Marken.Owner.EscrowRun

@[expose] public section

namespace Gabbro.Grammatik.EscrowWitness

/-- **Satisfiability of the owner-state premises**: from the empty valid state a mint is recorded, the result is
    valid, and the minted token can be both borrowed and transferred into a second frame. -/
theorem owner_erfuellbar :
    ∃ (D : Deklaration) (N : OwnerNamespace D) (d : OwnerMintDecl D) (s : OwnerState D) (t : OwnerToken D)
      (caller callee : ArenaOwnership.Frame),
      OwnerState.recordMint N d OwnerState.empty caller = some (s, t) ∧ s.Valid N ∧ s.owns N caller t ∧
      caller ≠ callee ∧
      (∃ loaned, OwnerState.borrow N s caller callee t = some loaned ∧ loaned.access N callee t) ∧
      (∃ moved token, OwnerState.transfer N s caller callee t = some (moved, token) ∧
        moved.owns N callee token) :=
  ⟨escrowD, escrowNames, escrowMint, mintedE, tokenE, callerF, calleeF, mintStepE, mintedValidE,
    mintGrantE.2.1, by decide, ⟨loanedE, borrowStepE, loanedGrantE.2.1⟩,
    ⟨movedE, movedTokenE, transferStepE, movedGrantE.2.1⟩⟩

/-- **Satisfiability of the invocation premises**: an owner invocation whose push and return are steps of machine
    G, with distinct caller and callee frames. -/
theorem owner_aufruf_erfuellbar :
    ∃ (c : OwnerInvocation escrowD) (M M' M'' : RufMaschineG escrowD),
      c.Push progE orakelE 0 M M' ∧ Nonempty (c.Return progE orakelE 0 M' M'') ∧ c.caller ≠ c.frame :=
  ⟨invocE, M0E, M1E, M2E, pushE, ⟨popE⟩, by rw [invocCallerE, invocFrameE]; decide⟩

end Gabbro.Grammatik.EscrowWitness
