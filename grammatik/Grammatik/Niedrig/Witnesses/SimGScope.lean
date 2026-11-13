module

public import Grammatik.Niedrig.Authority.SimGMachine
public import Grammatik.Kern.Syntax.Marken.Owner.EscrowRun

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.ScopeWitness

open EscrowWitness

abbrev D := escrowD

/-- Reuse the actual C09 call run, not a fabricated pair of machine states. -/
def space : Space D :=
  { nominal := 0
    backing := 0
    width := 1
    kind := .physical
    declared := (by change 0 < 1; omega)
    positiveWidth := (by omega) }

def rights : DataRights :=
  { read := true
    write := false
    owner := none }

def span : Span D :=
  { space := space
    base := 0
    length := 1
    table := ()
    number := 0
    rights := rights
    execute := false
    memoryClass := .ordinaryRam
    owner := true
    epoch := 0
    alignment := 1
    mapped := true
    initialized := true }

def authority : Authority D :=
  { names := escrowNames
    token := tokenE
    spans := [span]
    epoch := 0 }

def initial : Context D Unit Unit :=
  { owners := mintedE
    frame := callerF
    views := []
    privilege := ()
    interrupt := () }

theorem authority_valid : authority.Valid := by
  refine ⟨⟨(), List.mem_cons_self ..⟩, ?_, ?_, ?_⟩
  · change 0 < 3
    omega
  · intro s member
    change s ∈ [span] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst s
    exact ⟨⟨by change 0 < 1; omega, by change 0 + 1 ≤ 2 ^ 1; omega,
      by change 0 < 1; omega, rfl⟩, rfl, by change 0 ≤ 0; omega⟩
  · exact List.Pairwise.cons (fun _ h => False.elim (List.not_mem_nil h)) .nil

theorem initial_valid : initial.Valid authority := by
  have owner := mintGrantE.2.1
  refine ⟨authority_valid, mintGrantE.1, ?_, ?_, ?_⟩
  · exact ⟨owner.1, owner.2.1, ArenaOwnership.State.owner_access owner.2.2⟩
  · intro v member
    cases member
  · intro v member
    cases member

def start : Address space := ⟨⟨0, by omega, by change 0 ≤ 2 ^ 1 - 1; omega⟩⟩

def view : View D :=
  { span := span
    base := 0
    length := 1
    rights := rights
    lender := callerF
    borrower := calleeF
    epoch := 0 }

def receipt : ViewResult authority initial :=
  { view := view
    admission :=
      { span := List.mem_cons_self ..
        owner := rfl
        epoch := ⟨rfl, rfl⟩
        lender := rfl
        bounds := ⟨by change 0 ≤ 0; omega, by change 0 + 1 ≤ 0 + 1; omega⟩
        memoryClass := rfl
        permissions := ⟨.inl rfl, fun _ => rfl, fun h => h, rfl⟩
        alignment := ⟨by change 0 < 1; omega, rfl, rfl⟩
        mapping := rfl
        initialization := rfl
        compatible := (by intro w member; cases member) }
    owners := loanedE
    borrowed := borrowStepE }

theorem produced : ram_view authority initial start 1 rights calleeF = .ok receipt := rfl

def beforeBindings : OwnerBindings D.Marke :=
  [{ binder := 10
     mark := true
     stage := 0 }]

def afterBindings : OwnerBindings D.Marke :=
  [{ binder := 11
     mark := true
     stage := 0 }]

def scope : BorrowScopePremises authority initial receipt progE orakelE 0 M0E M1E :=
  { invocation := invocE
    push := pushE
    caller := invocCallerE
    borrower := invocFrameE
    linear :=
      { protocol := .ram start 1 rights calleeF receipt produced
        before := beforeBindings
        after := afterBindings
        source := 10
        into := 11
        bound := List.mem_cons_self ..
        moved := rfl }
    beforeBindings := (by
      intro resource member
      change resource ∈ [Res.marke true 0] at member
      change resource ∈ (M0E.faeden 0).kopf.rest.2.2.1
      rw [M0E_kopf]
      exact member)
    afterBindings := (by
      intro resource member
      change resource ∈ [Res.marke true 0] at member
      change resource ∈ (M1E.faeden 0).kopf.rest.2.2.1
      rw [M1E_kopf]
      exact member)
    world := rfl
    heldBefore := (by intro lock; exact lock.elim)
    heldAfter := (by intro lock; exact lock.elim) }

/-- All scope premises coexist with a successful ram_view and an actual G
    push; the loan changes the accessor while G's world and locks stay fixed. -/
theorem borrow_scope_sim_zeuge :
    RufSchrittG progE orakelE 0 M0E 0 M1E ∧
    scope.push.borrow authority.names initial.owners authority.token = some receipt.next.owners ∧
    SimRel authority receipt.next (M1E.weltVon 0) ∧ SpurInv M1E ∧
    HeldIn (M1E.faeden 0).kopf.rest.2.2.1 (M1E.weltVon 0).haelt :=
  borrow_scope_sim start 1 rights calleeF receipt produced scope
    (simRel_initial initial_valid rfl (M0E.weltVon 0))
    (spurInv_start progE spE initE)

/-- The same invocation has a real canonical pop and restores exactly this
    loan. This is the ledger/world roundtrip, not a theorem accepting every
    source view scope or either arbitrary error continuation. -/
theorem scope_return_zeuge :
    RufSchrittG progE orakelE 0 M1E 0 M2E ∧
    returnView authority receipt.next = .ok initial ∧
    popE.restore authority.names receipt.next.owners authority.token = some initial.owners ∧
    M2E.weltVon 0 = M1E.weltVon 0 ∧ SimRel authority initial (M2E.weltVon 0) := by
  have returned := ram_view_return initial_valid receipt
  have restored : SimRel authority initial (M1E.weltVon 0) :=
    returnView_sim borrow_scope_sim_zeuge.2.2.1 returned
  exact ⟨schrittPopE, returned,
    OwnerState.borrow_return mintGrantE.1 receipt.borrowed, rfl, restored⟩

end Gabbro.Grammatik.LowLevel.ScopeWitness
