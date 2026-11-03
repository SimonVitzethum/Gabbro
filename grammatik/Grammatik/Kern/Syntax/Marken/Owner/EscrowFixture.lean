module

public import Grammatik.Kern.Syntax.Marken.Owner.Conservation
public import Grammatik.Kern.Syntax.Syntax.Teil2

@[expose] public section

namespace Gabbro.Grammatik.EscrowWitness

/-! ## Shared C09 escrow fixture: one owner mark, caller escrows to callee

    `escrowD` is usable by both sides of the escrow: the owner checker side
    (`ArenaOwnership`, `OwnerFlow`, the escrow lemmas under
    `Bausteine/Arena/Ownership/` and `Marken/Owner/`) and the call machine G
    (a concrete `RufMaschineG` run with exactly one push and one return lives
    in `EscrowRun.lean`). The declaration carries one owner mark (`true`,
    three stages), one guarded table, and two functions sharing one
    signature: `false` is the caller, `true` the callee. Both signatures hold
    the same nominal loan (`escrowLoan`): the caller starts with the owner in
    hand, the call moves it into the callee frame escrow, and the return
    gives back exactly that identity at the same stage. No ordinary
    signature produces an owner. -/

/-- The escrowed owner: a nominal loan, same stage back on either channel. -/
@[expose, reducible] def escrowLoan : OwnerFlow Bool := { loans := [(true, 0)] }

/-- The one shared signature: no params, no result, holds the loaned owner. -/
@[expose, reducible] def escrowSig : Signatur Unit Empty Empty Bool where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []
  boden := none
  owner := escrowLoan

/-- The witness declaration: one table `Unit` with one field, no locks, no
    globals, one owner mark with three stages, two functions sharing the
    loan signature above. `false` calls, `true` is entered. -/
@[expose, reducible] def escrowD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 5
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Bool
  decMarke := inferInstance
  stufen := fun _ => 3
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => [true]
  Fn := Bool
  sig := fun _ => 0
  sigNr := fun _ => escrowSig
  eigner_nie_erzeugt := fun _ _ _ _ _ h => List.not_mem_nil h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => none
  aschreibt := fun _ _ => false
  agschreibt := fun _ e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp only [Bool.false_eq_true] at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- Every function takes no parameters (both share the loan signature). -/
theorem escrowParams (f : escrowD.Fn) : escrowD.params f = [] := by
  cases f <;> rfl

/-- Every function answers nothing (the return carries only the owner). -/
theorem escrowErg (f : escrowD.Fn) : escrowD.erg f = none := by
  cases f <;> rfl

/-- The caller and callee identities. -/
@[expose, reducible] def callerFn : escrowD.Fn := false

@[expose, reducible] def calleeFn : escrowD.Fn := true

/-- The nominal namespace: the one mark against the grant ledger. -/
@[expose, reducible] def escrowNames : OwnerNamespace escrowD where
  key := fun m => if m then 0 else 1
  injective := by intro a b h; cases a <;> cases b <;> simp_all

/-- The distinguished mint: `true` at stage 0, issued for the caller. -/
@[expose, reducible] def escrowMint : OwnerMintDecl escrowD where
  mark := true
  minter := ()
  root := false
  site := 7
  stage := 0
  owner := ⟨(), by decide⟩
  bounded := by decide

/-- The caller and callee activation identities of the witness run. -/
@[expose, reducible] def callerF : ArenaOwnership.Frame := ⟨0, 0⟩

@[expose, reducible] def calleeF : ArenaOwnership.Frame := ⟨0, 1⟩

@[expose, reducible] def tokenE : OwnerToken escrowD := ⟨true, 0, ⟨0, 0, 0⟩⟩

@[expose, reducible] def mintedLedgerE : ArenaOwnership.State :=
  { (ArenaOwnership.State.empty.put 0 (some ⟨0, 0, callerF, []⟩)) with next := 1 }

@[expose, reducible] def mintedE : OwnerState escrowD :=
  { OwnerState.empty with
    ledger := mintedLedgerE
    spent := fun m => if m = true then true else false
    stage := fun m => if m = true then 0 else 0 }

@[expose, reducible] def loanedE : OwnerState escrowD := mintedE.withLedger
  (mintedLedgerE.put 0 (some ⟨0, 0, callerF, [calleeF]⟩))

@[expose, reducible] def movedLedgerE : ArenaOwnership.State :=
  { (mintedLedgerE.put 0 (some ⟨0, 1, calleeF, []⟩)) with next := 2 }

@[expose, reducible] def movedE : OwnerState escrowD := mintedE.withLedger movedLedgerE

@[expose, reducible] def movedTokenE : OwnerToken escrowD := { tokenE with handle := ⟨0, 0, 1⟩ }

theorem mintStepE : OwnerState.recordMint escrowNames escrowMint
    OwnerState.empty callerF = some (mintedE, tokenE) := rfl

theorem mintedValidE : mintedE.Valid escrowNames :=
  OwnerState.mint_valid (OwnerState.empty_valid escrowNames) mintStepE

theorem mintGrantE : mintedE.ledger.valid ∧ mintedE.owns escrowNames callerF tokenE ∧
    mintedE.spent true = true ∧ mintedE.initial true = false :=
  OwnerState.mint_grant ArenaOwnership.State.empty_valid mintStepE

theorem borrowStepE : OwnerState.borrow escrowNames mintedE callerF calleeF tokenE =
    some loanedE := rfl

theorem loanedGrantE : loanedE.ledger.valid ∧ loanedE.access escrowNames calleeF tokenE ∧
    ¬ loanedE.access escrowNames callerF tokenE ∧ ¬ loanedE.owns escrowNames calleeF tokenE ∧
    loanedE.spent = mintedE.spent ∧ loanedE.stage = mintedE.stage :=
  OwnerState.borrow_grant mintGrantE.1 borrowStepE

theorem transferStepE : OwnerState.transfer escrowNames mintedE callerF calleeF tokenE =
    some (movedE, movedTokenE) := rfl

theorem movedGrantE : movedE.ledger.valid ∧ movedE.owns escrowNames calleeF movedTokenE ∧
    movedTokenE.mark = tokenE.mark ∧ movedTokenE.stage = tokenE.stage ∧
    (∀ frame, ¬ movedE.access escrowNames frame tokenE) ∧ movedE.spent = mintedE.spent :=
  OwnerState.transfer_grant mintGrantE.1 transferStepE

/-- The loan flow is escrow-ready: valid over its mentioned identity,
    disjoint from ordinary consumption, with a declared eigner. -/
theorem escrowReadyE : escrowLoan.EscrowReady
    (fun m => decide (m ∈ escrowLoan.inputs.map Prod.fst))
    escrowD.stufen (fun m => ∃ t, m ∈ escrowD.eigner t) [] := by
  have e : (fun m => decide (m ∈ escrowLoan.inputs.map Prod.fst)) = id := by
    funext m
    cases m <;> rfl
  rw [e]
  refine ⟨(OwnerFlow.validB_iff _ _ _).mp (by decide), ?_, ?_⟩
  · intro p hp
    exact (List.not_mem_nil hp).elim
  · intro m hm
    have hm' : m = true := by
      simpa [escrowLoan, OwnerFlow.inputs] using hm
    subst hm'
    exact ⟨(), by decide⟩

end Gabbro.Grammatik.EscrowWitness
