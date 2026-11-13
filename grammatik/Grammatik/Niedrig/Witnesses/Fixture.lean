module

public import Grammatik.Niedrig.Authority.Layout
public import Grammatik.Niedrig.Boot.Preservation
public import Grammatik.Kern.Syntax.Marken.Owner.Fixture

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Witness

abbrev D := OwnerWitness.D

inductive Privilege where
  | firmware
  | user
  deriving DecidableEq, Repr

/-- Explicit fields avoid positional construction of defaulted access flags. -/
def readWriteRights : DataRights :=
  { read := true
    write := true
    owner := none }

def readOnlyRights : DataRights :=
  { read := true
    write := false
    owner := none }

def space : Space D :=
  { nominal := 0
    backing := 0
    width := 8
    kind := .physical
    declared := (by change 0 < 1; omega)
    positiveWidth := (by omega) }

def ram : Span D :=
  { space := space
    base := 100
    length := 8
    table := ()
    number := 0
    rights := readWriteRights
    execute := false
    memoryClass := .ordinaryRam
    owner := true
    epoch := 2
    alignment := 1
    mapped := true
    initialized := true }

def device : Span D :=
  { ram with
    base := 108
    rights := readOnlyRights
    memoryClass := .device }

def authority : Authority D :=
  { names := OwnerWitness.names
    token := OwnerWitness.token
    spans := [ram, device]
    epoch := 2 }

/-- The same existing grant ledger, with an initial firmware origin rather
    than a software-mint origin. No mint operation is added to the protocol. -/
def initialOwners : OwnerState D :=
  { ledger := OwnerWitness.mintedLedger
    initial := fun m => m
    spent := fun _ => false
    stage := fun _ => 0 }

def initial : Context D Privilege Bool :=
  { owners := initialOwners
    frame := OwnerWitness.root
    views := []
    privilege := .firmware
    interrupt := true }

theorem authority_valid : authority.Valid := by
  refine ⟨⟨(), ?_⟩, ?_, ?_, ?_⟩
  · change true ∈ [true]
    exact List.mem_cons_self
  · change 0 < 3
    omega
  · intro span member
    change span ∈ [ram, device] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨⟨(by change 0 < 8; omega), (by change 100 + 8 ≤ 2 ^ 8; omega),
        (by change 0 < 1; omega), rfl⟩, rfl, (by change 2 ≤ 2; omega)⟩
    · exact ⟨⟨(by change 0 < 8; omega), (by change 108 + 8 ≤ 2 ^ 8; omega),
        (by change 0 < 1; omega), rfl⟩, rfl, (by change 2 ≤ 2; omega)⟩
  · apply List.Pairwise.cons
    · intro span member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst span
      right
      left
      change 100 + 8 ≤ 108
      omega
    · exact List.Pairwise.cons (fun _ h => absurd h List.not_mem_nil) .nil

theorem initial_ledger_valid : initialOwners.ledger.valid :=
  (OwnerState.mint_grant (D := D) ArenaOwnership.State.empty_valid
    (show OwnerState.recordMint OwnerWitness.names OwnerWitness.mint OwnerState.empty OwnerWitness.root =
      some (OwnerWitness.minted, OwnerWitness.token) from rfl)).1

theorem initial_owned : initialOwners.owns authority.names initial.frame authority.token :=
  ⟨rfl, rfl, ⟨⟨rfl, rfl⟩, rfl, rfl⟩⟩

theorem initial_valid : initial.Valid authority := by
  refine ⟨authority_valid, initial_ledger_valid, ?_, ?_, ?_⟩
  · exact ⟨initial_owned.1, initial_owned.2.1,
      ArenaOwnership.State.owner_access (s := initialOwners.ledger)
        (f := initial.frame) (h := authority.token.handle) initial_owned.2.2⟩
  · intro v member
    cases member
  · intro v member
    cases member

def start : Address space := ⟨⟨100, by omega, by change 100 ≤ 2 ^ 8 - 1; omega⟩⟩
def deviceStart : Address space := ⟨⟨108, by omega, by change 108 ≤ 2 ^ 8 - 1; omega⟩⟩

def writableView : View D :=
  { span := ram
    base := 100
    length := 4
    rights := readWriteRights
    lender := OwnerWitness.root
    borrower := OwnerWitness.child
    epoch := 2 }

def writableAdmission : ViewAdmission authority initial writableView :=
  { span := List.mem_cons_self ..
    owner := rfl
    epoch := ⟨rfl, rfl⟩
    lender := rfl
    bounds := ⟨(by change 100 ≤ 100; omega), (by change 100 + 4 ≤ 100 + 8; omega)⟩
    memoryClass := rfl
    permissions := ⟨.inl rfl, fun _ => rfl, fun _ => rfl, rfl⟩
    alignment := ⟨(by change 0 < 1; omega), rfl, rfl⟩
    mapping := rfl
    initialization := rfl
    compatible := (by intro w member; cases member) }

def borrowedOwners : OwnerState D :=
  initialOwners.withLedger (OwnerWitness.mintedLedger.put 0
    (some ⟨0, 0, OwnerWitness.root, [OwnerWitness.child]⟩))

def writableResult : ViewResult authority initial :=
  { view := writableView
    admission := writableAdmission
    owners := borrowedOwners
    borrowed := rfl }

theorem successful_view_zeuge :
    ram_view authority initial start 4 readWriteRights OwnerWitness.child = .ok writableResult := rfl

theorem class_refusal_zeuge :
    ram_view authority initial deviceStart 2 readOnlyRights OwnerWitness.child =
      .error .memoryClass := rfl

theorem bounds_refusal_zeuge :
    ram_view authority initial start 9 readWriteRights OwnerWitness.child = .error .bounds := rfl

theorem conflicting_loan_zeuge :
    ram_view authority writableResult.next start 4 readOnlyRights OwnerWitness.grandchild =
      .error .conflictingLoan := rfl

theorem return_zeuge : returnView authority writableResult.next = .ok initial :=
  ram_view_return initial_valid writableResult

end Gabbro.Grammatik.LowLevel.Witness
