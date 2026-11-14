module

public import Grammatik.Niedrig.Witnesses.Fixture
public import Grammatik.Niedrig.Authority.RuntimeScope

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Witness.Runtime

open Niedrig.Bytes

/-- This witness uses the same owner grant as the canonical RAM fixture,
    with the target-neutral privilege and interrupt state used by G. -/
def context : Construct.SystemContext D :=
  { owners := initialOwners
    frame := initial.frame
    views := []
    privilege := ⟨.kern, 0, false, 0, 0⟩
    interrupt :=
      { maske := ⟨fun _ => ⟨false, 0, []⟩⟩
        prio := fun _ => ⟨0, []⟩ } }

def entry : ContextEntry D :=
  { authority := authority
    context := context
    generations := fun node => if node = 7 then 3 else 11
    byteLoans := fun _ => ⟨fun _ => 0, []⟩ }

def key : ScopeKey := ⟨.view, 7, 3⟩

def receipt : ViewResult authority context :=
  { view := writableView
    admission := writableAdmission
    owners := borrowedOwners
    borrowed := rfl }

def opened : ContextEntry D :=
  { entry with context := receipt.next, scopes := [key] }

def closed : ContextEntry D := entry.finish key [] context entry.byteLoans

theorem admitted : entry.openView 7 start 4 readWriteRights OwnerWitness.child =
    .ok (opened, key) := rfl

theorem released : opened.close key = .ok closed := by
  have valid : entry.context.Valid entry.authority := initial_valid
  exact ContextEntry.openView_close valid admitted

/-- The child becomes stale; an ancestor retains a different, nonzero
    generation. This distinguishes node generations from one global epoch. -/
theorem child_and_parent : closed.generations 7 = 4 ∧ closed.generations 2 = 11 ∧
    key.generation < closed.generations key.node :=
  ⟨rfl, rfl, ContextEntry.close_stale released⟩

/-- The ledger operation executes the release of its actual stored entry. -/
theorem ledger_release :
    (ContextLedger.empty.set 4 opened).close 4 key =
      .ok ((ContextLedger.empty.set 4 opened).set 4 closed) := by
  simp only [ContextLedger.close, ContextLedger.set_self, released]

/-- An invalid stamp cannot use a successful escrow close to bypass the
    generation check; no success ledger is produced. -/
theorem stale_refused :
    ({ opened with scopes := [{ key with generation := 2 }] } : ContextEntry D).close
      { key with generation := 2 } = .error .stale := rfl

def byteCap : ByteCap := ⟨0, 0, 4, Perm.schreibe⟩
def byteGrant : Grant := ⟨byteCap, 0⟩
def loan : Loan := ⟨byteCap, byteGrant, 21⟩
def loanKey : ScopeKey := ⟨.loan 21, 7, 3⟩

def loanEntry : ContextEntry D :=
  { entry with
    scopes := [loanKey]
    byteLoans := fun node => if node = 7 then ⟨fun _ => 0, [loan]⟩ else entry.byteLoans node }

def loanClosed : ContextEntry D :=
  loanEntry.finish loanKey [] context
    (fun node => if node = 7 then ⟨fun _ => 0, []⟩ else loanEntry.byteLoans node)

/-- Loan cleanup invokes gibZurueck, removes its LIFO escrow and updates
    precisely the child's persistent generation. -/
theorem loan_release : loanEntry.close loanKey = .ok loanClosed := rfl

theorem loan_parent_live : loanClosed.generations 7 = 4 ∧
    loanClosed.generations 2 = 11 ∧ (loanClosed.byteLoans 7).loans = [] := ⟨rfl, rfl, rfl⟩

end Gabbro.Grammatik.LowLevel.Witness.Runtime
