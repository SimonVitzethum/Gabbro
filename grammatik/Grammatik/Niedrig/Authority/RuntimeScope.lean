module

public import Grammatik.Niedrig.Authority.Runtime
public import Grammatik.Niedrig.Authority.View

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

inductive ScopeFailure where
  | missingContext
  | order
  | stale
  | activeNode
  | view (reason : ViewFailure)
  | loan (reason : String)
  deriving DecidableEq

variable {D : Deklaration}

/-- Commit one checked lexical release. Memory is not part of this operation;
    restoring authority never rolls back writes performed in the body. -/
def ContextEntry.finish (entry : ContextEntry D) (key : ScopeKey) (tail : List ScopeKey)
    (context : Construct.SystemContext D) (loans : Nat → Niedrig.Bytes.GrantTable) : ContextEntry D :=
  { entry with
    context := context
    byteLoans := loans
    scopes := tail
    generations := entry.generations.bump key.node }

/-- The same executable close is used for fallthrough, both return channels,
    leave and next. It checks the actual context stack and its current stamp
    before invoking the existing escrow release. A refused close commits no
    ledger update and cannot be treated as a successful scope exit. -/
def ContextEntry.close (entry : ContextEntry D) (key : ScopeKey) :
    Except ScopeFailure (ContextEntry D) :=
  match entry.scopes with
  | [] => .error .order
  | top :: tail =>
      if top = key then
        if key.generation = entry.generations key.node then
          match key.kind with
          | .view =>
              match returnView entry.authority entry.context with
              | .error reason => .error (.view reason)
              | .ok context => .ok (entry.finish key tail context entry.byteLoans)
          | .loan id =>
              match Niedrig.Bytes.gibZurueck (entry.byteLoans key.node) id with
              | .error reason => .error (.loan reason)
              | .ok loans => .ok (entry.finish key tail entry.context
                  (fun node => if node = key.node then loans else entry.byteLoans node))
        else .error .stale
      else .error .order

/-- Resolve the id in shared machine data. No step can supply an unrelated
    Context or an existential successful receipt in place of that lookup. -/
def ContextLedger.close (ledger : ContextLedger D) (id : Nat) (key : ScopeKey) :
    Except ScopeFailure (ContextLedger D) :=
  match ledger id with
  | none => .error .missingContext
  | some entry =>
      match entry.close key with
      | .error reason => .error reason
      | .ok next => .ok (ledger.set id next)

/-- Admission stamps the actual ledger generation and pushes the same key
    that the continuation will retain. Active node identities cannot be
    reused by a nested view. The current ram_view checks remain in force. -/
def ContextEntry.openView {space : Space D} (entry : ContextEntry D) (node : Nat)
    (start : Address space) (length : Nat) (rights : DataRights)
    (borrower : ArenaOwnership.Frame) : Except ScopeFailure (ContextEntry D × ScopeKey) :=
  if entry.scopes.any (fun key => decide (key.node = node)) then
    .error .activeNode
  else
    match ram_view entry.authority entry.context start length rights borrower with
    | .error reason => .error (.view reason)
    | .ok receipt =>
        let key : ScopeKey := ⟨.view, node, entry.generations node⟩
        .ok ({ entry with context := receipt.next, scopes := key :: entry.scopes }, key)

/-- Shared admission reads the id once and changes only its stored entry. -/
def ContextLedger.openView {space : Space D} (ledger : ContextLedger D) (id node : Nat)
    (start : Address space) (length : Nat) (rights : DataRights)
    (borrower : ArenaOwnership.Frame) : Except ScopeFailure (ContextLedger D × ScopeKey) :=
  match ledger id with
  | none => .error .missingContext
  | some entry =>
      match entry.openView node start length rights borrower with
      | .error reason => .error reason
      | .ok (next, key) => .ok (ledger.set id next, key)

/-- Every successful close removes precisely the top ledger marker and
    increments its node. This is not yet a reachability theorem for G. -/
theorem ContextEntry.close_shape {entry next : ContextEntry D} {key : ScopeKey}
    (closed : entry.close key = .ok next) :
    ∃ tail context loans, entry.scopes = key :: tail ∧
      key.generation = entry.generations key.node ∧
      next = entry.finish key tail context loans := by
  unfold close at closed
  split at closed
  · cases closed
  · rename_i top tail hstack
    split at closed
    · rename_i same
      subst top
      split at closed
      · rename_i live
        cases hk : key.kind with
        | view =>
            simp only [hk] at closed
            split at closed
            · cases closed
            · cases closed
              exact ⟨tail, _, _, hstack, live, rfl⟩
        | loan id =>
            simp only [hk] at closed
            split at closed
            · cases closed
            · cases closed
              exact ⟨tail, _, _, hstack, live, rfl⟩
      · cases closed
    · cases closed

/-- No successful exit may silently leave the released generation live. -/
theorem ContextEntry.close_stale {entry next : ContextEntry D} {key : ScopeKey}
    (closed : entry.close key = .ok next) :
    key.generation < next.generations key.node := by
  obtain ⟨tail, context, loans, _, live, rfl⟩ := close_shape closed
  rw [finish, SpanGenerations.bump_self, live]
  exact Nat.lt_succ_self _

/-- A child release cannot invalidate the generation of a distinct ancestor. -/
theorem ContextEntry.close_other {entry next : ContextEntry D} {key : ScopeKey}
    (closed : entry.close key = .ok next) {ancestor : Nat} (different : ancestor ≠ key.node) :
    next.generations ancestor = entry.generations ancestor := by
  obtain ⟨tail, context, loans, _, _, rfl⟩ := close_shape closed
  exact SpanGenerations.bump_other entry.generations different

/-- Resolving and closing one id cannot alter another context. -/
theorem ContextLedger.close_other {ledger next : ContextLedger D} {id : Nat} {key : ScopeKey}
    (closed : ledger.close id key = .ok next) {other : Nat} (different : other ≠ id) :
    next other = ledger other := by
  unfold close at closed
  split at closed
  · cases closed
  · split at closed
    · cases closed
    · cases closed
      exact set_other _ _ _ different

end Gabbro.Grammatik.LowLevel
