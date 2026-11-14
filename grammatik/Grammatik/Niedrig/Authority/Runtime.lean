module

public import Grammatik.Niedrig.Authority.Metadata
public import Grammatik.Niedrig.Bytes.Grants

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

/-- Persistent generations belong to span nodes of one context. A child
    return updates its own node and leaves every ancestor's stamp intact. -/
abbrev SpanGenerations := Nat → Nat

def SpanGenerations.bump (generations : SpanGenerations) (node : Nat) : SpanGenerations :=
  fun other => if other = node then generations other + 1 else generations other

theorem SpanGenerations.bump_self (generations : SpanGenerations) (node : Nat) :
    generations.bump node node = generations node + 1 := if_pos rfl

theorem SpanGenerations.bump_other (generations : SpanGenerations) {node other : Nat}
    (different : other ≠ node) : generations.bump node other = generations other :=
  if_neg different

/-- The kind of the innermost lexical exit. A loan remembers its exact
    runtime identity; neither kind contains an authority receipt. -/
inductive ScopeKind where
  | view
  | loan (id : Nat)
  deriving DecidableEq

/-- A persistent node stamp, shared by the ledger's stack and the machine
    continuation marker. The generation is read from the entry on admission. -/
structure ScopeKey where
  kind : ScopeKind
  node : Nat
  generation : Nat
  deriving DecidableEq

/-- The machine stores the authority alongside the canonical context, so an
    operation resolves an id to actual data rather than to a ghost receipt.
    Byte-loan tables are separated by span node; their carrier-local counters
    therefore cannot invalidate an ancestor's node on a nested return. -/
structure ContextEntry (D : Deklaration) where
  authority : Authority D
  context : Construct.SystemContext D
  generations : SpanGenerations
  byteLoans : Nat → Niedrig.Bytes.GrantTable
  scopes : List ScopeKey := []

/-- Shared call-machine state, deliberately outside World and Speicher: an
    oracle may change neither authority nor generations by returning a World.
    Initial entries must be supplied by the entry/binding; no ordinary G step
    creates an entry. -/
abbrev ContextLedger (D : Deklaration) := Nat → Option (ContextEntry D)

def ContextLedger.empty : ContextLedger D := fun _ => none

def ContextLedger.set (ledger : ContextLedger D) (id : Nat) (entry : ContextEntry D) :
    ContextLedger D := fun other => if other = id then some entry else ledger other

theorem ContextLedger.set_self (ledger : ContextLedger D) (id : Nat) (entry : ContextEntry D) :
    ledger.set id entry id = some entry := if_pos rfl

theorem ContextLedger.set_other (ledger : ContextLedger D) (id : Nat) (entry : ContextEntry D)
    {other : Nat} (different : other ≠ id) : ledger.set id entry other = ledger other :=
  if_neg different

end Gabbro.Grammatik.LowLevel
