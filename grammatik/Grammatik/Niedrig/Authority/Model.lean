module

public import Grammatik.Kern.Syntax.Marken.Owner.Conservation
public import Grammatik.Kern.Syntax.Marken.Owner.Source
public import Grammatik.Niedrig.Authority.AddressData
public import Grammatik.Niedrig.Authority.Metadata
public import Grammatik.Hardware.Anbieter.Region

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

/-!
L1 is a layer beside machine G. No declaration here changes Ty, Expr, Stmt,
Akzeptiert, or any definition used by the goal statement.

Required later connections:
* G syntax/evaluation: address expressions need a new inert value case;
  context values must identify records in G's shared context ledger. Existing
  ghost owner bindings alone are not runtime contexts. A bounded-view scope
  must retain its extent and the actual owner escrow on every exit.
* G/GX: the shared ledger stores authority and canonical context records,
  outside World. Connect checked ledger entry/release to actual source scope
  transitions and record every ordinary access in the existing trace. The
  present ViewWrite is an extent receipt, not an admitted source operation.
* AkzeptiertSpec(X)/Akzeptiert: check declared spaces, profile/authority origin,
  exact LinearContextStep evidence, view lifetimes and permissions. Source
  forms stay refused until these checks and their simulation are connected.
* Spec: add reachable authority/epoch/view preservation and extend the address
  leg with finite realized spans. Derive the boot software parts of Laufzeit,
  StartGut, GutO, AxVertragO and ImBereichO from boot/body proofs; keep the
  firmware entry an explicit environment contract. These are owner-reviewed
  changes, not consequences already supplied by this layer.

L2 may reuse MemoryClass, spans, permissions, epochs and exclusive owner escrow.
It must add device-specific operations and quiescence contracts; ram_view has
no device acceptance branch. L3 owns live-byte representations and typed
reference construction. L6 owns physical translation, revocation and reuse;
the backing coordinate here is the existing canonical layout coordinate.
-/

def Span.range {D : Deklaration} (span : Span D) : Anbieter.Strecke :=
  ⟨span.base, span.base + span.length⟩

/-- Separation is by backing identity, never by nominal space name. -/
def Span.Separated {D : Deklaration} (a b : Span D) : Prop :=
  a.space.backing ≠ b.space.backing ∨ a.range.getrennt b.range

def Authority.Valid {D : Deklaration} (a : Authority D) : Prop :=
  (∃ t, a.token.mark ∈ D.eigner t) ∧ a.token.stage < D.stufen a.token.mark ∧
  (∀ span ∈ a.spans, span.Valid ∧ span.owner = a.token.mark ∧ span.epoch ≤ a.epoch) ∧
  a.spans.Pairwise Span.Separated

/-- Every live view retains the full authorization check, including permission,
    mapping and initialization facts; bounds alone are not an authority proof. -/
def View.Valid {D : Deklaration} (a : Authority D) (v : View D) : Prop :=
  v.span ∈ a.spans ∧ v.epoch = a.epoch ∧ v.span.memoryClass = .ordinaryRam ∧
  v.span.base ≤ v.base ∧ v.base + v.length ≤ v.span.base + v.span.length ∧
  v.span.owner = a.token.mark ∧ v.span.epoch = a.epoch ∧
  (v.rights.read = true ∨ v.rights.write = true) ∧
  (v.rights.read = true → v.span.rights.read = true) ∧
  (v.rights.write = true → v.span.rights.write = true) ∧
  v.rights.owner = v.span.rights.owner ∧
  0 < v.span.alignment ∧ v.base % v.span.alignment = 0 ∧ v.length % v.span.alignment = 0 ∧
  v.span.mapped = true ∧ v.span.initialized = true

/-- Runtime metadata plus static authority conditions. AuthorityStep supplies
    actual borrow/return provenance; arbitrary record literals are not origins. -/
def Context.Valid {D : Deklaration} {P I : Type} (a : Authority D) (c : Context D P I) : Prop :=
  a.Valid ∧ c.owners.ledger.valid ∧ c.owners.access a.names c.frame a.token ∧
  (∀ v ∈ c.views, v.Valid a) ∧
  (∀ v ∈ c.views, ∀ w ∈ c.views, v ≠ w → v.Compatible w)

end Gabbro.Grammatik.LowLevel
