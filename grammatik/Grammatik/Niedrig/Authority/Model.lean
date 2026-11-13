module

public import Grammatik.Speichermodell.Adressen.Layout
public import Grammatik.Kern.Syntax.Marken.Owner.Conservation
public import Grammatik.Kern.Syntax.Marken.Owner.Source
public import Grammatik.Niedrig.Authority.Address
public import Grammatik.Hardware.Anbieter.Region

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

/-!
L1 is a layer beside machine G. No declaration here changes Ty, Expr, Stmt,
Akzeptiert, or any definition used by the goal statement.

Required later connections:
* G syntax/evaluation: address expressions need a new inert value case;
  context names remain existing linear ghost owner bindings. A bounded-view
  scope must retain its extent and the actual owner escrow on both exits.
* G/GX: relate AuthorityStep to actual call/scope transitions and record every
  ordinary access in the existing trace. The present ViewWrite is an extent
  receipt over the existing store, not an admitted source memory operation.
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

/-- No device or reserved storage can be borrowed as ordinary RAM. Further
    device kinds belong to L2, rather than to permissive RAM defaults. -/
inductive MemoryClass where
  | ordinaryRam
  | device
  | reserved
  deriving DecidableEq, Repr

/-- A finite reservation over an existing carrier, not another heap. The
    execute bit is authority metadata only; data views never acquire it. -/
structure Span (D : Deklaration) where
  space : Space D
  base : Nat
  length : Nat
  table : D.Tab
  number : Nat
  rights : DataRights
  execute : Bool
  memoryClass : MemoryClass
  owner : D.Marke
  epoch : Nat
  alignment : Nat
  mapped : Bool
  initialized : Bool
  deriving DecidableEq

def Span.range {D : Deklaration} (span : Span D) : Anbieter.Strecke :=
  ⟨span.base, span.base + span.length⟩

/-- Separation is by backing identity, never by nominal space name. -/
def Span.Separated {D : Deklaration} (a b : Span D) : Prop :=
  a.space.backing ≠ b.space.backing ∨ a.range.getrennt b.range

def Span.Valid {D : Deklaration} (span : Span D) : Prop :=
  0 < span.length ∧ span.base + span.length ≤ 2 ^ span.space.width ∧
  0 < span.alignment ∧ D.capTab span.space.nominal span.number = some span.table

instance {D : Deklaration} (span : Span D) : Decidable span.Valid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- An authority declaration is satisfied at the chosen boot boundary. Its
    token is the existing nominal owner grant, never a copyable Ty value. -/
structure Authority (D : Deklaration) where
  names : OwnerNamespace D
  token : OwnerToken D
  spans : List (Span D)
  epoch : Nat

def Authority.Valid {D : Deklaration} (a : Authority D) : Prop :=
  (∃ t, a.token.mark ∈ D.eigner t) ∧ a.token.stage < D.stufen a.token.mark ∧
  (∀ span ∈ a.spans, span.Valid ∧ span.owner = a.token.mark ∧ span.epoch ≤ a.epoch) ∧
  a.spans.Pairwise Span.Separated

/-- A scoped finite borrow of the existing table capability. It carries bounds
    the present table-only DataTarget cannot express. Never erase those bounds
    to a bare Val.ptr; representation/reference introduction is L3. -/
structure View (D : Deklaration) where
  span : Span D
  base : Nat
  length : Nat
  rights : DataRights
  lender : ArenaOwnership.Frame
  borrower : ArenaOwnership.Frame
  epoch : Nat
  deriving DecidableEq

def View.region {D : Deklaration} (v : View D) : DataCapTy :=
  ⟨v.span.space.nominal, v.rights, .table v.span.number⟩

def View.Contains {D : Deklaration} (v : View D) (byte : Adresse) : Prop :=
  byte.1 = v.span.space.backing ∧ v.base ≤ byte.2 ∧ byte.2 < v.base + v.length

def View.Overlaps {D : Deklaration} (a b : View D) : Prop :=
  a.span.space.backing = b.span.space.backing ∧
  a.base < b.base + b.length ∧ b.base < a.base + a.length

/-- Shared live borrows may overlap only with read-only permissions. The
    existing exclusive escrow still grants access to just the innermost frame. -/
def View.Compatible {D : Deklaration} (a b : View D) : Prop :=
  a.Overlaps b → a.rights.write = false ∧ b.rights.write = false

instance {D : Deklaration} (a b : View D) : Decidable (a.Compatible b) :=
  inferInstanceAs (Decidable ((_ ∧ _ ∧ _) → _ ∧ _))

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

/-- Architectural state is abstract. No target or instruction is encoded here.
    One context grant is suspended/restored by the existing owner loan stack. -/
structure Context (D : Deklaration) (Privilege Interrupt : Type) where
  owners : OwnerState D
  frame : ArenaOwnership.Frame
  views : List (View D)
  privilege : Privilege
  interrupt : Interrupt

/-- Runtime metadata plus static authority conditions. AuthorityStep supplies
    actual borrow/return provenance; arbitrary record literals are not origins. -/
def Context.Valid {D : Deklaration} {P I : Type} (a : Authority D) (c : Context D P I) : Prop :=
  a.Valid ∧ c.owners.ledger.valid ∧ c.owners.access a.names c.frame a.token ∧
  (∀ v ∈ c.views, v.Valid a) ∧
  (∀ v ∈ c.views, ∀ w ∈ c.views, v ≠ w → v.Compatible w)

end Gabbro.Grammatik.LowLevel
