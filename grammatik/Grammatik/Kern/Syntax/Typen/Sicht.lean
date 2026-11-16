module

public import Grammatik.Kern.Syntax.Typen.AdressLayout
public import Grammatik.Kern.Syntax.Syntax.Teil1b
public import Grammatik.Kern.Syntax.Typen.Frame

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

/-- A declared nominal space and a canonical backing identity. Translation of
    virtual aliases is L6; distinct nominal names never establish separation. -/
inductive AddressKind where
  | physical
  | virtual
  deriving DecidableEq, Repr

structure Space (D : Deklaration) where
  nominal : Nat
  backing : Nat
  width : Nat
  kind : AddressKind
  declared : nominal < D.dataSpaces.length
  positiveWidth : 0 < width
  deriving DecidableEq, Repr

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

def Span.Valid {D : Deklaration} (span : Span D) : Prop :=
  0 < span.length ∧ span.base + span.length ≤ 2 ^ span.space.width ∧
  0 < span.alignment ∧ D.capTab span.space.nominal span.number = some span.table

instance {D : Deklaration} (span : Span D) : Decidable span.Valid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

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

instance {D : Deklaration} (v : View D) (byte : Adresse) : Decidable (v.Contains byte) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def View.Overlaps {D : Deklaration} (a b : View D) : Prop :=
  a.span.space.backing = b.span.space.backing ∧
  a.base < b.base + b.length ∧ b.base < a.base + a.length

/-- Shared live borrows may overlap only with read-only permissions. The
    existing exclusive escrow still grants access to just the innermost frame. -/
def View.Compatible {D : Deklaration} (a b : View D) : Prop :=
  a.Overlaps b → a.rights.write = false ∧ b.rights.write = false

instance {D : Deklaration} (a b : View D) : Decidable (a.Compatible b) :=
  inferInstanceAs (Decidable ((_ ∧ _ ∧ _) → _ ∧ _))

end Gabbro.Grammatik.LowLevel
