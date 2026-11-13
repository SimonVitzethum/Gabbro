module

public import Grammatik.Kern.Syntax.Typen.Teil2
public import Grammatik.Speichermodell.Adressen.Layout
import Lean.Elab.Tactic.Omega

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

/-- Inert, width-bounded data. The existing number type carries the range duty.
    There is deliberately no coercion to a capability, region or reference. -/
structure Address {D : Deklaration} (space : Space D) where
  value : Zahl 0 ((2 : Int) ^ space.width - 1)

namespace Address

theorem ext {D : Deklaration} {space : Space D} {a b : Address space}
    (h : a.value.n = b.value.n) : a = b := by
  rcases a with ⟨av⟩
  rcases b with ⟨bv⟩
  have values : av = bv := zahl_ext h
  cases values
  rfl

instance {D : Deklaration} {space : Space D} : DecidableEq (Address space) := fun a b =>
  if h : a.value.n = b.value.n then isTrue (ext h)
  else isFalse (fun e => h (congrArg (fun a => a.value.n) e))

def byte {D : Deklaration} {space : Space D} (a : Address space) : Nat := a.value.n.toNat

/-- The model's existing pair of backing identity and byte offset. -/
def location {D : Deklaration} {space : Space D} (a : Address space) : Adresse := (space.backing, a.byte)

end Address

/-- Arithmetic never wraps or saturates into a successful address. -/
inductive AddressFailure where
  | range
  deriving DecidableEq, Repr

/-- Fitting integer construction, also used for checked narrowing. -/
def address {D : Deklaration} (space : Space D) (n : Int) : Except AddressFailure (Address space) :=
  if h : 0 ≤ n ∧ n ≤ (2 : Int) ^ space.width - 1 then
    .ok ⟨⟨n, h.1, h.2⟩⟩
  else .error .range

/-- Address expressions are literals and signed byte displacements. Width
    changes use narrowAddress separately. No memory operation exists here. -/
inductive AddressExpr {D : Deklaration} (space : Space D) where
  | literal (n : Int)
  | offset (base : AddressExpr space) (delta : Int)

def AddressExpr.eval {D : Deklaration} {space : Space D} :
    AddressExpr space → Except AddressFailure (Address space)
  | .literal n => address space n
  | .offset base delta => do
      let a ← base.eval
      address space (a.value.n + delta)

/-- Width change retains both identities and checks the new finite range. -/
def narrowAddress {D : Deklaration} {space : Space D} (width : Nat) (positive : 0 < width)
    (a : Address space) :
    Except AddressFailure (Address { space with width := width, positiveWidth := positive }) :=
  address { space with width := width, positiveWidth := positive } a.value.n

/-- Same-space difference is an ordinary bounded number, never authority. -/
def addressDifference {D : Deklaration} {space : Space D} (a b : Address space) :
    Zahl (-(2 ^ space.width - 1)) (2 ^ space.width - 1) :=
  ⟨a.value.n - b.value.n, by have := a.value.lo_le; have := b.value.le_hi; omega,
    by have := a.value.le_hi; have := b.value.lo_le; omega⟩

/-- An address expression's evaluation is independent of the world; failure
    also retains it. This is a layer judgment, not a new constructor of G.Expr. -/
def evalAddress {D : Deklaration} {space : Space D} (e : AddressExpr space) (world : World D) :
    Except AddressFailure (Address space) × World D := (e.eval, world)

theorem address_world_unchanged {D : Deklaration} {space : Space D}
    (e : AddressExpr space) (world : World D) : (evalAddress e world).2 = world := rfl

theorem address_result_independent {D : Deklaration} {space : Space D}
    (e : AddressExpr space) (first second : World D) :
    (evalAddress e first).1 = (evalAddress e second).1 := rfl

end Gabbro.Grammatik.LowLevel
