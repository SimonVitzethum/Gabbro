module

public import Core.Ast.LowLevel.Syntax
public import Core.Ast.Aggregate.Runtime
public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-- The target tables currently supply widths for physical, virtual and port
    addresses. Guest-physical and I/O-virtual widths need their own rows. -/
def AddressSpace.width (platform : Plattform) : AddressSpace → Option Nat
  | .physical => some platform.ziel.physicalBits
  | .virtual => some platform.ziel.virtualBits
  | .port => platform.portAddressBits
  | .guestPhysical | .ioVirtual => none

/-- A number with bounds and a space tag. It has no capability or destination. -/
structure Address (space : AddressSpace) (platform : Plattform) where
  width : Nat
  number : Nat
  spaceWidth : space.width platform = some width
  fits : number < 2 ^ width

inductive ByteOrder where
  | little
  | big
  deriving DecidableEq

def ByteOrder.ofTarget (target : ZielDaten) : ByteOrder :=
  if target.big then .big else .little

/-- An exact-width integer view reuses the representation range of its written
    type. Loads must establish initialization and the declared value range. -/
structure Layout where
  written : WrittenType
  bytes : Nat
  alignment : Nat
  endian : ByteOrder

def layout (target : ZielDaten) : WrittenType → Option Layout
  | .integer signed width range =>
    let written := WrittenType.integer signed width range
    let (minimum, maximum) := WrittenType.storage signed width
    let (lo, hi) := range.getD (minimum, maximum)
    if width ∈ ([8, 16, 32, 64] : List Nat) ∧ minimum ≤ lo ∧ lo ≤ hi ∧ hi ≤ maximum then
      some ⟨written, width / 8, width / 8, .ofTarget target⟩
    else none
  | .bool | .array .. | .tuple .. | .text .. | .index .. | .indexOption ..
  | .address .. | .ownedRegion => none

def Layout.fits (shape : Layout) (extent : Strecke) : Prop :=
  extent.von % shape.alignment = 0 ∧ extent.von + shape.bytes ≤ extent.bis

instance (shape : Layout) (extent : Strecke) : Decidable (shape.fits extent) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Both the low-level meaning and the ordinary binding use the same layout,
    alignment and extent test. Forming a view does not read its bytes. -/
def RegionInitializer.value (target : ZielDaten) (slot : Nat) (extent : Strecke) :
    RegionInitializer → Option Dynamisch
  | .address =>
    if h : extent.von < 2 ^ target.physicalBits then
      some ⟨.address .physical, ⟨target.physicalBits, extent.von, h⟩⟩
    else none
  | .view written _valid => do
    let shape ← layout target written
    if shape.fits extent then
      some ⟨.regionView written.type, ⟨slot, extent.von, shape.bytes, target.big⟩⟩
    else none

/-- A source scope associates names with arrival-region slots. A slot identifies
    an object in the boundary contract, independently of the object's address. -/
abbrev RegionScope := List Identifier

def RegionScope.slot (scope : RegionScope) (name : Identifier) : Option Nat :=
  List.idxOf? name.val (scope.map Subtype.val)

inductive Instruction (k : Katalog) where
  | denoteAddress (space : AddressSpace) (width : Nat) (valid : space.width k.plattform = some width)
  | projectAddress (slot : Nat)
  | borrowView (slot : Nat) (layout : Layout)
  | selectEnvironment (name : Identifier) (abi : DienstAbi) (row : FirmwareZeile)
      (allowed : row.zugelassen k abi)

/-- The ABI and service row are checked together at the declaration. Name
    resolution of the two region operands uses the same arrival-region scope. -/
def elaborate (k : Katalog) (scope : RegionScope) : Tree form → Option (Instruction k)
  | .addressType space =>
    if h : (space.width k.plattform).isSome then
      some (.denoteAddress space _ (Option.some_get h).symm)
    else none
  | .regionAddress name => (scope.slot name).map .projectAddress
  | .view name written => do
    let slot ← scope.slot name
    let shape ← layout k.plattform.ziel written
    pure (.borrowView slot shape)
  | .environment name abi row =>
    if h : row.zugelassen k abi then some (.selectEnvironment name abi row h) else none

inductive Result (k : Katalog) where
  | addressType (space : AddressSpace) (width : Nat)
  | address (value : Address .physical k.plattform)
  | view (slot : Nat) (authority : Griff) (extent : Strecke) (layout : Layout)
  | environment (name : Identifier) (row : FirmwareZeile) (abi : DienstAbi)

structure Frame (k : Katalog) where
  pc : Nat := 0
  regions : List Strecke := []
  borrowed : List Griff := []
  result : Option (Result k) := none

abbrev State (k : Katalog) := Zustand PUnit Nat UInt8 PUnit (Frame k) PUnit

/-- Only the current owner can use the extent in its arrival slot. The handle
    uses an object index and epoch, and the authoritative extent comes from the
    boundary's region list. Borrowing never reads the represented bytes. -/
def heldRegion {k : Katalog} (s : State k) (c : Kontext) (slot : Nat) : Option (Griff × Strecke) := do
  let frame := s.lokal c
  let extent ← frame.regions[slot]?
  let handle : Griff := ⟨slot, 0⟩
  if s.rechte.lebt slot && s.rechte.gen slot == handle.gen && !frame.borrowed.contains handle then
    match s.leihen slot with
    | .eigen => pure (handle, extent)
    | .verliehen _ => none
  else none

structure Transfer (k : Katalog) where
  value : Result k
  loan : Option Griff := none

def Instruction.evaluate {k : Katalog} (op : Instruction k) (s : State k) (c : Kontext) :
    Option (Transfer k) :=
  match op with
  | .denoteAddress space width _ => some ⟨.addressType space width, none⟩
  | .projectAddress slot => do
    let (_, extent) ← heldRegion s c slot
    let width := k.plattform.ziel.physicalBits
    if h : extent.von < 2 ^ width then
      pure ⟨.address ⟨width, extent.von, rfl, h⟩, none⟩
    else none
  | .borrowView slot shape => do
    let (handle, extent) ← heldRegion s c slot
    if shape.fits extent then
      pure ⟨.view slot handle ⟨extent.von, extent.von + shape.bytes⟩ shape, some handle⟩
    else none
  | .selectEnvironment name abi row _ => some ⟨.environment name row abi, none⟩

end Gabbro.Core.Ast.LowLevel
