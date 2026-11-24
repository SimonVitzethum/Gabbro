module

public import Core.Ast.LowLevel.Syntax
public import Core.Ast.LowLevel.MemSyntax
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
  | .bool | .array .. | .tuple .. => none

/-- A pending revocation: the cleared range of one space with the generation it
    cleared at and the frame base the range mapped to. The frames return to the
    kernel only after the matching `flush` invalidated every cached translation. -/
structure Zuruecknahme where
  raum : Nat
  seite : Nat
  seiten : Nat
  generation : Nat
  frameBasis : Nat
  deriving DecidableEq, Repr

/-- The language-owned state of one address space: the table extent the space
    was created from, the installed page map, the current mapping generation
    and the revocations still awaiting their shootdown. Cached translations
    live in the frame's `tlb` view; `generation` tells a stale entry apart. -/
structure Adressraum where
  tabellen : Strecke
  abbildung : Nat → Option Seiteneintrag
  generation : Nat
  ausstehend : List Zuruecknahme

/-- A space activates only in this shape: the tables are a non-empty,
    page-aligned extent inside the physical address width, and every installed
    entry points at a present frame with a non-empty right set. -/
def Adressraum.Wohlgeformt (z : ZielDaten) (sp : Adressraum) : Prop :=
  sp.tabellen.von < sp.tabellen.bis ∧ sp.tabellen.bis ≤ 2 ^ z.physicalBits ∧
  sp.tabellen.von % z.seitengranule = 0 ∧
  ∀ pg e, sp.abbildung pg = some e →
    e.frame * z.seitengranule + z.seitengranule ≤ 2 ^ z.physicalBits ∧ e.rights ≠ []

/-- A source scope holds three separate name lists: arrival regions, address
    spaces and revocation-token bindings. The enclosing statement layer keeps
    the token bindings and the frame's token list in the same order. -/
structure MemScope where
  regionen : List Identifier
  raeume : List Identifier
  marken : List Identifier

def MemScope.slotRegion (scope : MemScope) (name : Identifier) : Option Nat :=
  List.idxOf? name.val (scope.regionen.map Subtype.val)

def MemScope.slotRaum (scope : MemScope) (name : Identifier) : Option Nat :=
  List.idxOf? name.val (scope.raeume.map Subtype.val)

def MemScope.slotMarke (scope : MemScope) (name : Identifier) : Option Nat :=
  List.idxOf? name.val (scope.marken.map Subtype.val)

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
  | splitRegion (slot point : Nat)
  | splitPages (slot pages : Nat)
  | mergeRegions (first second : Nat)
  | newSpace (tables : Nat)
  | mapSpace (space : Nat) (virt : Nat) (frames : Nat) (rights : List Speicherdienst)
  | protectSpace (space : Nat) (virt : Nat) (pages : Nat) (rights : List Speicherdienst)
  | unmapSpace (space : Nat) (virt : Nat) (pages : Nat)
  | flushSpace (name : Identifier)
  | activateSpace (space : Nat)

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

/-- Elaborate a memory-management leaf. Region, space and token names resolve
    in their own scope lists; an unknown name refuses the occurrence. The token
    of `flush` additionally needs its binding in the frame (see `bindMarke`). -/
def elaborateMem (k : Katalog) (scope : MemScope) : MemTree form → Option (Instruction k)
  | .splitAt region point => (scope.slotRegion region).map (fun slot => .splitRegion slot point)
  | .splitPages region pages => (scope.slotRegion region).map (fun slot => .splitPages slot pages)
  | .merge first second => do
    let s₁ ← scope.slotRegion first
    let s₂ ← scope.slotRegion second
    pure (.mergeRegions s₁ s₂)
  | .newSpace tables => (scope.slotRegion tables).map .newSpace
  | .mapSpace space virt frames rights => do
    let sp ← scope.slotRaum space
    let fr ← scope.slotRegion frames
    pure (.mapSpace sp virt fr rights)
  | .protectSpace space virt pages rights => do
    let sp ← scope.slotRaum space
    pure (.protectSpace sp virt pages rights)
  | .unmapSpace space virt pages => do
    let sp ← scope.slotRaum space
    pure (.unmapSpace sp virt pages)
  | .flushSpace name => do
    let _ ← scope.slotMarke name
    pure (.flushSpace name)
  | .activateSpace space => (scope.slotRaum space).map .activateSpace

inductive Result (k : Katalog) where
  | addressType (space : AddressSpace) (width : Nat)
  | address (value : Address .physical k.plattform)
  | view (slot : Nat) (authority : Griff) (extent : Strecke) (layout : Layout)
  | environment (name : Identifier) (row : FirmwareZeile) (abi : DienstAbi)
  | partition (first second : Strecke)
  | merged (extent : Strecke)
  | space (id : Nat)
  | mapped
  | protected
  | pending (token : Zuruecknahme)
  | frames (extent : Strecke)
  | activated

structure Frame (k : Katalog) where
  pc : Nat := 0
  regions : List Strecke := []
  borrowed : List Griff := []
  result : Option (Result k) := none
  spaces : List Adressraum := []
  tlb : Nat → Nat → Nat → Option Seiteneintrag := fun _ _ _ => none
  aktiverRaum : Option Nat := none
  marken : List (Identifier × Zuruecknahme) := []

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
  regionen : Option (List Strecke) := none
  rechte : Option Rechte := none
  raeume : Option (List Adressraum) := none
  tlb : Option (Nat → Nat → Nat → Option Seiteneintrag) := none
  aktiv : Option Nat := none
  marken : Option (List (Identifier × Zuruecknahme)) := none

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
    if extent.von % shape.alignment = 0 ∧ extent.von + shape.bytes ≤ extent.bis then
      pure ⟨.view slot handle ⟨extent.von, extent.von + shape.bytes⟩ shape, some handle⟩
    else none
  | .selectEnvironment name abi row _ => some ⟨.environment name row abi, none⟩
  | .splitRegion slot point => do
    let (_, extent) ← heldRegion s c slot
    if extent.von < point ∧ point < extent.bis then
      let left : Strecke := ⟨extent.von, point⟩
      let right : Strecke := ⟨point, extent.bis⟩
      let regions := (s.lokal c).regions.set slot left ++ [right]
      pure { value := .partition left right, regionen := some regions,
        rechte := some (s.rechte.beleben regions.length.pred) }
    else none
  | .splitPages slot pages => do
    let g := k.plattform.ziel.seitengranule
    let (_, extent) ← heldRegion s c slot
    let cut := extent.von + pages * g
    if extent.von % g = 0 ∧ 0 < pages ∧ cut < extent.bis then
      let left : Strecke := ⟨extent.von, cut⟩
      let right : Strecke := ⟨cut, extent.bis⟩
      let regions := (s.lokal c).regions.set slot left ++ [right]
      pure { value := .partition left right, regionen := some regions,
        rechte := some (s.rechte.beleben regions.length.pred) }
    else none
  | .mergeRegions s₁ s₂ => do
    let (_, e₁) ← heldRegion s c s₁
    let (_, e₂) ← heldRegion s c s₂
    if s₁ ≠ s₂ ∧ (e₁.bis = e₂.von ∨ e₂.bis = e₁.von) then
      let merged : Strecke := ⟨Nat.min e₁.von e₂.von, Nat.max e₁.bis e₂.bis⟩
      let regions := (s.lokal c).regions.set s₁ merged
      pure { value := .merged merged, regionen := some regions,
        rechte := some (s.rechte.widerrufen s₂) }
    else none
  | .newSpace tables => do
    let z := k.plattform.ziel
    let (_, extent) ← heldRegion s c tables
    if extent.von < extent.bis ∧ extent.bis ≤ 2 ^ z.physicalBits ∧
        extent.von % z.seitengranule = 0 then
      let sp : Adressraum :=
        { tabellen := extent, abbildung := fun _ => none, generation := 0, ausstehend := [] }
      pure { value := .space (s.lokal c).spaces.length,
        raeume := some ((s.lokal c).spaces ++ [sp]) }
    else none
  | .mapSpace sp virt fr rights => do
    let z := k.plattform.ziel
    let g := z.seitengranule
    let space ← (s.lokal c).spaces[sp]?
    let (_, fext) ← heldRegion s c fr
    let bytes := fext.bis - fext.von
    if rights ≠ [] ∧ fext.von < fext.bis ∧ bytes % g = 0 ∧ fext.von % g = 0 then
      let seiten := bytes / g
      let base := virt / g
      if 0 < seiten ∧ virt % g = 0 ∧
          ((List.range seiten).all fun i => (space.abbildung (base + i)).isNone) ∧
          ((List.range seiten).all fun i => decide (z.virtuell (virt + i * g))) ∧
          (space.ausstehend.all fun t =>
            (List.range seiten).all fun i =>
              decide (¬ (t.seite ≤ base + i ∧ base + i < t.seite + t.seiten))) then
        let fbasis := fext.von / g
        let abbildung := fun pg =>
          if base ≤ pg ∧ pg < base + seiten then
            some { frame := fbasis + (pg - base), rechte := rights, generation := space.generation }
          else space.abbildung pg
        pure { value := .mapped,
          raeume := some ((s.lokal c).spaces.set sp { space with abbildung := abbildung }) }
      else none
    else none
  | .protectSpace sp virt pages rights => do
    let z := k.plattform.ziel
    let g := z.seitengranule
    let space ← (s.lokal c).spaces[sp]?
    let base := virt / g
    if rights ≠ [] ∧ 0 < pages ∧ virt % g = 0 ∧
        ((List.range pages).all fun i => (space.abbildung (base + i)).isSome) ∧
        ((List.range pages).all fun i => decide (z.virtuell (virt + i * g))) then
      let abbildung := fun pg =>
        match space.abbildung pg with
        | some e =>
          if base ≤ pg ∧ pg < base + pages then some { e with rechte := rights } else some e
        | none => none
      let tlb := fun co sp' pg =>
        if sp' = sp ∧ base ≤ pg ∧ pg < base + pages then none
        else (s.lokal c).tlb co sp' pg
      pure { value := .protected,
        raeume := some ((s.lokal c).spaces.set sp { space with abbildung := abbildung }),
        tlb := some tlb }
    else none
  | .unmapSpace sp virt pages => do
    let z := k.plattform.ziel
    let g := z.seitengranule
    let space ← (s.lokal c).spaces[sp]?
    let base := virt / g
    let first ← space.abbildung base
    if 0 < pages ∧ virt % g = 0 ∧
        ((List.range pages).all fun i =>
          decide ((space.abbildung (base + i)).map Seiteneintrag.frame =
            some (first.frame + i))) ∧
        ((List.range pages).all fun i => decide (z.virtuell (virt + i * g))) then
      let abbildung := fun pg =>
        if base ≤ pg ∧ pg < base + pages then none else space.abbildung pg
      let tok : Zuruecknahme :=
        { raum := sp, seite := base, seiten := pages, generation := space.generation + 1,
          frameBasis := first.frame }
      pure { value := .pending tok,
        raeume := some ((s.lokal c).spaces.set sp
          { space with abbildung := abbildung, generation := space.generation + 1,
            ausstehend := tok :: space.ausstehend }) }
    else none
  | .flushSpace name => do
    let g := k.plattform.ziel.seitengranule
    let frame := s.lokal c
    let (_, tok) ← frame.marken.find? (fun p => decide (p.1.val = name.val))
    let space ← frame.spaces[tok.raum]?
    if tok ∈ space.ausstehend then
      let tlb := fun co sp' pg =>
        if sp' = tok.raum ∧ tok.seite ≤ pg ∧ pg < tok.seite + tok.seiten then none
        else frame.tlb co sp' pg
      let extent : Strecke := ⟨tok.frameBasis * g, (tok.frameBasis + tok.seiten) * g⟩
      pure { value := .frames extent,
        tlb := some tlb,
        raeume := some (frame.spaces.set tok.raum
          { space with ausstehend := space.ausstehend.filter (fun t => !decide (t = tok)) }),
        marken := some (frame.marken.filter (fun p => !decide (p.1.val = name.val))) }
    else none
  | .activateSpace sp => do
    let space ← (s.lokal c).spaces[sp]?
    if space.Wohlgeformt k.plattform.ziel then
      pure { value := .activated, aktiv := some sp }
    else none

/-- The enclosing `let` binds a revocation token under its source name. The
    future statement layer performs exactly this update after `unmap`; `flush`
    resolves its operand through the resulting binding. -/
def bindMarke {k : Katalog} (s : State k) (c : Kontext) (name : Identifier)
    (tok : Zuruecknahme) : State k :=
  let frame := s.lokal c
  { s with lokal := Function.update s.lokal c { frame with marken := frame.marken ++ [(name, tok)] } }

end Gabbro.Core.Ast.LowLevel
