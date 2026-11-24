module

public import Core.Ast.LowLevel.Mem.Syntax
public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-- Partitioning a live grant changes its local extent, while preserving the
    authorities that back every byte. Slots are appended and never reused. -/
structure MemRegion where
  extent : Strecke
  backing : List Griff
  deriving DecidableEq

structure Zuruecknahme where
  raum : Nat
  seite : Nat
  seiten : Nat
  generation : Nat
  frameBasis : Nat
  deriving DecidableEq, Repr

def Zuruecknahme.contains (token : Zuruecknahme) (page : Nat) : Prop :=
  token.seite ≤ page ∧ page < token.seite + token.seiten

instance (token : Zuruecknahme) (page : Nat) : Decidable (token.contains page) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Zuruecknahme.frames (token : Zuruecknahme) (granule : Nat) : Strecke :=
  ⟨token.frameBasis * granule, (token.frameBasis + token.seiten) * granule⟩

structure Adressraum where
  tabellen : Strecke
  entries : List (Nat × Seiteneintrag)
  generation : Nat
  ausstehend : List Zuruecknahme

def Adressraum.abbildung (space : Adressraum) (page : Nat) : Option Seiteneintrag :=
  (space.entries.find? (fun entry => entry.1 == page)).map Prod.snd

def Adressraum.Wohlgeformt (z : ZielDaten) (space : Adressraum) : Prop :=
  space.tabellen.seiten z ∧ (space.entries.map Prod.fst).Nodup ∧
  ∀ entry ∈ space.entries,
    z.virtuell (entry.1 * z.seitengranule) ∧
    (entry.2.frame + 1) * z.seitengranule ≤ 2 ^ z.physicalBits ∧
    entry.2.rights ≠ [] ∧ entry.2.generation ≤ space.generation ∧
    ∀ token ∈ space.ausstehend, ¬ token.contains entry.1

instance (z : ZielDaten) (extent : Strecke) : Decidable (extent.seiten z) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (z : ZielDaten) (space : Adressraum) : Decidable (space.Wohlgeformt z) :=
  inferInstanceAs (Decidable (_ ∧ _))

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

inductive MemResult where
  | partition (left right : MemRegion)
  | merged (region : MemRegion)
  | space (id : Nat)
  | mapped
  | «protected»
  | pending (token : Zuruecknahme)
  | frames (extent : Strecke)
  | activated

/-- One translation a core holds cached: the core, the space and the virtual page it translates, and
    the table entry it copied. Hardware drops and refills cells on its own; the language owns the
    invalidation protocol and the reuse of frames. -/
structure TlbZelle where
  kern : Nat
  raum : Nat
  seite : Nat
  eintrag : Seiteneintrag
  deriving DecidableEq, Repr

/-- The translations cached on every core of the spaces of one frame. The list is finite, so "no core
    caches a page of this range" is decidable; a core may hold several cells for one page. -/
structure TranslationCache where
  zellen : List TlbZelle := []

def TranslationCache.Haelt (cache : TranslationCache) (core space page : Nat)
    (entry : Seiteneintrag) : Prop :=
  (⟨core, space, page, entry⟩ : TlbZelle) ∈ cache.zellen

/-- A core takes a translation into its cache. -/
def TranslationCache.fill (cache : TranslationCache) (zelle : TlbZelle) : TranslationCache :=
  ⟨zelle :: cache.zellen⟩

structure MemFrame where
  pc : Nat := 0
  regions : List (Option MemRegion) := []
  result : Option MemResult := none
  spaces : List Adressraum := []
  tlb : TranslationCache := {}
  active : Option Nat := none
  marken : List (Identifier × Zuruecknahme) := []

abbrev MemState := Zustand PUnit Nat UInt8 PUnit MemFrame PUnit

instance (left right : Strecke) : Decidable (left.getrennt right) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Every active mapping and every pending shootdown reserves its physical
    frames, across all spaces. Thus a different virtual address cannot reuse
    pages that still have a stale translation. -/
def MemFrame.unreserved (frame : MemFrame) (granule : Nat) (extent : Strecke) : Bool :=
  frame.spaces.all fun space =>
    decide (extent.getrennt space.tabellen) &&
    space.entries.all (fun (_, entry) =>
      decide (extent.getrennt ⟨entry.frame * granule, (entry.frame + 1) * granule⟩)) &&
    space.ausstehend.all (fun token => decide (extent.getrennt (token.frames granule)))

def MemRegion.live (region : MemRegion) (s : MemState) : Bool :=
  !region.backing.isEmpty && region.backing.all fun handle =>
    s.rechte.lebt handle.objekt && s.rechte.gen handle.objekt == handle.gen &&
    (match s.leihen handle.objekt with | .eigen => true | .verliehen _ => false)

def heldMemRegion (z : ZielDaten) (s : MemState) (c : Kontext) (slot : Nat) : Option MemRegion := do
  let region ← (s.lokal c).regions[slot]?.join
  if region.live s && (s.lokal c).unreserved z.seitengranule region.extent then some region
  else none

instance (owner extent : Strecke) : Decidable (owner.enthaelt extent) :=
  inferInstanceAs (Decidable (_ ∧ _))

def MemFrame.covered (frame : MemFrame) (s : MemState) (extent : Strecke) : Bool :=
  frame.regions.any fun slot =>
    slot.any fun region => region.live s && decide (region.extent.enthaelt extent)

def Adressraum.Aktivierbar (space : Adressraum) (z : ZielDaten) (s : MemState) (c : Kontext) : Prop :=
  space.Wohlgeformt z ∧ (s.lokal c).covered s space.tabellen ∧
  space.entries.all fun (_, entry) =>
    (s.lokal c).covered s ⟨entry.frame * z.seitengranule, (entry.frame + 1) * z.seitengranule⟩

instance (space : Adressraum) (z : ZielDaten) (s : MemState) (c : Kontext) :
    Decidable (space.Aktivierbar z s c) :=
  inferInstanceAs (Decidable (_ ∧ _))

def MemFrame.bindMarke (frame : MemFrame) (name : Identifier) (token : Zuruecknahme) :
    Option MemFrame := do
  let space ← frame.spaces[token.raum]?
  if token ∈ space.ausstehend ∧
      (frame.marken.all fun (other, bound) => decide (other.val ≠ name.val ∧ bound ≠ token)) then
    some { frame with marken := frame.marken ++ [(name, token)] }
  else none

end Gabbro.Core.Ast.LowLevel
