module

public import Core.Ast.LowLevel.DeviceSyntax

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel.Device

open Katalog Maschine

/-- An owned region descriptor. Its checked handle, extent and rights
    determine the loan; its start address alone grants no device access. -/
structure LoanRegion where
  handle : Griff
  extent : Strecke
  read : Bool
  write : Bool

def LoanRegion.loan (region : LoanRegion) : Katalog.Leihe :=
  ⟨Nat.pair region.handle.objekt region.handle.gen, region.extent, region.read, region.write⟩

def LoanRegion.held (region : LoanRegion) (s : State) (c : Kontext) : Prop :=
  s.rechte.Gueltig region.handle ∧
  s.leihen region.handle.objekt = .eigen ∧
  (∀ address, address ∈ s.buchung.umfang region.handle.objekt ↔ region.extent.drin address) ∧
  (region.read = true → s.buchung.haelt c region.handle .lesen) ∧
  (region.write = true → s.buchung.haelt c region.handle .schreiben) ∧
  (∀ other right, s.buchung.haelt other region.handle right → other = c)

structure DmaMapping where
  extent : Strecke
  read : Bool
  write : Bool

def DmaMapping.covers (mapping : DmaMapping) (loan : Katalog.Leihe) : Prop :=
  mapping.extent.enthaelt loan.region ∧
  (loan.read = true → mapping.read = true) ∧
  (loan.write = true → mapping.write = true)

inductive Revocation where
  | live
  | stopped
  | revoked
  | invalidated
  deriving DecidableEq

structure LoanSession where
  region : LoanRegion
  revocation : Revocation := .live
  pending : List DmaZugriff := []

structure LoanState where
  machine : State
  mappings : Objekt → Option DmaMapping
  sessions : Objekt → Option LoanSession


def Binding.Lent (binding : Binding k) (s : LoanState) (c : Kontext) (session : LoanSession) : Prop :=
  s.sessions binding.object = some session ∧
  s.machine.buchung.geraet binding.object = some (c, .verliehen session.region.loan) ∧
  (s.machine.lokal c).phases binding.object = some (.lending session.region.loan) ∧
  s.machine.leihen session.region.handle.objekt = .verliehen binding.object ∧
  s.machine.rechte.Gueltig session.region.handle

/-- Update both typestate ledgers at the same cut. -/
def setLoan (s : LoanState) (c : Kontext) (device : Objekt) (region : Nat)
    (phase : GeraetePhase) (deviceRight : Aussen.Vollmacht) (regionRight : Maschine.Leihe Objekt)
    (session : Option LoanSession) : LoanState :=
  { s with
    sessions := Function.update s.sessions device session
    machine := { setFrame s.machine c
        { s.machine.lokal c with phases := Function.update (s.machine.lokal c).phases device (some phase) } with
      leihen := Function.update s.machine.leihen region regionRight
      buchung := { s.machine.buchung with
        geraet := Function.update s.machine.buchung.geraet device (some (c, deviceRight)) } } }

def lend (binding : Binding k) (region : LoanRegion) (c : Kontext)
    (before : LoanState) (event : Ereignis) (after : LoanState) : Prop :=
  region.held before.machine c ∧
  before.machine.buchung.geraet binding.object = some (c, .frei) ∧
  (before.machine.lokal c).phases binding.object = some .ready ∧
  (before.machine.lokal c).pending = none ∧ before.sessions binding.object = none ∧
  (∃ mapping, before.mappings binding.object = some mapping ∧ mapping.covers region.loan) ∧
  GeraeteUebergang binding.row k.plattform.ziel .ready (.lend region.loan) (.lending region.loan) ∧
  event = .geraet binding.object.endpoint (.lend region.loan) ∧
  after = setLoan before c binding.object region.handle.objekt (.lending region.loan)
    (.verliehen region.loan) (.verliehen binding.object) (some ⟨region, .live, []⟩)

/-- The source supplies the names of the owned operands. Their identities
    are resolved in the accepted unit before the lending rule applies. -/
structure LendSource where
  region : Identifier
  device : Identifier

def LendSource.tokens (source : LendSource) : List Text.Token :=
  [keyword "lend", .word source.region.val, keyword "to", .word source.device.val, semicolon]

def LendSource.printPieces (source : LendSource) : List Text.PrintedToken :=
  [lowWord 'l' "end", source.region.print, lowWord 't' "o", source.device.print, printSemicolon]

def LendSource.Parse (text : Text.RawText) (source : LendSource) : Prop :=
  Text.Parse (Text.tokenGrammar (fun tokens tree => tokens = LendSource.tokens tree)) text source

end Gabbro.Core.Ast.LowLevel.Device
