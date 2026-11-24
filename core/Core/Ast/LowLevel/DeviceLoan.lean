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
  prepared : Griff
  extent : Strecke
  read : Bool
  write : Bool

def DmaMapping.covers (mapping : DmaMapping) (region : LoanRegion) : Prop :=
  let loan := region.loan
  mapping.prepared = region.handle ∧ mapping.extent.enthaelt loan.region ∧
  (loan.read = true → mapping.read = true) ∧
  (loan.write = true → mapping.write = true)

inductive Revocation where
  | live
  | stopped
  | revoked
  | invalidated
  | synchronized
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
  (∃ mapping, before.mappings binding.object = some mapping ∧ mapping.covers region) ∧
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

/-- Capabilities identify the current loan. The transfer still has to satisfy
    its permission, direction, relative extent and current translation. -/
def DmaBefugt (binding : Binding k) (s : LoanState) (c : Kontext)
    (session : LoanSession) (access : DmaZugriff) : Prop :=
  binding.Lent s c session ∧ session.revocation = .live ∧
  (∃ mapping, s.mappings binding.object = some mapping ∧ mapping.covers session.region) ∧
  dma binding.row (.lending session.region.loan) session.region.loan access

def setSession (s : LoanState) (device : Objekt) (session : LoanSession) : LoanState :=
  { s with sessions := Function.update s.sessions device (some session) }

/-- Accepting a request puts it in flight. Completion removes that exact
    request, and revocation can wait for all outstanding completions. -/
inductive DmaStep (binding : Binding k) (c : Kontext) (before : LoanState) :
    Ereignis → LoanState → Prop where
  | issue {session access} (allowed : DmaBefugt binding before c session access) :
    DmaStep binding c before (.dma binding.object.endpoint access)
      (setSession before binding.object { session with pending := session.pending ++ [access] })

inductive RevocationEvent where
  | stopped (device : Objekt)
  | unmapped (device : Objekt)
  | translationCacheInvalidated (device : Objekt)
  | completed (device : Objekt) (request : DmaZugriff)
  | cpuCacheSynchronized (device : Objekt)

/-- The protocol consumes completion events already attributed to this
    device. Revocation disables new requests before it drains old ones. -/
inductive RevokeStep (binding : Binding k) (c : Kontext) (before : LoanState) :
    RevocationEvent → LoanState → Prop where
  | stop {session} (lent : binding.Lent before c session) (live : session.revocation = .live) :
    RevokeStep binding c before (.stopped binding.object)
      (setSession before binding.object { session with revocation := .stopped })
  | revoke {session} (lent : binding.Lent before c session) (stopped : session.revocation = .stopped) :
    RevokeStep binding c before (.unmapped binding.object)
      { setSession before binding.object { session with revocation := .revoked } with
        mappings := Function.update before.mappings binding.object none }
  | invalidate {session} (lent : binding.Lent before c session) (revoked : session.revocation = .revoked)
      (unmapped : before.mappings binding.object = none) :
    RevokeStep binding c before (.translationCacheInvalidated binding.object)
      (setSession before binding.object { session with revocation := .invalidated })
  | complete {session access} (lent : binding.Lent before c session) (pending : access ∈ session.pending) :
    RevokeStep binding c before (.completed binding.object access)
      (setSession before binding.object { session with pending := session.pending.erase access })
  | synchronize {session} (lent : binding.Lent before c session) (invalidated : session.revocation = .invalidated)
      (drained : session.pending = []) :
    RevokeStep binding c before (.cpuCacheSynchronized binding.object)
      (setSession before binding.object { session with revocation := .synchronized })

def returnRegion (before : LoanState) (c : Kontext) (device : Objekt) (region : LoanRegion) : LoanState :=
  let returned := setLoan before c device region.handle.objekt .ready .frei .eigen none
  let rights := (returned.machine.rechte.widerrufen region.handle.objekt).beleben region.handle.objekt
  let refreshed := rights.ausgeben region.handle.objekt
  { returned with machine := { returned.machine with
      rechte := rights
      buchung := { returned.machine.buchung with
        haelt := fun holder handle right =>
          if handle.objekt = region.handle.objekt then
            holder = c ∧ handle = refreshed ∧ before.machine.buchung.haelt c region.handle right
          else before.machine.buchung.haelt holder handle right } } }

inductive ReclaimResult where
  | returned (handle : Griff)
  | stuck

def takeBack (binding : Binding k) (c : Kontext) (session : LoanSession)
    (before : LoanState) : ReclaimResult → Option Ereignis → LoanState → Prop
  | .returned handle, event, after =>
    binding.Lent before c session ∧ session.revocation = .synchronized ∧
    before.mappings binding.object = none ∧ session.pending = [] ∧
    GeraeteUebergang binding.row k.plattform.ziel (.lending session.region.loan)
      (.takeBack session.region.loan) .ready ∧
    event = some (.geraet binding.object.endpoint (.takeBack session.region.loan)) ∧
    handle = after.machine.rechte.ausgeben session.region.handle.objekt ∧
    after = returnRegion before c binding.object session.region
  | .stuck, event, after =>
    binding.Lent before c session ∧ session.revocation ≠ .live ∧
    (session.revocation ≠ .synchronized ∨ session.pending ≠ []) ∧ event = none ∧
    after = { before with mappings := Function.update before.mappings binding.object none }

structure TakeBackSource where
  region : Identifier
  device : Identifier
  handler : Identifier

def TakeBackSource.tokens (source : TakeBackSource) : List Text.Token :=
  [keyword "take", keyword "back", .word source.region.val, keyword "from",
    .word source.device.val, keyword "else", .word source.handler.val, semicolon]

def TakeBackSource.printPieces (source : TakeBackSource) : List Text.PrintedToken :=
  [lowWord 't' "ake", lowWord 'b' "ack", source.region.print, lowWord 'f' "rom",
    source.device.print, lowWord 'e' "lse", source.handler.print, printSemicolon]

def TakeBackSource.Parse (text : Text.RawText) (source : TakeBackSource) : Prop :=
  Text.Parse (Text.tokenGrammar (fun tokens tree => tokens = TakeBackSource.tokens tree)) text source

def TakeBackSource.resume (source : TakeBackSource) : ReclaimResult → Option Identifier
  | .returned _handle => none
  | .stuck => some source.handler

/-- Resolution supplies capabilities already in scope. It never converts a
    physical or device address into a lendable region. -/
structure LoanNames (k : Katalog) where
  region : Identifier → Option LoanRegion
  device : Identifier → Option (Binding k)

def LoanNames.resolve (names : LoanNames k) (region device : Identifier) :
    Option (LoanRegion × Binding k) := do
  let region ← names.region region
  let device ← names.device device
  pure (region, device)

def LendSource.elaborate (source : LendSource) (names : LoanNames k) :=
  names.resolve source.region source.device

def TakeBackSource.elaborate (source : TakeBackSource) (names : LoanNames k) :=
  names.resolve source.region source.device

def LendSource.Step (source : LendSource) (names : LoanNames k) (c : Kontext)
    (before : LoanState) (event : Ereignis) (after : LoanState) : Prop :=
  ∃ region binding, source.elaborate names = some (region, binding) ∧
    lend binding region c before event after

def TakeBackSource.Step (source : TakeBackSource) (names : LoanNames k) (c : Kontext)
    (before : LoanState) (result : ReclaimResult) (event : Option Ereignis) (after : LoanState) : Prop :=
  ∃ binding session, source.elaborate names = some (session.region, binding) ∧
    takeBack binding c session before result event after

end Gabbro.Core.Ast.LowLevel.Device
