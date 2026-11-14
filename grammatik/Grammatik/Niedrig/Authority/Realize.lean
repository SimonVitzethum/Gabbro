module

public import Grammatik.Niedrig.Authority.Layout
public import Grammatik.Niedrig.Boot.Transition
public import Grammatik.Niedrig.Bytes.Bytes

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

variable {D : Deklaration}

/-- Placement of a provider reservation in a carrier, measured in ELEMENTS.
    The provider has no backing or table coordinate. This explicit software
    receipt supplies that missing correspondence; neither freshness nor
    LayoutOk can determine it from numeric addresses alone. Partial-byte
    spans may use a subrange of the reservation. OPEN carriers have no
    element ceiling, but every reservation remains finite. -/
structure CarrierReservation (lay : AdressLayout D) (table : D.Tab)
    (reservation : Anbieter.Strecke) where
  first : Nat
  elements : Nat
  positiveElements : 0 < elements
  positiveWidth : 0 < lay.breite table
  start : reservation.von = lay.basis table + first * lay.breite table
  finish : reservation.bis = lay.basis table + (first + elements) * lay.breite table
  extent : D.offen table = true ∨ first + elements ≤ (D.count table).toNat

/-- A span is backed by a live, resident provider reservation placed in its
    actual table. The backing equality is indispensable: provider offsets
    alone cannot establish an address-space identity. -/
structure ProviderSpan (lay : AdressLayout D) (state : Anbieter.Zust)
    (span : Span D) where
  reservation : Anbieter.Strecke
  live : reservation ∈ state.lebend
  carrier : CarrierReservation lay span.table reservation
  backing : span.space.backing = lay.raum span.table
  included : ∀ byte, span.range.drin byte → reservation.drin byte
  resident : ∀ byte, span.range.drin byte → state.ram byte = true

/-- Provenance in the EXISTING owner ledger, rooted at a firmware grant.
    Mint edges retain the exact recordMint equation and declaration. As in
    OwnerState itself, this is metadata after the binding returned; the
    canonical G invocation and its software duty remain P2/C08 obligations.
    There is no constructor admitting an arbitrary final ledger or token. -/
inductive OwnerMintChain (names : OwnerNamespace D)
    (initial : OwnerState D) (root : ArenaOwnership.Frame) (grant : OwnerToken D) :
    OwnerState D → ArenaOwnership.Frame → OwnerToken D → Prop where
  | initial : OwnerMintChain names initial root grant initial root grant
  | mint {before after : OwnerState D} {frame : ArenaOwnership.Frame}
      {old token : OwnerToken D}
      (previous : OwnerMintChain names initial root grant before frame old)
      (declaration : OwnerMintDecl D)
      (minted : OwnerState.recordMint names declaration before frame = some (after, token)) :
      OwnerMintChain names initial root grant after frame token
  | handoff {before after : OwnerState D} {source into : ArenaOwnership.Frame}
      {old token : OwnerToken D}
      (previous : OwnerMintChain names initial root grant before source old)
      (moved : OwnerState.transfer names before source into old = some (after, token)) :
      OwnerMintChain names initial root grant after into token

/-- The byte state supplied AT firmware entry, independent of reservation
    residency (committing RAM does not initialize its contents). Only bytes
    covered by this authority may arrive initialized. Every span marked
    initialized really has all its bytes supplied, with bounded byte values.

    L3b.Erreichbar currently starts only at leererZustand. This receipt is
    deliberately not a proof of that predicate: a later package must add an
    explicit firmware-rooted history and distinguish firmware provenance from
    successful program writes. In particular no fictitious write is asserted. -/
structure FirmwareMemory (a : Authority D) where
  bytes : Gabbro.Grammatik.Niedrig.Bytes.ByteState
  byteValues : Gabbro.Grammatik.Niedrig.Bytes.byteOk bytes
  supplied : ∀ span ∈ a.spans, span.initialized = true →
    ∀ byte, span.range.drin byte → bytes.init span.space.backing byte = true
  confined : ∀ backing byte, bytes.init backing byte = true →
    ∃ span ∈ a.spans, span.space.backing = backing ∧
      span.initialized = true ∧ span.range.drin byte

/-- A provider run, actual carrier placements and firmware-origin grant chain.
    All layout placement and initial byte obligations are explicit user or
    environment receipts. Realizes is a conclusion, never a field, and the
    firmware contract need not mention it. This does not yet extend ZielX.

    Anbieter uses one numeric reservation arena. Thus this record describes
    one provider arena, with an explicit backing for each covered span; its
    numeric freshness is stronger than separation across distinct backings.
    It must not be used to infer numeric overlap is impossible for unrelated
    provider arenas. -/
structure BootProviderRecord {P I : Type} (b : BootContract D P I)
    (a : Authority D) (lay : AdressLayout D) where
  granule : Nat
  positiveGranule : 0 < granule
  providerTrace : List Anbieter.Ereig
  providerFinal : Anbieter.Zust
  run : Anbieter.Lauf granule Anbieter.Zust.leer providerTrace providerFinal
  covers : ∀ span ∈ a.spans, ProviderSpan lay providerFinal span
  firmwareAuthority : Authority D
  firmwareContext : Context D P I
  boot : FirmwareEntry b firmwareAuthority firmwareContext
  names : firmwareAuthority.names = a.names
  firmwareMemory : FirmwareMemory firmwareAuthority
  owners : OwnerState D
  frame : ArenaOwnership.Frame
  mintChain : OwnerMintChain a.names firmwareContext.owners firmwareContext.frame
    firmwareAuthority.token owners frame a.token

end Gabbro.Grammatik.LowLevel
