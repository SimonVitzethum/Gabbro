module

public import Core.Beobachtung.Unentscheidbar.Simulation.KodierInstanzen

noncomputable section

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ast.LowLevel
open Gabbro.Core.Katalog
open Gabbro.Core.Text

/-! ## WrittenType and WrittenTypes

The two mutually recursive spellings use the same first-order Nat codes as
`Ty`: a constructor tag paired with its children, shifted by one so every
child code is strictly smaller. The decoders are partial and recursive on that
strictly smaller child code, which makes the termination argument local. -/

mutual
  def writtenTypeCode : WrittenType → Nat
    | .bool => Nat.pair 0 0 + 1
    | .integer signed width interval =>
        Nat.pair 1 (Nat.pair (Encodable.encode signed)
          (Nat.pair (Encodable.encode width) (Encodable.encode interval))) + 1
    | .array element count =>
        Nat.pair 2 (Nat.pair (writtenTypeCode element) (Encodable.encode count)) + 1
    | .tuple first second rest =>
        Nat.pair 3 (Nat.pair (writtenTypeCode first)
          (Nat.pair (writtenTypeCode second) (writtenTypesCode rest))) + 1
    | .text capacity => Nat.pair 4 (Encodable.encode capacity) + 1
    | .index carrier count =>
        Nat.pair 5 (Nat.pair (Encodable.encode carrier) (Encodable.encode count)) + 1
    | .indexOption carrier count =>
        Nat.pair 6 (Nat.pair (Encodable.encode carrier) (Encodable.encode count)) + 1
    | .address space => Nat.pair 7 (Encodable.encode space) + 1
    | .ownedRegion => Nat.pair 8 0 + 1
    | .ptr space recht referent =>
        Nat.pair 9 (Nat.pair (Encodable.encode space)
          (Nat.pair (Encodable.encode recht) (writtenTypeCode referent))) + 1

  def writtenTypesCode : WrittenTypes → Nat
    | .empty => Nat.pair 0 0 + 1
    | .next head tail =>
        Nat.pair 1 (Nat.pair (writtenTypeCode head) (writtenTypesCode tail)) + 1

  def writtenTypeOfCode : Nat → Option WrittenType
    | 0 => none
    | n + 1 =>
      let p := n.unpair
      let payload := p.2
      have hp : payload < n + 1 := lt_of_le_of_lt (Nat.unpair_right_le n) (Nat.lt_succ_self n)
      have ha : payload.unpair.1 < n + 1 := lt_of_le_of_lt (Nat.unpair_left_le payload) hp
      have hb : payload.unpair.2 < n + 1 := lt_of_le_of_lt (Nat.unpair_right_le payload) hp
      have hb1 : payload.unpair.2.unpair.1 < n + 1 :=
        lt_of_le_of_lt (Nat.unpair_left_le payload.unpair.2) hb
      have hb2 : payload.unpair.2.unpair.2 < n + 1 :=
        lt_of_le_of_lt (Nat.unpair_right_le payload.unpair.2) hb
      match p.1 with
      | 0 => some .bool
      | 1 => do
          let signed : Bool ← Encodable.decode payload.unpair.1
          let width : Nat ← Encodable.decode payload.unpair.2.unpair.1
          let interval : Option (Int × Int) ← Encodable.decode payload.unpair.2.unpair.2
          some (.integer signed width interval)
      | 2 => do
          let element ← writtenTypeOfCode payload.unpair.1
          let count : Nat ← Encodable.decode payload.unpair.2
          some (.array element count)
      | 3 => do
          let first ← writtenTypeOfCode payload.unpair.1
          let second ← writtenTypeOfCode payload.unpair.2.unpair.1
          let rest ← writtenTypesOfCode payload.unpair.2.unpair.2
          some (.tuple first second rest)
      | 4 => do
          let capacity : Nat ← Encodable.decode payload
          some (.text capacity)
      | 5 => do
          let carrier : Identifier ← Encodable.decode payload.unpair.1
          let count : Nat ← Encodable.decode payload.unpair.2
          some (.index carrier count)
      | 6 => do
          let carrier : Identifier ← Encodable.decode payload.unpair.1
          let count : Nat ← Encodable.decode payload.unpair.2
          some (.indexOption carrier count)
      | 7 => do
          let space : AddressSpace ← Encodable.decode payload
          some (.address space)
      | 8 => some .ownedRegion
      | 9 => do
          let space : AddressSpace ← Encodable.decode payload.unpair.1
          let recht : PtrRecht ← Encodable.decode payload.unpair.2.unpair.1
          let referent ← writtenTypeOfCode payload.unpair.2.unpair.2
          some (.ptr space recht referent)
      | _ => none

  def writtenTypesOfCode : Nat → Option WrittenTypes
    | 0 => none
    | n + 1 =>
      let p := n.unpair
      let payload := p.2
      have hp : payload < n + 1 := lt_of_le_of_lt (Nat.unpair_right_le n) (Nat.lt_succ_self n)
      have ha : payload.unpair.1 < n + 1 := lt_of_le_of_lt (Nat.unpair_left_le payload) hp
      have hb : payload.unpair.2 < n + 1 := lt_of_le_of_lt (Nat.unpair_right_le payload) hp
      match p.1 with
      | 0 => some .empty
      | 1 => do
          let head ← writtenTypeOfCode payload.unpair.1
          let tail ← writtenTypesOfCode payload.unpair.2
          some (.next head tail)
      | _ => none
end

mutual
  lemma writtenTypeCode_ofCode (w : WrittenType) :
      writtenTypeOfCode (writtenTypeCode w) = some w := by
    induction w <;> simp [writtenTypeCode, writtenTypeOfCode, writtenTypesCode_ofCode,
      writtenTypesCode, writtenTypesOfCode, *]

  lemma writtenTypesCode_ofCode (w : WrittenTypes) :
      writtenTypesOfCode (writtenTypesCode w) = some w := by
    induction w <;> simp [writtenTypesCode, writtenTypesOfCode, writtenTypeCode_ofCode,
      writtenTypeCode, writtenTypeOfCode, *]
end

instance : Encodable WrittenType :=
  Encodable.ofLeftInjection writtenTypeCode writtenTypeOfCode writtenTypeCode_ofCode

instance : Encodable WrittenTypes :=
  Encodable.ofLeftInjection writtenTypesCode writtenTypesOfCode writtenTypesCode_ofCode

/-! ## RegionInitializer -/

def regionInitializerCode (i : RegionInitializer) : Nat :=
  Encodable.encode <| match i with
    | .address => none
    | .view written _ => some (Encodable.encode written)

noncomputable def regionInitializerDecode (n : Nat) : Option RegionInitializer := by
  classical
  let o : Option Nat ← Encodable.decode n
  match o with
  | none => exact some .address
  | some w =>
      let written : WrittenType ← Encodable.decode w
      if h : written.valid [] then some (.view written h) else none

instance : Encodable RegionInitializer :=
  Encodable.ofLeftInjection regionInitializerCode regionInitializerDecode (by
    intro i
    cases i with
    | address => simp [regionInitializerCode, regionInitializerDecode, Encodable.encodek]
    | view written valid =>
        classical
        simp [regionInitializerCode, regionInitializerDecode, Encodable.encodek, valid])

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
