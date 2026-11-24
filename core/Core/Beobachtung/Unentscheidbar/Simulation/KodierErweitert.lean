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
open Nat.Partrec

/-! ## WrittenType and WrittenTypes

The mutually recursive spellings use the same `Code` trees as `Ty`; the
decoders are structural on the tree and the inverse lemmas are equation-defined
recursive theorems. -/

mutual
  def writtenTypeZuCode : WrittenType → Code
    | .bool => Code.pair (natZuCode 0) Code.zero
    | .integer signed width interval =>
        Code.pair (natZuCode 1) (Code.pair (natZuCode (Encodable.encode signed))
          (Code.pair (natZuCode (Encodable.encode width))
            (natZuCode (Encodable.encode interval))))
    | .array element count =>
        Code.pair (natZuCode 2) (Code.pair (writtenTypeZuCode element)
          (natZuCode (Encodable.encode count)))
    | .tuple first second rest =>
        Code.pair (natZuCode 3) (Code.pair (writtenTypeZuCode first)
          (Code.pair (writtenTypeZuCode second) (writtenTypesZuCode rest)))
    | .text capacity => Code.pair (natZuCode 4) (natZuCode (Encodable.encode capacity))
    | .index carrier count =>
        Code.pair (natZuCode 5) (Code.pair (natZuCode (Encodable.encode carrier))
          (natZuCode (Encodable.encode count)))
    | .indexOption carrier count =>
        Code.pair (natZuCode 6) (Code.pair (natZuCode (Encodable.encode carrier))
          (natZuCode (Encodable.encode count)))
    | .address space => Code.pair (natZuCode 7) (natZuCode (Encodable.encode space))
    | .ownedRegion => Code.pair (natZuCode 8) Code.zero
    | .ptr space recht referent =>
        Code.pair (natZuCode 9) (Code.pair (natZuCode (Encodable.encode space))
          (Code.pair (natZuCode (Encodable.encode recht)) (writtenTypeZuCode referent)))

  def writtenTypesZuCode : WrittenTypes → Code
    | .empty => Code.pair (natZuCode 0) Code.zero
    | .next head tail =>
        Code.pair (natZuCode 1) (Code.pair (writtenTypeZuCode head) (writtenTypesZuCode tail))

  def writtenTypeVonCode : Code → Option WrittenType
    | Code.pair tag kids =>
      match codeZuNat tag with
      | some 0 =>
        match kids with
        | Code.zero => some .bool
        | _ => none
      | some 1 =>
        match kids with
        | Code.pair s (Code.pair w i) => do
            let sn : Nat ← codeZuNat s
            let wn : Nat ← codeZuNat w
            let signed : Bool ← Encodable.decode sn
            let width : Nat ← Encodable.decode wn
            let ivn : Nat ← codeZuNat i
            let interval : Option (Int × Int) ← Encodable.decode ivn
            some (.integer signed width interval)
        | _ => none
      | some 2 =>
        match kids with
        | Code.pair el cnt => do
            let element ← writtenTypeVonCode el
            let cntn : Nat ← codeZuNat cnt
            let count : Nat ← Encodable.decode cntn
            some (.array element count)
        | _ => none
      | some 3 =>
        match kids with
        | Code.pair first (Code.pair second tail) => do
            let first' ← writtenTypeVonCode first
            let second' ← writtenTypeVonCode second
            let tail' ← writtenTypesVonCode tail
            some (.tuple first' second' tail')
        | _ => none
      | some 4 => do
          let capn : Nat ← codeZuNat kids
          let capacity : Nat ← Encodable.decode capn
          some (.text capacity)
      | some 5 =>
        match kids with
        | Code.pair carrier count => do
            let carn : Nat ← codeZuNat carrier
            let cntn : Nat ← codeZuNat count
            let car : Identifier ← Encodable.decode carn
            let cnt : Nat ← Encodable.decode cntn
            some (.index car cnt)
        | _ => none
      | some 6 =>
        match kids with
        | Code.pair carrier count => do
            let carn : Nat ← codeZuNat carrier
            let cntn : Nat ← codeZuNat count
            let car : Identifier ← Encodable.decode carn
            let cnt : Nat ← Encodable.decode cntn
            some (.indexOption car cnt)
        | _ => none
      | some 7 => do
          let sn : Nat ← codeZuNat kids
          let space : AddressSpace ← Encodable.decode sn
          some (.address space)
      | some 8 =>
        match kids with
        | Code.zero => some .ownedRegion
        | _ => none
      | some 9 =>
        match kids with
        | Code.pair space (Code.pair recht referent) => do
            let sn : Nat ← codeZuNat space
            let rn : Nat ← codeZuNat recht
            let space' : AddressSpace ← Encodable.decode sn
            let recht' : PtrRecht ← Encodable.decode rn
            let referent' ← writtenTypeVonCode referent
            some (.ptr space' recht' referent')
        | _ => none
      | _ => none
    | _ => none

  def writtenTypesVonCode : Code → Option WrittenTypes
    | Code.pair tag kids =>
      match codeZuNat tag with
      | some 0 =>
        match kids with
        | Code.zero => some .empty
        | _ => none
      | some 1 =>
        match kids with
        | Code.pair head tail => do
            let head' ← writtenTypeVonCode head
            let tail' ← writtenTypesVonCode tail
            some (.next head' tail')
        | _ => none
      | _ => none
    | _ => none
end

mutual
  theorem writtenTypeCode_ofCode : ∀ w : WrittenType,
    writtenTypeVonCode (writtenTypeZuCode w) = some w
  | .bool => by
      unfold writtenTypeVonCode writtenTypeZuCode
      simp only [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .integer signed width interval => by
      unfold writtenTypeVonCode writtenTypeZuCode
      simp only [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .array element count => by
      have ih := writtenTypeCode_ofCode element
      unfold writtenTypeVonCode writtenTypeZuCode
      simp only [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, ih]
  | .tuple first second rest => by
      have ih1 := writtenTypeCode_ofCode first
      have ih2 := writtenTypeCode_ofCode second
      have ih3 := writtenTypesCode_ofCode rest
      unfold writtenTypeVonCode writtenTypeZuCode
      simp only [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, ih1, ih2, ih3,
        writtenTypesVonCode, writtenTypesZuCode]
  | .text capacity => by
      unfold writtenTypeVonCode writtenTypeZuCode
      simp only [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .index carrier count => by
      unfold writtenTypeVonCode writtenTypeZuCode
      simp only [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .indexOption carrier count => by
      unfold writtenTypeVonCode writtenTypeZuCode
      simp only [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .address space => by
      unfold writtenTypeVonCode writtenTypeZuCode
      simp only [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .ownedRegion => by
      unfold writtenTypeVonCode writtenTypeZuCode
      simp only [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .ptr space recht referent => by
      have ih := writtenTypeCode_ofCode referent
      unfold writtenTypeVonCode writtenTypeZuCode
      simp only [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, ih]

  theorem writtenTypesCode_ofCode : ∀ w : WrittenTypes,
    writtenTypesVonCode (writtenTypesZuCode w) = some w
  | .empty => by
      unfold writtenTypesVonCode writtenTypesZuCode
      simp only [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one]
  | .next head tail => by
      have ih1 := writtenTypeCode_ofCode head
      have ih2 := writtenTypesCode_ofCode tail
      unfold writtenTypesVonCode writtenTypesZuCode
      simp only [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, ih1, ih2,
        writtenTypeVonCode, writtenTypeZuCode]
end

instance : Encodable WrittenType :=
  Encodable.ofLeftInjection
    (fun w => Encodable.encode (writtenTypeZuCode w))
    (fun n => (Encodable.decode n).bind writtenTypeVonCode)
    (by intro w; simp only [Encodable.encodek, writtenTypeCode_ofCode, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one])

instance : Encodable WrittenTypes :=
  Encodable.ofLeftInjection
    (fun w => Encodable.encode (writtenTypesZuCode w))
    (fun n => (Encodable.decode n).bind writtenTypesVonCode)
    (by intro w; simp only [Encodable.encodek, writtenTypesCode_ofCode, Option.map_some, Option.bind_some, Option.some.injEq, Nat.succ_eq_add_one, Nat.add_one])

/-! ## RegionInitializer -/

noncomputable def viewRegion (written : WrittenType) : Option RegionInitializer := by
  classical
  exact if h : written.valid [] then Option.some (.view written h) else Option.none

def regionInitializerCode (i : RegionInitializer) : Nat :=
  match i with
  | .address => 0
  | .view written _ => Encodable.encode written + 1

noncomputable def regionInitializerDecode (n : Nat) : Option RegionInitializer :=
  match n with
  | 0 => Option.some .address
  | k + 1 => do
      let written : WrittenType ← Encodable.decode k
      viewRegion written

instance : Encodable RegionInitializer :=
  Encodable.ofLeftInjection regionInitializerCode regionInitializerDecode (by
    intro i
    cases i with
    | address => rfl
    | view written valid =>
        classical
        simp only [regionInitializerCode, regionInitializerDecode, Encodable.encodek, viewRegion, valid])

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
