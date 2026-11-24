module

public import Core.Beobachtung.Unentscheidbar.Simulation.KodierInstanzen

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ast.LowLevel
open Gabbro.Core.Katalog
open Gabbro.Core.Text

/-! ## WrittenType and WrittenTypes

The two mutually recursive spellings use the same preorder code discipline as
`Ty`, with mutually recursive structural decoders and a generalized inverse
lemma over the leftover token list. -/

mutual
  def writtenTypeCode : WrittenType → List Nat
    | .bool => [0]
    | .integer signed width interval =>
        1 :: Encodable.encode signed :: Encodable.encode width :: Encodable.encode interval :: []
    | .array element count => 2 :: writtenTypeCode element ++ [Encodable.encode count]
    | .tuple first second rest =>
        3 :: writtenTypeCode first ++ writtenTypeCode second ++ writtenTypesCode rest
    | .text capacity => [4, Encodable.encode capacity]
    | .index carrier count => [5, Encodable.encode carrier, Encodable.encode count]
    | .indexOption carrier count => [6, Encodable.encode carrier, Encodable.encode count]
    | .address space => [7, Encodable.encode space]
    | .ownedRegion => [8]
    | .ptr space recht referent =>
        9 :: Encodable.encode space :: Encodable.encode recht :: writtenTypeCode referent

  def writtenTypesCode : WrittenTypes → List Nat
    | .empty => [0]
    | .next head tail => 1 :: writtenTypeCode head ++ writtenTypesCode tail

  def writtenTypeDecode : List Nat → Option (WrittenType × List Nat)
    | 0 :: rest => some (.bool, rest)
    | 1 :: s :: w :: i :: rest => do
        let signed : Bool ← Encodable.decode s
        let width : Nat ← Encodable.decode w
        let interval : Option (Int × Int) ← Encodable.decode i
        some (.integer signed width interval, rest)
    | 2 :: rest => do
        let (element, r1) ← writtenTypeDecode rest
        match r1 with
        | count :: r2 =>
            let c : Nat ← Encodable.decode count
            some (.array element c, r2)
        | _ => none
    | 3 :: rest => do
        let (first, r1) ← writtenTypeDecode rest
        let (second, r2) ← writtenTypeDecode r1
        let (tail, r3) ← writtenTypesDecode r2
        some (.tuple first second tail, r3)
    | 4 :: cap :: rest => do
        let c : Nat ← Encodable.decode cap
        some (.text c, rest)
    | 5 :: carrier :: count :: rest => do
        let car : Identifier ← Encodable.decode carrier
        let c : Nat ← Encodable.decode count
        some (.index car c, rest)
    | 6 :: carrier :: count :: rest => do
        let car : Identifier ← Encodable.decode carrier
        let c : Nat ← Encodable.decode count
        some (.indexOption car c, rest)
    | 7 :: space :: rest => do
        let s : AddressSpace ← Encodable.decode space
        some (.address s, rest)
    | 8 :: rest => some (.ownedRegion, rest)
    | 9 :: space :: recht :: rest => do
        let s : AddressSpace ← Encodable.decode space
        let r : PtrRecht ← Encodable.decode recht
        let (referent, r') ← writtenTypeDecode rest
        some (.ptr s r referent, r')
    | _ => none

  def writtenTypesDecode : List Nat → Option (WrittenTypes × List Nat)
    | 0 :: rest => some (.empty, rest)
    | 1 :: rest => do
        let (head, r1) ← writtenTypeDecode rest
        let (tail, r2) ← writtenTypesDecode r1
        some (.next head tail, r2)
    | _ => none
end

mutual
  lemma writtenTypeDecode_code : ∀ (w : WrittenType) (rest : List Nat),
      writtenTypeDecode (writtenTypeCode w ++ rest) = some (w, rest) := by
    intro w
    induction w <;> (intro rest; simp [writtenTypeCode, writtenTypeDecode,
      writtenTypesDecode_code, writtenTypesCode, writtenTypesDecode, *, List.append_assoc])

  lemma writtenTypesDecode_code : ∀ (w : WrittenTypes) (rest : List Nat),
      writtenTypesDecode (writtenTypesCode w ++ rest) = some (w, rest) := by
    intro w
    induction w <;> (intro rest; simp [writtenTypesCode, writtenTypesDecode, *, List.append_assoc])
end

instance : Encodable WrittenType :=
  Encodable.ofLeftInjection
    (fun w => Encodable.encode (writtenTypeCode w))
    (fun n => do
      let toks : List Nat ← Encodable.decode n
      let (w, rest) ← writtenTypeDecode toks
      if rest.isEmpty then some w else none)
    (by
      intro w
      rw [Encodable.encodek, writtenTypeDecode_code]
      simp)

instance : Encodable WrittenTypes :=
  Encodable.ofLeftInjection
    (fun w => Encodable.encode (writtenTypesCode w))
    (fun n => do
      let toks : List Nat ← Encodable.decode n
      let (w, rest) ← writtenTypesDecode toks
      if rest.isEmpty then some w else none)
    (by
      intro w
      rw [Encodable.encodek, writtenTypesDecode_code]
      simp)

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
