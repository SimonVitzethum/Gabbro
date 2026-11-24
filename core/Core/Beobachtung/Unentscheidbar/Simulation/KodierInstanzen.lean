module

public import Core.Beobachtung.Unentscheidbar.Simulation.Substrat
public import Init.Data.Char.Lemmas

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ast.LowLevel
open Gabbro.Core.Katalog
open Gabbro.Core.Text

/-! ## Char and the finite enumerations

Every instance below is an explicit left injection into an already-encodable
type. No derive handler, macro or syntax is used. -/

instance : Encodable Char :=
  Encodable.ofLeftInjection Char.toNat (fun n => some (Char.ofNat n)) (by
    intro c
    simp only [Char.ofNat_toNat])

def arithCode : Arith → Nat
  | .add => 0
  | .mul => 1
  | .sub => 2

def arithOfNat : Nat → Arith
  | 0 => .add
  | 1 => .mul
  | _ => .sub

instance : Encodable Arith :=
  Encodable.ofLeftInverse arithCode arithOfNat (by intro a; cases a <;> rfl)

def compareCode : Compare → Nat
  | .eq => 0
  | .ne => 1
  | .lt => 2
  | .le => 3
  | .gt => 4
  | .ge => 5

def compareOfNat : Nat → Compare
  | 0 => .eq
  | 1 => .ne
  | 2 => .lt
  | 3 => .le
  | 4 => .gt
  | _ => .ge

instance : Encodable Compare :=
  Encodable.ofLeftInverse compareCode compareOfNat (by intro a; cases a <;> rfl)

def carrierAccessCode : CarrierAccess → Nat
  | .read => 0
  | .write => 1

def carrierAccessOfNat : Nat → CarrierAccess
  | 0 => .read
  | _ => .write

instance : Encodable CarrierAccess :=
  Encodable.ofLeftInverse carrierAccessCode carrierAccessOfNat (by intro a; cases a <;> rfl)

def ptrRechtCode : PtrRecht → Nat
  | .r => 0
  | .w => 1
  | .rw => 2

def ptrRechtOfNat : Nat → PtrRecht
  | 0 => .r
  | 1 => .w
  | _ => .rw

instance : Encodable PtrRecht :=
  Encodable.ofLeftInverse ptrRechtCode ptrRechtOfNat (by intro a; cases a <;> rfl)

def addressSpaceCode : AddressSpace → Nat
  | .physical => 0
  | .virtual => 1
  | .port => 2
  | .guestPhysical => 3
  | .ioVirtual => 4

def addressSpaceOfNat : Nat → AddressSpace
  | 0 => .physical
  | 1 => .virtual
  | 2 => .port
  | 3 => .guestPhysical
  | _ => .ioVirtual

instance : Encodable AddressSpace :=
  Encodable.ofLeftInverse addressSpaceCode addressSpaceOfNat (by intro a; cases a <;> rfl)

def dienstAbiCode : DienstAbi → Nat
  | .biosInterrupt => 0
  | .efiX64 => 1
  | .efiAapcs => 2
  | .psciSmc => 3
  | .sbiEcall => 4

def dienstAbiOfNat : Nat → DienstAbi
  | 0 => .biosInterrupt
  | 1 => .efiX64
  | 2 => .efiAapcs
  | 3 => .psciSmc
  | _ => .sbiEcall

instance : Encodable DienstAbi :=
  Encodable.ofLeftInverse dienstAbiCode dienstAbiOfNat (by intro a; cases a <;> rfl)

def firmwareZeileCode : FirmwareZeile → Nat
  | .biosServices => 0
  | .uefi210 => 1
  | .psci => 2
  | .sbi => 3

def firmwareZeileOfNat : Nat → FirmwareZeile
  | 0 => .biosServices
  | 1 => .uefi210
  | 2 => .psci
  | _ => .sbi

instance : Encodable FirmwareZeile :=
  Encodable.ofLeftInverse firmwareZeileCode firmwareZeileOfNat (by intro a; cases a <;> rfl)

/-! ## Identifier

A written name is a subtype of `List Char`. The inverse checks the spelling
constructively and rebuilds the proof component. -/

def identifierFinv (name : List Char) : Option Identifier :=
  match name with
  | [] => none
  | c :: rest =>
    if h1 : isNameStart c then
      if h2 : ∀ a ∈ rest, isNamePart a then
        some ⟨c :: rest, ⟨c, rest, rfl, h1, h2⟩⟩
      else none
    else none

instance : Encodable Identifier :=
  Encodable.ofLeftInjection (fun id : Identifier => id.val) identifierFinv (by
    intro id
    rcases id with ⟨name, h⟩
    rcases h with ⟨c, rest, rfl, hs, hp⟩
    simp only [identifierFinv]
    rw [dif_pos hs, dif_pos hp]
    rfl)

/-! ## CarrierEffect -/

def carrierEffectCode (e : CarrierEffect) : Nat :=
  Encodable.encode [e.declaration, Encodable.encode e.carrier, Encodable.encode e.access]

def carrierEffectDecode (n : Nat) : Option CarrierEffect := do
  let fs : List Nat ← Encodable.decode n
  match fs with
  | [d, c, a] => do
      let carrier : List Char ← Encodable.decode c
      let access : CarrierAccess ← Encodable.decode a
      some { declaration := d, carrier, access }
  | _ => none

instance : Encodable CarrierEffect :=
  Encodable.ofLeftInjection carrierEffectCode carrierEffectDecode (by
    rintro ⟨d, c, a⟩
    simp [carrierEffectCode, carrierEffectDecode, Encodable.encodek])

/-! ## Ty (indexed family, encoded by structural first-order trees)

`Ty .value` is recursive. Its code is a preorder list of natural numbers; the
decoder consumes that list and returns the leftover tail, so recursion is
structural on the list and the inverse lemma is generalized over the tail. -/

def tyCode : Ty .value → List Nat
  | .int lo hi => 0 :: Encodable.encode lo :: Encodable.encode hi :: []
  | .bool => [1]
  | .array el cnt => 2 :: tyCode el ++ [Encodable.encode cnt]
  | .productEnd => [3]
  | .product h t => 4 :: tyCode h ++ tyCode t
  | .record nm ls lay => 5 :: Encodable.encode nm :: Encodable.encode ls :: tyCode lay
  | .recordSchema nm ls lay => 6 :: Encodable.encode nm :: Encodable.encode ls :: tyCode lay
  | .sumEnd => [7]
  | .sum h t => 8 :: tyCode h ++ tyCode t
  | .variant nm ls hp lay =>
      9 :: Encodable.encode nm :: Encodable.encode ls :: Encodable.encode hp :: tyCode lay
  | .variantSchema nm ls hp lay =>
      10 :: Encodable.encode nm :: Encodable.encode ls :: Encodable.encode hp :: tyCode lay
  | .text cap => [11, Encodable.encode cap]
  | .carrierSchema cnt ls lay ex =>
      12 :: Encodable.encode cnt :: Encodable.encode ls :: tyCode lay ++ [Encodable.encode ex]
  | .effectGroupSchema eff => [13, Encodable.encode eff]
  | .address space => [14, Encodable.encode space]
  | .ownedRegion => [15]
  | .regionView el => 16 :: tyCode el
  | .ptr space recht referent =>
      17 :: Encodable.encode space :: Encodable.encode recht :: tyCode referent

def tyDecode : List Nat → Option (Ty .value × List Nat)
  | 0 :: lo :: hi :: rest => do
      let l : Int ← Encodable.decode lo
      let h : Int ← Encodable.decode hi
      some (.int l h, rest)
  | 1 :: rest => some (.bool, rest)
  | 2 :: rest => do
      let (el, r1) ← tyDecode rest
      match r1 with
      | cnt :: r2 =>
          let c : Nat ← Encodable.decode cnt
          some (.array el c, r2)
      | _ => none
  | 3 :: rest => some (.productEnd, rest)
  | 4 :: rest => do
      let (h, r1) ← tyDecode rest
      let (t, r2) ← tyDecode r1
      some (.product h t, r2)
  | 5 :: nm :: ls :: rest => do
      let n : List Char ← Encodable.decode nm
      let l : List (List Char) ← Encodable.decode ls
      let (lay, r) ← tyDecode rest
      some (.record n l lay, r)
  | 6 :: nm :: ls :: rest => do
      let n : List Char ← Encodable.decode nm
      let l : List (List Char) ← Encodable.decode ls
      let (lay, r) ← tyDecode rest
      some (.recordSchema n l lay, r)
  | 7 :: rest => some (.sumEnd, rest)
  | 8 :: rest => do
      let (h, r1) ← tyDecode rest
      let (t, r2) ← tyDecode r1
      some (.sum h t, r2)
  | 9 :: nm :: ls :: hp :: rest => do
      let n : List Char ← Encodable.decode nm
      let l : List (List Char) ← Encodable.decode ls
      let p : List Bool ← Encodable.decode hp
      let (lay, r) ← tyDecode rest
      some (.variant n l p lay, r)
  | 10 :: nm :: ls :: hp :: rest => do
      let n : List Char ← Encodable.decode nm
      let l : List (List Char) ← Encodable.decode ls
      let p : List Bool ← Encodable.decode hp
      let (lay, r) ← tyDecode rest
      some (.variantSchema n l p lay, r)
  | 11 :: cap :: rest => do
      let c : Nat ← Encodable.decode cap
      some (.text c, rest)
  | 12 :: cnt :: ls :: rest => do
      let c : Nat ← Encodable.decode cnt
      let l : List (List Char) ← Encodable.decode ls
      let (lay, r1) ← tyDecode rest
      match r1 with
      | ex :: r2 =>
          let e : Bool ← Encodable.decode ex
          some (.carrierSchema c l lay e, r2)
      | _ => none
  | 13 :: eff :: rest => do
      let e : List CarrierEffect ← Encodable.decode eff
      some (.effectGroupSchema e, rest)
  | 14 :: space :: rest => do
      let s : AddressSpace ← Encodable.decode space
      some (.address s, rest)
  | 15 :: rest => some (.ownedRegion, rest)
  | 16 :: rest => do
      let (el, r) ← tyDecode rest
      some (.regionView el, r)
  | 17 :: space :: recht :: rest => do
      let s : AddressSpace ← Encodable.decode space
      let r : PtrRecht ← Encodable.decode recht
      let (referent, r') ← tyDecode rest
      some (.ptr s r referent, r')
  | _ => none

lemma tyDecode_code : ∀ (t : Ty .value) (rest : List Nat),
    tyDecode (tyCode t ++ rest) = some (t, rest) := by
  intro t
  induction t <;> (intro rest; simp [tyCode, tyDecode, *, List.append_assoc])

instance : Encodable (Ty .value) :=
  Encodable.ofLeftInjection
    (fun t => Encodable.encode (tyCode t))
    (fun n => do
      let toks : List Nat ← Encodable.decode n
      let (t, rest) ← tyDecode toks
      if rest.isEmpty then some t else none)
    (by
      intro t
      rw [Encodable.encodek, tyDecode_code]
      simp)

/-! ## Rufstelle -/

def rufstelleCode (r : Rufstelle) : Nat :=
  Encodable.encode [Encodable.encode r.name, Encodable.encode r.args,
    Encodable.encode r.bind, Encodable.encode r.effects]

def rufstelleDecode (n : Nat) : Option Rufstelle := do
  let fs : List Nat ← Encodable.decode n
  match fs with
  | [a, b, c, d] => do
      let name : Identifier ← Encodable.decode a
      let args : List (Ty .value) ← Encodable.decode b
      let bind : Option (Ty .value) ← Encodable.decode c
      let effects : Option (List CarrierEffect) ← Encodable.decode d
      some { name, args, bind, effects }
  | _ => none

instance : Encodable Rufstelle :=
  Encodable.ofLeftInjection rufstelleCode rufstelleDecode (by
    rintro ⟨name, args, bind, effects⟩
    simp [rufstelleCode, rufstelleDecode, Encodable.encodek])

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
