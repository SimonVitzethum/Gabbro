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

noncomputable def identifierFinv (name : List Char) : Option Identifier := by
  classical
  match name with
  | [] => exact none
  | c :: rest =>
      if h1 : isNameStart c then
        if h2 : ∀ a ∈ rest, isNamePart a then
          exact some ⟨c :: rest, ⟨c, rest, rfl, h1, h2⟩⟩
        else exact none
      else exact none

instance : Encodable Identifier :=
  Encodable.ofLeftInjection (fun id : Identifier => id.val) identifierFinv (by
    intro id
    classical
    rcases id with ⟨name, h⟩
    rcases h with ⟨c, rest, rfl, hs, hp⟩
    simp [identifierFinv, hs, hp])

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

def tyCode : Ty .value → Nat
  | .int lo hi => Nat.pair 0 (Nat.pair (Encodable.encode lo) (Encodable.encode hi)) + 1
  | .bool => Nat.pair 1 0 + 1
  | .array el cnt => Nat.pair 2 (Nat.pair (tyCode el) (Encodable.encode cnt)) + 1
  | .productEnd => Nat.pair 3 0 + 1
  | .product h t => Nat.pair 4 (Nat.pair (tyCode h) (tyCode t)) + 1
  | .record nm ls lay =>
      Nat.pair 5 (Nat.pair (Encodable.encode nm) (Nat.pair (Encodable.encode ls) (tyCode lay))) + 1
  | .recordSchema nm ls lay =>
      Nat.pair 6 (Nat.pair (Encodable.encode nm) (Nat.pair (Encodable.encode ls) (tyCode lay))) + 1
  | .sumEnd => Nat.pair 7 0 + 1
  | .sum h t => Nat.pair 8 (Nat.pair (tyCode h) (tyCode t)) + 1
  | .variant nm ls hp lay =>
      Nat.pair 9 (Nat.pair (Encodable.encode nm)
        (Nat.pair (Encodable.encode ls) (Nat.pair (Encodable.encode hp) (tyCode lay)))) + 1
  | .variantSchema nm ls hp lay =>
      Nat.pair 10 (Nat.pair (Encodable.encode nm)
        (Nat.pair (Encodable.encode ls) (Nat.pair (Encodable.encode hp) (tyCode lay)))) + 1
  | .text cap => Nat.pair 11 (Encodable.encode cap) + 1
  | .carrierSchema cnt ls lay ex =>
      Nat.pair 12 (Nat.pair (Encodable.encode cnt)
        (Nat.pair (Encodable.encode ls) (Nat.pair (tyCode lay) (Encodable.encode ex)))) + 1
  | .effectGroupSchema eff => Nat.pair 13 (Encodable.encode eff) + 1
  | .address space => Nat.pair 14 (Encodable.encode space) + 1
  | .ownedRegion => Nat.pair 15 0 + 1
  | .regionView el => Nat.pair 16 (tyCode el) + 1
  | .ptr space recht referent =>
      Nat.pair 17 (Nat.pair (Encodable.encode space)
        (Nat.pair (Encodable.encode recht) (tyCode referent))) + 1

def tyOfCode : Nat → Ty .value
  | 0 => .bool
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
    have hb21 : payload.unpair.2.unpair.2.unpair.1 < n + 1 :=
      lt_of_le_of_lt (Nat.unpair_left_le payload.unpair.2.unpair.2) hb2
    have hb22 : payload.unpair.2.unpair.2.unpair.2 < n + 1 :=
      lt_of_le_of_lt (Nat.unpair_right_le payload.unpair.2.unpair.2) hb2
    match p.1 with
    | 0 => .int (Encodable.decode payload.unpair.1).getD 0 (Encodable.decode payload.unpair.2).getD 0
    | 1 => .bool
    | 2 => .array (tyOfCode payload.unpair.1) (Encodable.decode payload.unpair.2).getD 0
    | 3 => .productEnd
    | 4 => .product (tyOfCode payload.unpair.1) (tyOfCode payload.unpair.2)
    | 5 => .record (Encodable.decode payload.unpair.1).getD []
        (Encodable.decode payload.unpair.2.unpair.1).getD [] (tyOfCode payload.unpair.2.unpair.2)
    | 6 => .recordSchema (Encodable.decode payload.unpair.1).getD []
        (Encodable.decode payload.unpair.2.unpair.1).getD [] (tyOfCode payload.unpair.2.unpair.2)
    | 7 => .sumEnd
    | 8 => .sum (tyOfCode payload.unpair.1) (tyOfCode payload.unpair.2)
    | 9 => .variant (Encodable.decode payload.unpair.1).getD []
        (Encodable.decode payload.unpair.2.unpair.1).getD []
        (Encodable.decode payload.unpair.2.unpair.2.unpair.1).getD []
        (tyOfCode payload.unpair.2.unpair.2.unpair.2)
    | 10 => .variantSchema (Encodable.decode payload.unpair.1).getD []
        (Encodable.decode payload.unpair.2.unpair.1).getD []
        (Encodable.decode payload.unpair.2.unpair.2.unpair.1).getD []
        (tyOfCode payload.unpair.2.unpair.2.unpair.2)
    | 11 => .text (Encodable.decode payload).getD 0
    | 12 => .carrierSchema (Encodable.decode payload.unpair.1).getD 0
        (Encodable.decode payload.unpair.2.unpair.1).getD []
        (tyOfCode payload.unpair.2.unpair.2.unpair.1)
        (Encodable.decode payload.unpair.2.unpair.2.unpair.2).getD false
    | 13 => .effectGroupSchema (Encodable.decode payload).getD []
    | 14 => .address (Encodable.decode payload).getD .physical
    | 15 => .ownedRegion
    | 16 => .regionView (tyOfCode payload)
    | 17 => .ptr (Encodable.decode payload.unpair.1).getD .physical
        (Encodable.decode payload.unpair.2.unpair.1).getD .r
        (tyOfCode payload.unpair.2.unpair.2)
    | _ => .bool

lemma tyCode_ofCode (t : Ty .value) : tyOfCode (tyCode t) = t := by
  induction t <;> simp [tyCode, tyOfCode, *]

instance : Encodable (Ty .value) :=
  Encodable.ofLeftInverse tyCode tyOfCode tyCode_ofCode

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
