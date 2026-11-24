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
type. Every inverse is proved explicitly. -/

instance : Encodable Char :=
  Encodable.ofLeftInjection Char.toNat (fun n => some (Char.ofNat n)) (by
    intro c
    simp_all)

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

local instance nameStartDecidable (c : Char) : Decidable (isNameStart c) := by
  unfold isNameStart isLetter
  infer_instance

local instance namePartDecidable (c : Char) : Decidable (isNamePart c) := by
  unfold isNamePart isNameStart isLetter
  infer_instance

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
    simp_all
    rw [dif_pos hs, dif_pos hp])

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
    simp_all)

/-! ## First-order tree codes

`Nat.Partrec.Code` is an already-decodable recursive tree. An AST value is
injected into it by a structural map; the inverse is structural recursion on
the tree, so no well-founded proof obligations and no meta commands are needed. -/

open Nat.Partrec

def natZuCode : Nat → Code
  | 0 => Code.zero
  | n + 1 => Code.pair Code.right (natZuCode n)

def codeZuNat : Code → Option Nat
  | Code.zero => some 0
  | Code.pair Code.right c => do
      let n ← codeZuNat c
      some (n + 1)
  | _ => none

theorem codeZuNat_natZuCode (n : Nat) : codeZuNat (natZuCode n) = some n := by
  induction n with
  | zero => simp_all
  | succ n ih => simp_all

lemma intRueck (z : Int) : Equiv.intEquivNat.symm (Encodable.encode z) = z := by
  simpa [Encodable.encode, Encodable.decode] using (Encodable.encodek z)

/-! ## Ty (indexed family) -/

def tyZuCode : Ty .value → Code
  | .int lo hi =>
      Code.pair (natZuCode 0) (Code.pair (natZuCode (Encodable.encode lo))
        (Code.pair (natZuCode (Encodable.encode hi)) Code.zero))
  | .bool => Code.pair (natZuCode 1) Code.zero
  | .array el cnt =>
      Code.pair (natZuCode 2) (Code.pair (tyZuCode el)
        (Code.pair (natZuCode (Encodable.encode cnt)) Code.zero))
  | .productEnd => Code.pair (natZuCode 3) Code.zero
  | .product h t =>
      Code.pair (natZuCode 4) (Code.pair (tyZuCode h) (Code.pair (tyZuCode t) Code.zero))
  | .record nm ls lay =>
      Code.pair (natZuCode 5) (Code.pair (natZuCode (Encodable.encode nm))
        (Code.pair (natZuCode (Encodable.encode ls)) (Code.pair (tyZuCode lay) Code.zero)))
  | .recordSchema nm ls lay =>
      Code.pair (natZuCode 6) (Code.pair (natZuCode (Encodable.encode nm))
        (Code.pair (natZuCode (Encodable.encode ls)) (Code.pair (tyZuCode lay) Code.zero)))
  | .sumEnd => Code.pair (natZuCode 7) Code.zero
  | .sum h t =>
      Code.pair (natZuCode 8) (Code.pair (tyZuCode h) (Code.pair (tyZuCode t) Code.zero))
  | .variant nm ls hp lay =>
      Code.pair (natZuCode 9) (Code.pair (natZuCode (Encodable.encode nm))
        (Code.pair (natZuCode (Encodable.encode ls))
          (Code.pair (natZuCode (Encodable.encode hp)) (Code.pair (tyZuCode lay) Code.zero))))
  | .variantSchema nm ls hp lay =>
      Code.pair (natZuCode 10) (Code.pair (natZuCode (Encodable.encode nm))
        (Code.pair (natZuCode (Encodable.encode ls))
          (Code.pair (natZuCode (Encodable.encode hp)) (Code.pair (tyZuCode lay) Code.zero))))
  | .text cap => Code.pair (natZuCode 11) (natZuCode (Encodable.encode cap))
  | .carrierSchema cnt ls lay ex =>
      Code.pair (natZuCode 12) (Code.pair (natZuCode (Encodable.encode cnt))
        (Code.pair (natZuCode (Encodable.encode ls))
          (Code.pair (tyZuCode lay) (Code.pair (natZuCode (Encodable.encode ex)) Code.zero))))
  | .effectGroupSchema eff =>
      Code.pair (natZuCode 13) (natZuCode (Encodable.encode eff))
  | .address space => Code.pair (natZuCode 14) (natZuCode (Encodable.encode space))
  | .ownedRegion => Code.pair (natZuCode 15) Code.zero
  | .regionView el => Code.pair (natZuCode 16) (tyZuCode el)
  | .ptr space recht referent =>
      Code.pair (natZuCode 17) (Code.pair (natZuCode (Encodable.encode space))
        (Code.pair (natZuCode (Encodable.encode recht)) (tyZuCode referent)))

def tyVonCode : Code → Option (Ty .value)
  | Code.pair tag kids =>
    match codeZuNat tag with
    | some 0 =>
      match kids with
      | Code.pair lo (Code.pair hi Code.zero) => do
          let lon : Nat ← codeZuNat lo
          let hin : Nat ← codeZuNat hi
          let lo' : Int ← Encodable.decode lon
          let hi' : Int ← Encodable.decode hin
          some (.int lo' hi')
      | _ => none
    | some 1 =>
      match kids with
      | Code.zero => some .bool
      | _ => none
    | some 2 =>
      match kids with
      | Code.pair el (Code.pair cnt Code.zero) => do
          let el' ← tyVonCode el
          let cnt' : Nat ← codeZuNat cnt
          some (.array el' cnt')
      | _ => none
    | some 3 =>
      match kids with
      | Code.zero => some .productEnd
      | _ => none
    | some 4 =>
      match kids with
      | Code.pair h (Code.pair t Code.zero) => do
          let h' ← tyVonCode h
          let t' ← tyVonCode t
          some (.product h' t')
      | _ => none
    | some 5 =>
      match kids with
      | Code.pair nm (Code.pair ls (Code.pair lay Code.zero)) => do
          let nmn : Nat ← codeZuNat nm
          let lsn : Nat ← codeZuNat ls
          let nm' : List Char ← Encodable.decode nmn
          let ls' : List (List Char) ← Encodable.decode lsn
          let lay' ← tyVonCode lay
          some (.record nm' ls' lay')
      | _ => none
    | some 6 =>
      match kids with
      | Code.pair nm (Code.pair ls (Code.pair lay Code.zero)) => do
          let nmn : Nat ← codeZuNat nm
          let lsn : Nat ← codeZuNat ls
          let nm' : List Char ← Encodable.decode nmn
          let ls' : List (List Char) ← Encodable.decode lsn
          let lay' ← tyVonCode lay
          some (.recordSchema nm' ls' lay')
      | _ => none
    | some 7 =>
      match kids with
      | Code.zero => some .sumEnd
      | _ => none
    | some 8 =>
      match kids with
      | Code.pair h (Code.pair t Code.zero) => do
          let h' ← tyVonCode h
          let t' ← tyVonCode t
          some (.sum h' t')
      | _ => none
    | some 9 =>
      match kids with
      | Code.pair nm (Code.pair ls (Code.pair hp (Code.pair lay Code.zero))) => do
          let nmn : Nat ← codeZuNat nm
          let lsn : Nat ← codeZuNat ls
          let hpn : Nat ← codeZuNat hp
          let nm' : List Char ← Encodable.decode nmn
          let ls' : List (List Char) ← Encodable.decode lsn
          let hp' : List Bool ← Encodable.decode hpn
          let lay' ← tyVonCode lay
          some (.variant nm' ls' hp' lay')
      | _ => none
    | some 10 =>
      match kids with
      | Code.pair nm (Code.pair ls (Code.pair hp (Code.pair lay Code.zero))) => do
          let nmn : Nat ← codeZuNat nm
          let lsn : Nat ← codeZuNat ls
          let hpn : Nat ← codeZuNat hp
          let nm' : List Char ← Encodable.decode nmn
          let ls' : List (List Char) ← Encodable.decode lsn
          let hp' : List Bool ← Encodable.decode hpn
          let lay' ← tyVonCode lay
          some (.variantSchema nm' ls' hp' lay')
      | _ => none
    | some 11 => do
        let capn : Nat ← codeZuNat kids
        let cap : Nat ← Encodable.decode capn
        some (.text cap)
    | some 12 =>
      match kids with
      | Code.pair cnt (Code.pair ls (Code.pair lay (Code.pair ex Code.zero))) => do
          let cntn : Nat ← codeZuNat cnt
          let lsn : Nat ← codeZuNat ls
          let exn : Nat ← codeZuNat ex
          let cnt' : Nat ← Encodable.decode cntn
          let ls' : List (List Char) ← Encodable.decode lsn
          let ex' : Bool ← Encodable.decode exn
          let lay' ← tyVonCode lay
          some (.carrierSchema cnt' ls' lay' ex')
      | _ => none
    | some 13 => do
        let effn : Nat ← codeZuNat kids
        let eff : List CarrierEffect ← Encodable.decode effn
        some (.effectGroupSchema eff)
    | some 14 => do
        let sn : Nat ← codeZuNat kids
        let space : AddressSpace ← Encodable.decode sn
        some (.address space)
    | some 15 =>
      match kids with
      | Code.zero => some .ownedRegion
      | _ => none
    | some 16 => do
        let el' ← tyVonCode kids
        some (.regionView el')
    | some 17 =>
      match kids with
      | Code.pair space (Code.pair recht referent) => do
          let sn : Nat ← codeZuNat space
          let rn : Nat ← codeZuNat recht
          let space' : AddressSpace ← Encodable.decode sn
          let recht' : PtrRecht ← Encodable.decode rn
          let referent' ← tyVonCode referent
          some (.ptr space' recht' referent')
      | _ => none
    | _ => none
  | _ => none

theorem tyCode_ofCode : ∀ t : Ty .value, tyVonCode (tyZuCode t) = some t
  | .int lo hi => by
      unfold tyVonCode tyZuCode
      simp_all
  | .bool => by
      unfold tyVonCode tyZuCode
      simp_all
  | .array el cnt => by
      have ih := tyCode_ofCode el
      unfold tyVonCode tyZuCode
      simp_all
  | .productEnd => by
      unfold tyVonCode tyZuCode
      simp_all
  | .product h t => by
      have ih1 := tyCode_ofCode h
      have ih2 := tyCode_ofCode t
      unfold tyVonCode tyZuCode
      simp_all
  | .record nm ls lay => by
      have ih := tyCode_ofCode lay
      unfold tyVonCode tyZuCode
      simp_all
  | .recordSchema nm ls lay => by
      have ih := tyCode_ofCode lay
      unfold tyVonCode tyZuCode
      simp_all
  | .sumEnd => by
      unfold tyVonCode tyZuCode
      simp_all
  | .sum h t => by
      have ih1 := tyCode_ofCode h
      have ih2 := tyCode_ofCode t
      unfold tyVonCode tyZuCode
      simp_all
  | .variant nm ls hp lay => by
      have ih := tyCode_ofCode lay
      unfold tyVonCode tyZuCode
      simp_all
  | .variantSchema nm ls hp lay => by
      have ih := tyCode_ofCode lay
      unfold tyVonCode tyZuCode
      simp_all
  | .text cap => by
      unfold tyVonCode tyZuCode
      simp_all
  | .carrierSchema cnt ls lay ex => by
      have ih := tyCode_ofCode lay
      unfold tyVonCode tyZuCode
      simp_all
  | .effectGroupSchema eff => by
      unfold tyVonCode tyZuCode
      simp_all
  | .address space => by
      unfold tyVonCode tyZuCode
      simp_all
  | .ownedRegion => by
      unfold tyVonCode tyZuCode
      simp_all
  | .regionView el => by
      have ih := tyCode_ofCode el
      unfold tyVonCode tyZuCode
      simp_all
  | .ptr space recht referent => by
      have ih := tyCode_ofCode referent
      unfold tyVonCode tyZuCode
      simp_all

instance instEncodableTy (k : Kind) : Encodable (Ty k) := by
  cases k
  exact Encodable.ofLeftInjection (β := Ty .value)
    (fun t => Encodable.encode (tyZuCode t))
    (fun n => (Encodable.decode n).bind tyVonCode)
    (by intro t; simp_all)

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
    simp_all)

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
