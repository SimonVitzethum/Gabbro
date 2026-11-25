module

public import Core.Beobachtung.Unentscheidbar.Simulation.KodierInstanzen

noncomputable section

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ast.LowLevel
open Gabbro.Core.Katalog
open Gabbro.Core.Aussenfrage
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
      simp_all [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, Option.bind_some]
  | .integer signed width interval => by
      unfold writtenTypeVonCode writtenTypeZuCode
      simp_all [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, Option.bind_some]
  | .array element count => by
      have ih := writtenTypeCode_ofCode element
      unfold writtenTypeVonCode writtenTypeZuCode
      simp_all [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, ih]
  | .tuple first second rest => by
      have ih1 := writtenTypeCode_ofCode first
      have ih2 := writtenTypeCode_ofCode second
      have ih3 := writtenTypesCode_ofCode rest
      unfold writtenTypeVonCode writtenTypeZuCode
      simp_all [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, ih1, ih2, ih3,
        writtenTypesVonCode, writtenTypesZuCode]
  | .text capacity => by
      unfold writtenTypeVonCode writtenTypeZuCode
      simp_all [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, Option.bind_some]
  | .index carrier count => by
      unfold writtenTypeVonCode writtenTypeZuCode
      simp_all [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, Option.bind_some]
  | .indexOption carrier count => by
      unfold writtenTypeVonCode writtenTypeZuCode
      simp_all [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, Option.bind_some]
  | .address space => by
      unfold writtenTypeVonCode writtenTypeZuCode
      simp_all [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, Option.bind_some]
  | .ownedRegion => by
      unfold writtenTypeVonCode writtenTypeZuCode
      simp_all [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, Option.bind_some]
  | .ptr space recht referent => by
      have ih := writtenTypeCode_ofCode referent
      unfold writtenTypeVonCode writtenTypeZuCode
      simp_all [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, ih]

  theorem writtenTypesCode_ofCode : ∀ w : WrittenTypes,
    writtenTypesVonCode (writtenTypesZuCode w) = some w
  | .empty => by
      unfold writtenTypesVonCode writtenTypesZuCode
      simp_all [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, Option.bind_some]
  | .next head tail => by
      have ih1 := writtenTypeCode_ofCode head
      have ih2 := writtenTypesCode_ofCode tail
      unfold writtenTypesVonCode writtenTypesZuCode
      simp_all [natZuCode, codeZuNat, codeZuNat_natZuCode, Encodable.encodek, ih1, ih2,
        writtenTypeVonCode, writtenTypeZuCode]
end

instance : Encodable WrittenType :=
  Encodable.ofLeftInjection
    (fun w => Encodable.encode (writtenTypeZuCode w))
    (fun n => (Encodable.decode n).bind writtenTypeVonCode)
    (by intro w; simp_all [Encodable.encodek, writtenTypeCode_ofCode, Option.bind_some])

instance : Encodable WrittenTypes :=
  Encodable.ofLeftInjection
    (fun w => Encodable.encode (writtenTypesZuCode w))
    (fun n => (Encodable.decode n).bind writtenTypesVonCode)
    (by intro w; simp_all [Encodable.encodek, writtenTypesCode_ofCode, Option.bind_some])

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
        simp_all [regionInitializerCode, regionInitializerDecode, Encodable.encodek, viewRegion, valid])

/-! ## Zugriffsform (MK-04) -/

/-- The access modes as numbers. -/
def modusNr : Gabbro.Core.Speicher.Modus → Nat
  | .na => 0
  | .rlx => 1
  | .ra => 2
  | .sc => 3

def modusVonNr : Nat → Option Gabbro.Core.Speicher.Modus
  | 0 => Option.some .na
  | 1 => Option.some .rlx
  | 2 => Option.some .ra
  | 3 => Option.some .sc
  | _ => Option.none

instance : Encodable Gabbro.Core.Speicher.Modus :=
  Encodable.ofLeftInjection modusNr modusVonNr (by intro m; cases m <;> rfl)

/-- An access instruction as a sum of the products of its fields. -/
abbrev ZugriffssummeTyp : Type :=
  (Nat × Nat × Nat × Ty .value × Gabbro.Core.Speicher.Modus) ⊕
    (Nat × Nat × Nat × Gabbro.Core.Speicher.Modus) ⊕
    (Nat × Nat × Nat × Nat × Ty .value × Gabbro.Core.Speicher.Modus) ⊕
    (Nat × Nat × Nat × Nat × Nat × Ty .value × Gabbro.Core.Speicher.Modus) ⊕
    (Nat × Nat × Nat × Nat × Ty .value × Gabbro.Core.Speicher.Modus) ⊕
    (Nat × Nat × Nat × Int × Ty .value × Gabbro.Core.Speicher.Modus) ⊕
    (Nat × Nat × Nat × Gabbro.Core.Speicher.Modus) ⊕
    Gabbro.Core.Speicher.Modus

def zugriffZuSumme : Zugriffsform → ZugriffssummeTyp
  | .lade a b c t m => .inl (a, b, c, t, m)
  | .speichere a b c m => .inr (.inl (a, b, c, m))
  | .tausche a b c d t m => .inr (.inr (.inl (a, b, c, d, t, m)))
  | .vergleicheTausche a b c d e t m => .inr (.inr (.inr (.inl (a, b, c, d, e, t, m))))
  | .holeUndAddiere a b c d t m => .inr (.inr (.inr (.inr (.inl (a, b, c, d, t, m)))))
  | .erwarte a b c i t m => .inr (.inr (.inr (.inr (.inr (.inl (a, b, c, i, t, m))))))
  | .veroeffentliche a b c m => .inr (.inr (.inr (.inr (.inr (.inr (.inl (a, b, c, m)))))))
  | .zaun m => .inr (.inr (.inr (.inr (.inr (.inr (.inr m))))))

def zugriffVonSumme : ZugriffssummeTyp → Option Zugriffsform
  | .inl (a, b, c, t, m) => Option.some (.lade a b c t m)
  | .inr (.inl (a, b, c, m)) => Option.some (.speichere a b c m)
  | .inr (.inr (.inl (a, b, c, d, t, m))) => Option.some (.tausche a b c d t m)
  | .inr (.inr (.inr (.inl (a, b, c, d, e, t, m)))) => Option.some (.vergleicheTausche a b c d e t m)
  | .inr (.inr (.inr (.inr (.inl (a, b, c, d, t, m))))) => Option.some (.holeUndAddiere a b c d t m)
  | .inr (.inr (.inr (.inr (.inr (.inl (a, b, c, i, t, m)))))) => Option.some (.erwarte a b c i t m)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (a, b, c, m))))))) => Option.some (.veroeffentliche a b c m)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr m)))))) => Option.some (.zaun m)

instance : Encodable Zugriffsform :=
  Encodable.ofLeftInjection zugriffZuSumme zugriffVonSumme (by intro z; cases z <;> rfl)

/-! ## Fadenform (MK-07) -/

/-- A lifecycle instruction as a sum of the products of its fields. -/
abbrev FadensummeTyp : Type :=
  (Nat × Nat × Ty .value × List Nat) ⊕ Nat ⊕ (Nat × Nat × Ty .value) ⊕ (Nat × Nat) ⊕ (Nat × Nat)

def fadenZuSumme : Fadenform → FadensummeTyp
  | .starte a b t l => .inl (a, b, t, l)
  | .beende a => .inr (.inl a)
  | .verbinde a b t => .inr (.inr (.inl (a, b, t)))
  | .wechsle a b => .inr (.inr (.inr (.inl (a, b))))
  | .kernStart a b => .inr (.inr (.inr (.inr (a, b))))

def fadenVonSumme : FadensummeTyp → Option Fadenform
  | .inl (a, b, t, l) => Option.some (.starte a b t l)
  | .inr (.inl a) => Option.some (.beende a)
  | .inr (.inr (.inl (a, b, t))) => Option.some (.verbinde a b t)
  | .inr (.inr (.inr (.inl (a, b)))) => Option.some (.wechsle a b)
  | .inr (.inr (.inr (.inr (a, b)))) => Option.some (.kernStart a b)

instance : Encodable Fadenform :=
  Encodable.ofLeftInjection fadenZuSumme fadenVonSumme (by intro z; cases z <;> rfl)

/-! ## Outside-question forms (MK-06) -/

def dienstCode : Dienst → Nat
  | .readSectors => 0
  | .memoryMap => 1
  | .enableA20 => 2
  | .exitBootServices => 3
  | .cpuOn => 4
  | .hartStart => 5

def dienstOfNat : Nat → Dienst
  | 0 => .readSectors
  | 1 => .memoryMap
  | 2 => .enableA20
  | 3 => .exitBootServices
  | 4 => .cpuOn
  | _ => .hartStart

instance : Encodable Dienst :=
  Encodable.ofLeftInverse dienstCode dienstOfNat (by intro d; cases d <;> rfl)

abbrev AussenOperationSummeTyp : Type :=
  Nat ⊕ (List UInt8) ⊕ (List UInt8) ⊕ (Dienst × List UInt8) ⊕ (List UInt8) ⊕
    Nat ⊕ (Nat × Nat) ⊕ (Nat × Nat)

def aussenOperationZuSumme : AussenOperation → AussenOperationSummeTyp
  | .read => .inl 0
  | .write bytes => .inr (.inl bytes)
  | .resolve name => .inr (.inr (.inl name))
  | .firmware service bytes => .inr (.inr (.inr (.inl (service, bytes))))
  | .exchange message => .inr (.inr (.inr (.inr (.inl message))))
  | .registerRead offset => .inr (.inr (.inr (.inr (.inr (.inl offset)))))
  | .registerWrite offset value => .inr (.inr (.inr (.inr (.inr (.inr (.inl (offset, value)))))))
  | .waitRegister offset expected => .inr (.inr (.inr (.inr (.inr (.inr (.inr ((offset, expected))))))))

def aussenOperationVonSumme : AussenOperationSummeTyp → Option AussenOperation
  | .inl _ => Option.some .read
  | .inr (.inl bytes) => Option.some (.write bytes)
  | .inr (.inr (.inl name)) => Option.some (.resolve name)
  | .inr (.inr (.inr (.inl (service, bytes)))) => Option.some (.firmware service bytes)
  | .inr (.inr (.inr (.inr (.inl message)))) => Option.some (.exchange message)
  | .inr (.inr (.inr (.inr (.inr (.inl offset))))) => Option.some (.registerRead offset)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (offset, value))))))) =>
    Option.some (.registerWrite offset value)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr ((offset, expected)))))))) =>
    Option.some (.waitRegister offset expected)

instance : Encodable AussenOperation :=
  Encodable.ofLeftInjection aussenOperationZuSumme aussenOperationVonSumme
    (by intro op; cases op <;> rfl)

abbrev AussenfrageSummeTyp : Type := (Nat × AussenOperation × List Nat) ⊕ Nat

def aussenfrageZuSumme : Aussenfrageform → AussenfrageSummeTyp
  | .frage ziel operation args => .inl (ziel, operation, args)
  | .verbrauche ziel => .inr ziel

def aussenfrageVonSumme : AussenfrageSummeTyp → Option Aussenfrageform
  | .inl (ziel, operation, args) => Option.some (.frage ziel operation args)
  | .inr ziel => Option.some (.verbrauche ziel)

instance : Encodable Aussenfrageform :=
  Encodable.ofLeftInjection aussenfrageZuSumme aussenfrageVonSumme
    (by intro form; cases form <;> rfl)

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
