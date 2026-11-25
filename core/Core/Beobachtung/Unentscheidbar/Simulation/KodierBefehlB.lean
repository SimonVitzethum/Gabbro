module

public import Core.Beobachtung.Unentscheidbar.Simulation.KodierBefehl

noncomputable section

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ast.LowLevel
open Gabbro.Core.Katalog
open Gabbro.Core.Text
open Nat.Partrec


def befehlVonCodeB : Code → Option Befehl
  | Code.pair tag kids =>
    match codeZuNat tag with
    | some 25 =>
      match kids with
      | Code.pair f0 (Code.zero) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          Option.some (.zurueckSprung f0')
      | _ => Option.none
    | some 26 =>
      match kids with
      | Code.pair f0 (Code.zero) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : Identifier ← Encodable.decode f0n
          Option.some (.starte f0')
      | _ => Option.none
    | some 27 =>
      match kids with
      | Code.zero => Option.some .ende
      | _ => Option.none
    | some 28 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.zero))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : Ty .value ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : ℕ ← Encodable.decode f2n
          Option.some (.baueArray f0' f1' f2')
      | _ => Option.none
    | some 29 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.zero))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : Ty .value ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : ℕ ← Encodable.decode f2n
          Option.some (.liesArray f0' f1' f2')
      | _ => Option.none
    | some 30 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : List (Ty .value) ← Encodable.decode f1n
          Option.some (.baueTupel f0' f1')
      | _ => Option.none
    | some 31 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.zero))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : List (Ty .value) ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : Fin f1'.length ← Encodable.decode f2n
          Option.some (.liesTupelfeld f0' f1' f2')
      | _ => Option.none
    | some 32 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.zero))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : List (Ty .value) ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : List Bool ← Encodable.decode f2n
          Option.some (.bindeTupel f0' f1' f2')
      | _ => Option.none
    | some 33 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.zero))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : List Char ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : List Identifier ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : List (Ty .value) ← Encodable.decode f2n
          Option.some (.definiereRecord f0' f1' f2')
      | _ => Option.none
    | some 34 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.pair f3 (Code.pair f4 (Code.zero))))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : List Char ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : List Identifier ← Encodable.decode f2n
          let f3n : ℕ ← codeZuNat f3
          let f3' : List (Ty .value) ← Encodable.decode f3n
          let f4n : ℕ ← codeZuNat f4
          let f4' : List ℕ ← Encodable.decode f4n
          Option.some (.baueRecord f0' f1' f2' f3' f4')
      | _ => Option.none
    | some 35 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.pair f3 (Code.pair f4 (Code.zero))))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : List Char ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : List Identifier ← Encodable.decode f2n
          let f3n : ℕ ← codeZuNat f3
          let f3' : List (Ty .value) ← Encodable.decode f3n
          let f4n : ℕ ← codeZuNat f4
          let f4' : Fin f3'.length ← Encodable.decode f4n
          Option.some (.liesRecordFeld f0' f1' f2' f3' f4')
      | _ => Option.none
    | some 36 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.pair f3 (Code.pair f4 (Code.pair f5 (Code.zero)))))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : List Char ← Encodable.decode f2n
          let f3n : ℕ ← codeZuNat f3
          let f3' : List Identifier ← Encodable.decode f3n
          let f4n : ℕ ← codeZuNat f4
          let f4' : List (Ty .value) ← Encodable.decode f4n
          let f5n : ℕ ← codeZuNat f5
          let f5' : Fin f4'.length ← Encodable.decode f5n
          Option.some (.setzeRecordFeld f0' f1' f2' f3' f4' f5')
      | _ => Option.none
    | some 37 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.zero))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : List Char ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : List Identifier ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : List (Option (Ty .value)) ← Encodable.decode f2n
          Option.some (.definiereVariante f0' f1' f2')
      | _ => Option.none
    | some 38 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.pair f3 (Code.pair f4 (Code.zero))))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : List Char ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : List Identifier ← Encodable.decode f2n
          let f3n : ℕ ← codeZuNat f3
          let f3' : List (Option (Ty .value)) ← Encodable.decode f3n
          let f4n : ℕ ← codeZuNat f4
          let f4' : Fin f3'.length ← Encodable.decode f4n
          Option.some (.baueVariante f0' f1' f2' f3' f4')
      | _ => Option.none
    | some 39 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.pair f3 (Code.pair f4 (Code.zero))))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : List Char ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : List Identifier ← Encodable.decode f2n
          let f3n : ℕ ← codeZuNat f3
          let f3' : List (Option (Ty .value)) ← Encodable.decode f3n
          let f4n : ℕ ← codeZuNat f4
          let f4' : List (ℕ × Bool) ← Encodable.decode f4n
          Option.some (.waehleVariante f0' f1' f2' f3' f4')
      | _ => Option.none
    | some 40 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : List Char ← Encodable.decode f1n
          Option.some (.textLiteral f0' f1')
      | _ => Option.none
    | some 41 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.zero))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : ℕ ← Encodable.decode f2n
          Option.some (.textConcat f0' f1' f2')
      | _ => Option.none
    | some 42 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          Option.some (.textIndex f0' f1')
      | _ => Option.none
    | some 43 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          Option.some (.substring f0' f1')
      | _ => Option.none
    | some 44 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          Option.some (.textLength f0' f1')
      | _ => Option.none
    | some 45 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.pair f3 (Code.zero)))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : List (List Char) ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : Ty .value ← Encodable.decode f2n
          let f3n : ℕ ← codeZuNat f3
          let f3' : Bool ← Encodable.decode f3n
          Option.some (.definiereTraeger f0' f1' f2' f3')
      | _ => Option.none
    | some 46 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          Option.some (.optionIstBesetzt f0' f1')
      | _ => Option.none
    | some 47 =>
      match kids with
      | Code.pair f0 (Code.zero) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : List CarrierEffect ← Encodable.decode f0n
          Option.some (.definiereEffektgruppe f0')
      | _ => Option.none
    | some 48 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.zero))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : Identifier ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : DienstAbi ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : FirmwareZeile ← Encodable.decode f2n
          Option.some (.waehleUmgebung f0' f1' f2')
      | _ => Option.none
    | some 49 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : RegionInitializer ← Encodable.decode f1n
          Option.some (.bindeRegion f0' f1')
      | _ => Option.none
    | some 50 =>
      match kids with
      | Code.pair f0 (Code.zero) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : Zugriffsform ← Encodable.decode f0n
          Option.some (.zugriff f0')
      | _ => Option.none
    | some 51 =>
      match kids with
      | Code.pair f0 (Code.zero) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : Fadenform ← Encodable.decode f0n
          Option.some (.faden f0')
      | _ => Option.none
    | some 52 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : Bool ← Encodable.decode f1n
          Option.some (.maskiere f0' f1')
      | _ => Option.none
    | some 53 =>
      match kids with
      | Code.pair f0 (Code.zero) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          Option.some (.prioritaet f0')
      | _ => Option.none
    | some 54 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          Option.some (.sendeUnterbrechung f0' f1')
      | _ => Option.none
    | some 55 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.zero))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : ℕ ← Encodable.decode f2n
          Option.some (.leiteLeitung f0' f1' f2')
      | _ => Option.none
    | _ => Option.none
  | _ => Option.none

def befehlVonCode (c : Code) : Option Befehl :=
  befehlVonCodeA c <|> befehlVonCodeB c

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

