module

public import Core.Beobachtung.Unentscheidbar.Simulation.KodierErweitert

noncomputable section

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ast.LowLevel
open Gabbro.Core.Katalog
open Gabbro.Core.Text
open Nat.Partrec


/-! ## Befehl as a first-order `Code` tree -/

def befehlZuCode : Befehl → Code
  | .literal f0 f1 => Code.pair (natZuCode 0) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .binaer f0 f1 => Code.pair (natZuCode 1) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .binden f0 f1 => Code.pair (natZuCode 2) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .wahrheitswert f0 f1 => Code.pair (natZuCode 3) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .lesen f0 f1 => Code.pair (natZuCode 4) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .negativ f0 f1 => Code.pair (natZuCode 5) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .negieren f0 => Code.pair (natZuCode 6) (Code.pair (natZuCode (Encodable.encode f0)) (Code.zero))
  | .verneinen f0 => Code.pair (natZuCode 7) (Code.pair (natZuCode (Encodable.encode f0)) (Code.zero))
  | .teilen f0 => Code.pair (natZuCode 8) (Code.pair (natZuCode (Encodable.encode f0)) (Code.zero))
  | .vergleichen f0 f1 => Code.pair (natZuCode 9) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .springeWenn f0 f1 f2 => Code.pair (natZuCode 10) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.zero))))
  | .zuweisen f0 f1 f2 => Code.pair (natZuCode 11) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.zero))))
  | .zurueck f0 f1 => Code.pair (natZuCode 12) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .springe f0 => Code.pair (natZuCode 13) (Code.pair (natZuCode (Encodable.encode f0)) (Code.zero))
  | .blockEnde f0 => Code.pair (natZuCode 14) (Code.pair (natZuCode (Encodable.encode f0)) (Code.zero))
  | .bindeWert f0 f1 f2 => Code.pair (natZuCode 15) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.zero))))
  | .definiere f0 f1 f2 f3 f4 f5 f6 f7 => Code.pair (natZuCode 16) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.pair (natZuCode (Encodable.encode f3)) (Code.pair (natZuCode (Encodable.encode f4)) (Code.pair (natZuCode (Encodable.encode f5)) (Code.pair (natZuCode (Encodable.encode f6)) (Code.pair (natZuCode (Encodable.encode f7)) (Code.zero)))))))))
  | .rufe f0 f1 f2 => Code.pair (natZuCode 17) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.zero))))
  | .rueckVoid => Code.pair (natZuCode 18) Code.zero
  | .pruefeMass f0 => Code.pair (natZuCode 19) (Code.pair (natZuCode (Encodable.encode f0)) (Code.zero))
  | .setzePasszahl f0 f1 => Code.pair (natZuCode 20) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .whileTest f0 f1 f2 => Code.pair (natZuCode 21) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.zero))))
  | .forAnfang f0 f1 f2 f3 f4 f5 => Code.pair (natZuCode 22) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.pair (natZuCode (Encodable.encode f3)) (Code.pair (natZuCode (Encodable.encode f4)) (Code.pair (natZuCode (Encodable.encode f5)) (Code.zero)))))))
  | .forTest f0 f1 => Code.pair (natZuCode 23) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .forNaechster f0 f1 => Code.pair (natZuCode 24) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .zurueckSprung f0 => Code.pair (natZuCode 25) (Code.pair (natZuCode (Encodable.encode f0)) (Code.zero))
  | .starte f0 => Code.pair (natZuCode 26) (Code.pair (natZuCode (Encodable.encode f0)) (Code.zero))
  | .ende => Code.pair (natZuCode 27) Code.zero
  | .baueArray f0 f1 f2 => Code.pair (natZuCode 28) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.zero))))
  | .liesArray f0 f1 f2 => Code.pair (natZuCode 29) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.zero))))
  | .baueTupel f0 f1 => Code.pair (natZuCode 30) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .liesTupelfeld f0 f1 f2 => Code.pair (natZuCode 31) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.zero))))
  | .bindeTupel f0 f1 f2 => Code.pair (natZuCode 32) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.zero))))
  | .definiereRecord f0 f1 f2 => Code.pair (natZuCode 33) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.zero))))
  | .baueRecord f0 f1 f2 f3 f4 => Code.pair (natZuCode 34) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.pair (natZuCode (Encodable.encode f3)) (Code.pair (natZuCode (Encodable.encode f4)) (Code.zero))))))
  | .liesRecordFeld f0 f1 f2 f3 f4 => Code.pair (natZuCode 35) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.pair (natZuCode (Encodable.encode f3)) (Code.pair (natZuCode (Encodable.encode f4)) (Code.zero))))))
  | .setzeRecordFeld f0 f1 f2 f3 f4 f5 => Code.pair (natZuCode 36) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.pair (natZuCode (Encodable.encode f3)) (Code.pair (natZuCode (Encodable.encode f4)) (Code.pair (natZuCode (Encodable.encode f5)) (Code.zero)))))))
  | .definiereVariante f0 f1 f2 => Code.pair (natZuCode 37) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.zero))))
  | .baueVariante f0 f1 f2 f3 f4 => Code.pair (natZuCode 38) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.pair (natZuCode (Encodable.encode f3)) (Code.pair (natZuCode (Encodable.encode f4)) (Code.zero))))))
  | .waehleVariante f0 f1 f2 f3 f4 => Code.pair (natZuCode 39) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.pair (natZuCode (Encodable.encode f3)) (Code.pair (natZuCode (Encodable.encode f4)) (Code.zero))))))
  | .textLiteral f0 f1 => Code.pair (natZuCode 40) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .textConcat f0 f1 f2 => Code.pair (natZuCode 41) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.zero))))
  | .textIndex f0 f1 => Code.pair (natZuCode 42) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .substring f0 f1 => Code.pair (natZuCode 43) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .textLength f0 f1 => Code.pair (natZuCode 44) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .definiereTraeger f0 f1 f2 f3 => Code.pair (natZuCode 45) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.pair (natZuCode (Encodable.encode f3)) (Code.zero)))))
  | .optionIstBesetzt f0 f1 => Code.pair (natZuCode 46) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .definiereEffektgruppe f0 => Code.pair (natZuCode 47) (Code.pair (natZuCode (Encodable.encode f0)) (Code.zero))
  | .waehleUmgebung f0 f1 f2 => Code.pair (natZuCode 48) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.pair (natZuCode (Encodable.encode f2)) (Code.zero))))
  | .bindeRegion f0 f1 => Code.pair (natZuCode 49) (Code.pair (natZuCode (Encodable.encode f0)) (Code.pair (natZuCode (Encodable.encode f1)) (Code.zero)))
  | .zugriff f0 => Code.pair (natZuCode 50) (Code.pair (natZuCode (Encodable.encode f0)) (Code.zero))
  | .faden f0 => Code.pair (natZuCode 51) (Code.pair (natZuCode (Encodable.encode f0)) (Code.zero))

def befehlVonCodeA : Code → Option Befehl
  | Code.pair tag kids =>
    match codeZuNat tag with
    | some 0 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          Option.some (.literal f0' f1')
      | _ => Option.none
    | some 1 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : Arith ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          Option.some (.binaer f0' f1')
      | _ => Option.none
    | some 2 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : Identifier ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          Option.some (.binden f0' f1')
      | _ => Option.none
    | some 3 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : Bool ← Encodable.decode f1n
          Option.some (.wahrheitswert f0' f1')
      | _ => Option.none
    | some 4 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          Option.some (.lesen f0' f1')
      | _ => Option.none
    | some 5 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          Option.some (.negativ f0' f1')
      | _ => Option.none
    | some 6 =>
      match kids with
      | Code.pair f0 (Code.zero) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          Option.some (.negieren f0')
      | _ => Option.none
    | some 7 =>
      match kids with
      | Code.pair f0 (Code.zero) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          Option.some (.verneinen f0')
      | _ => Option.none
    | some 8 =>
      match kids with
      | Code.pair f0 (Code.zero) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          Option.some (.teilen f0')
      | _ => Option.none
    | some 9 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : Compare ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          Option.some (.vergleichen f0' f1')
      | _ => Option.none
    | some 10 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.zero))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : Bool ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : ℕ ← Encodable.decode f2n
          Option.some (.springeWenn f0' f1' f2')
      | _ => Option.none
    | some 11 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.zero))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : Ty .value ← Encodable.decode f2n
          Option.some (.zuweisen f0' f1' f2')
      | _ => Option.none
    | some 12 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : Ty .value ← Encodable.decode f1n
          Option.some (.zurueck f0' f1')
      | _ => Option.none
    | some 13 =>
      match kids with
      | Code.pair f0 (Code.zero) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          Option.some (.springe f0')
      | _ => Option.none
    | some 14 =>
      match kids with
      | Code.pair f0 (Code.zero) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          Option.some (.blockEnde f0')
      | _ => Option.none
    | some 15 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.zero))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : Ty .value ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : Bool ← Encodable.decode f2n
          Option.some (.bindeWert f0' f1' f2')
      | _ => Option.none
    | some 16 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.pair f3 (Code.pair f4 (Code.pair f5 (Code.pair f6 (Code.pair f7 (Code.zero)))))))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : Identifier ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : List (Ty .value) ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : Option (Ty .value) ← Encodable.decode f2n
          let f3n : ℕ ← codeZuNat f3
          let f3' : ℕ ← Encodable.decode f3n
          let f4n : ℕ ← codeZuNat f4
          let f4' : ℕ ← Encodable.decode f4n
          let f5n : ℕ ← codeZuNat f5
          let f5' : Bool ← Encodable.decode f5n
          let f6n : ℕ ← codeZuNat f6
          let f6' : List Rufstelle ← Encodable.decode f6n
          let f7n : ℕ ← codeZuNat f7
          let f7' : Option (List CarrierEffect) ← Encodable.decode f7n
          Option.some (.definiere f0' f1' f2' f3' f4' f5' f6' f7')
      | _ => Option.none
    | some 17 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.zero))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : Identifier ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : List (Ty .value) ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : Option (Ty .value) ← Encodable.decode f2n
          Option.some (.rufe f0' f1' f2')
      | _ => Option.none
    | some 18 =>
      match kids with
      | Code.zero => Option.some .rueckVoid
      | _ => Option.none
    | some 19 =>
      match kids with
      | Code.pair f0 (Code.zero) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          Option.some (.pruefeMass f0')
      | _ => Option.none
    | some 20 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          Option.some (.setzePasszahl f0' f1')
      | _ => Option.none
    | some 21 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.zero))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : Identifier ← Encodable.decode f2n
          Option.some (.whileTest f0' f1' f2')
      | _ => Option.none
    | some 22 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.pair f2 (Code.pair f3 (Code.pair f4 (Code.pair f5 (Code.zero)))))) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : ℕ ← Encodable.decode f1n
          let f2n : ℕ ← codeZuNat f2
          let f2' : Ty .value ← Encodable.decode f2n
          let f3n : ℕ ← codeZuNat f3
          let f3' : ℕ ← Encodable.decode f3n
          let f4n : ℕ ← codeZuNat f4
          let f4' : Bool ← Encodable.decode f4n
          let f5n : ℕ ← codeZuNat f5
          let f5' : Bool ← Encodable.decode f5n
          Option.some (.forAnfang f0' f1' f2' f3' f4' f5')
      | _ => Option.none
    | some 23 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : Option Identifier ← Encodable.decode f1n
          Option.some (.forTest f0' f1')
      | _ => Option.none
    | some 24 =>
      match kids with
      | Code.pair f0 (Code.pair f1 (Code.zero)) => do
          let f0n : ℕ ← codeZuNat f0
          let f0' : ℕ ← Encodable.decode f0n
          let f1n : ℕ ← codeZuNat f1
          let f1' : Ty .value ← Encodable.decode f1n
          Option.some (.forNaechster f0' f1')
      | _ => Option.none
    | _ => Option.none
  | _ => Option.none

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

