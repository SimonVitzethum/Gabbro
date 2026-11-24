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

/-! ## Befehl

A command is a first-order tuple: a constructor tag followed by the encodings
of its fields. Dependent `Fin` fields are encoded through their own
`Encodable` instance, so no constructor is changed and no per-program data is
needed. -/

def befehlCode (b : Befehl) : Nat :=
  Encodable.encode <| match b with
  | .literal ziel wert => [0, ziel, wert]
  | .binaer op links => [1, Encodable.encode op, links]
  | .binden name quelle => [2, Encodable.encode name, quelle]
  | .wahrheitswert ziel wert => [3, ziel, Encodable.encode wert]
  | .lesen ziel index => [4, ziel, index]
  | .negativ ziel betrag => [5, ziel, betrag]
  | .negieren ziel => [6, ziel]
  | .verneinen ziel => [7, ziel]
  | .teilen links => [8, links]
  | .vergleichen op links => [9, Encodable.encode op, links]
  | .springeWenn quelle bei abstand => [10, quelle, Encodable.encode bei, abstand]
  | .zuweisen quelle index zieltyp => [11, quelle, index, Encodable.encode zieltyp]
  | .zurueck quelle zieltyp => [12, quelle, Encodable.encode zieltyp]
  | .springe abstand => [13, abstand]
  | .blockEnde freigabe => [14, freigabe]
  | .bindeWert quelle ziel global => [15, quelle, Encodable.encode ziel, Encodable.encode global]
  | .definiere name parameter result globale ueberspringe misstAbstieg ruft effects =>
      [16, Encodable.encode name, Encodable.encode parameter, Encodable.encode result,
        globale, ueberspringe, Encodable.encode misstAbstieg, Encodable.encode ruft,
        Encodable.encode effects]
  | .rufe name args bind =>
      [17, Encodable.encode name, Encodable.encode args, Encodable.encode bind]
  | .rueckVoid => [18]
  | .pruefeMass quelle => [19, quelle]
  | .setzePasszahl quelle stelle => [20, quelle, stelle]
  | .whileTest quelle ende handler => [21, quelle, ende, Encodable.encode handler]
  | .forAnfang unter ober index skipEmpty shadowed missingHandler =>
      [22, unter, ober, Encodable.encode index, skipEmpty,
        Encodable.encode shadowed, Encodable.encode missingHandler]
  | .forTest ende handler => [23, ende, Encodable.encode handler]
  | .forNaechster zurueck index => [24, zurueck, Encodable.encode index]
  | .zurueckSprung abstand => [25, abstand]
  | .starte name => [26, Encodable.encode name]
  | .ende => [27]
  | .baueArray ziel element count => [28, ziel, Encodable.encode element, count]
  | .liesArray basis element count => [29, basis, Encodable.encode element, count]
  | .baueTupel ziel types => [30, ziel, Encodable.encode types]
  | .liesTupelfeld basis types index => [31, basis, Encodable.encode types, Encodable.encode index]
  | .bindeTupel quelle types bind =>
      [32, quelle, Encodable.encode types, Encodable.encode bind]
  | .definiereRecord name labels types =>
      [33, Encodable.encode name, Encodable.encode labels, Encodable.encode types]
  | .baueRecord ziel name labels types sources =>
      [34, ziel, Encodable.encode name, Encodable.encode labels, Encodable.encode types,
        Encodable.encode sources]
  | .liesRecordFeld basis name labels types index =>
      [35, basis, Encodable.encode name, Encodable.encode labels, Encodable.encode types,
        Encodable.encode index]
  | .setzeRecordFeld source indexLocal name labels types index =>
      [36, source, indexLocal, Encodable.encode name, Encodable.encode labels,
        Encodable.encode types, Encodable.encode index]
  | .definiereVariante name labels cases =>
      [37, Encodable.encode name, Encodable.encode labels, Encodable.encode cases]
  | .baueVariante ziel name labels cases index =>
      [38, ziel, Encodable.encode name, Encodable.encode labels, Encodable.encode cases,
        Encodable.encode index]
  | .waehleVariante source name labels cases branches =>
      [39, source, Encodable.encode name, Encodable.encode labels, Encodable.encode cases,
        Encodable.encode branches]
  | .textLiteral ziel decoded => [40, ziel, Encodable.encode decoded]
  | .textConcat basis a b => [41, basis, a, b]
  | .textIndex basis capacity => [42, basis, capacity]
  | .substring basis capacity => [43, basis, capacity]
  | .textLength basis capacity => [44, basis, capacity]
  | .definiereTraeger count labels layout exported =>
      [45, count, Encodable.encode labels, Encodable.encode layout, Encodable.encode exported]
  | .optionIstBesetzt ziel count => [46, ziel, count]
  | .definiereEffektgruppe effects => [47, Encodable.encode effects]
  | .waehleUmgebung name abi row =>
      [48, Encodable.encode name, Encodable.encode abi, Encodable.encode row]
  | .bindeRegion receiver init => [49, receiver, Encodable.encode init]

def befehlDecode (n : Nat) : Option Befehl := do
  let fs : List Nat ← Encodable.decode n
  match fs with
  | [0, z, w] => some (.literal z w)
  | [1, op, l] =>
      let o : Arith ← Encodable.decode op
      some (.binaer o l)
  | [2, name, q] =>
      let nm : Identifier ← Encodable.decode name
      some (.binden nm q)
  | [3, z, w] =>
      let v : Bool ← Encodable.decode w
      some (.wahrheitswert z v)
  | [4, z, i] => some (.lesen z i)
  | [5, z, b] => some (.negativ z b)
  | [6, z] => some (.negieren z)
  | [7, z] => some (.verneinen z)
  | [8, l] => some (.teilen l)
  | [9, op, l] =>
      let o : Compare ← Encodable.decode op
      some (.vergleichen o l)
  | [10, q, bei, ab] =>
      let b : Bool ← Encodable.decode bei
      some (.springeWenn q b ab)
  | [11, q, i, t] =>
      let ty : Ty .value ← Encodable.decode t
      some (.zuweisen q i ty)
  | [12, q, t] =>
      let ty : Ty .value ← Encodable.decode t
      some (.zurueck q ty)
  | [13, ab] => some (.springe ab)
  | [14, f] => some (.blockEnde f)
  | [15, q, z, g] =>
      let ty : Ty .value ← Encodable.decode z
      let gl : Bool ← Encodable.decode g
      some (.bindeWert q ty gl)
  | [16, name, ps, res, glob, skip, meas, ruft, eff] => do
      let nm : Identifier ← Encodable.decode name
      let ps' : List (Ty .value) ← Encodable.decode ps
      let res' : Option (Ty .value) ← Encodable.decode res
      let meas' : Bool ← Encodable.decode meas
      let ruft' : List Rufstelle ← Encodable.decode ruft
      let eff' : Option (List CarrierEffect) ← Encodable.decode eff
      some (.definiere nm ps' res' glob skip meas' ruft' eff')
  | [17, name, args, bind] => do
      let nm : Identifier ← Encodable.decode name
      let args' : List (Ty .value) ← Encodable.decode args
      let bind' : Option (Ty .value) ← Encodable.decode bind
      some (.rufe nm args' bind')
  | [18] => some .rueckVoid
  | [19, q] => some (.pruefeMass q)
  | [20, q, st] => some (.setzePasszahl q st)
  | [21, q, ende, handler] =>
      let h : Identifier ← Encodable.decode handler
      some (.whileTest q ende h)
  | [22, unt, ob, idx, skip, sh, miss] => do
      let idx' : Ty .value ← Encodable.decode idx
      let sh' : Bool ← Encodable.decode sh
      let miss' : Bool ← Encodable.decode miss
      some (.forAnfang unt ob idx' skip sh' miss')
  | [23, ende, handler] =>
      let h : Option Identifier ← Encodable.decode handler
      some (.forTest ende h)
  | [24, back, idx] =>
      let idx' : Ty .value ← Encodable.decode idx
      some (.forNaechster back idx')
  | [25, ab] => some (.zurueckSprung ab)
  | [26, name] =>
      let nm : Identifier ← Encodable.decode name
      some (.starte nm)
  | [27] => some .ende
  | [28, z, el, cnt] =>
      let el' : Ty .value ← Encodable.decode el
      some (.baueArray z el' cnt)
  | [29, basis, el, cnt] =>
      let el' : Ty .value ← Encodable.decode el
      some (.liesArray basis el' cnt)
  | [30, z, types] =>
      let types' : List (Ty .value) ← Encodable.decode types
      some (.baueTupel z types')
  | [31, basis, types, index] => do
      let types' : List (Ty .value) ← Encodable.decode types
      let index' : Fin types'.length ← Encodable.decode index
      some (.liesTupelfeld basis types' index')
  | [32, q, types, bind] => do
      let types' : List (Ty .value) ← Encodable.decode types
      let bind' : List Bool ← Encodable.decode bind
      some (.bindeTupel q types' bind')
  | [33, name, labels, types] => do
      let name' : List Char ← Encodable.decode name
      let labels' : List Identifier ← Encodable.decode labels
      let types' : List (Ty .value) ← Encodable.decode types
      some (.definiereRecord name' labels' types')
  | [34, z, name, labels, types, sources] => do
      let name' : List Char ← Encodable.decode name
      let labels' : List Identifier ← Encodable.decode labels
      let types' : List (Ty .value) ← Encodable.decode types
      let sources' : List Nat ← Encodable.decode sources
      some (.baueRecord z name' labels' types' sources')
  | [35, basis, name, labels, types, index] => do
      let name' : List Char ← Encodable.decode name
      let labels' : List Identifier ← Encodable.decode labels
      let types' : List (Ty .value) ← Encodable.decode types
      let index' : Fin types'.length ← Encodable.decode index
      some (.liesRecordFeld basis name' labels' types' index')
  | [36, source, indexLocal, name, labels, types, index] => do
      let name' : List Char ← Encodable.decode name
      let labels' : List Identifier ← Encodable.decode labels
      let types' : List (Ty .value) ← Encodable.decode types
      let index' : Fin types'.length ← Encodable.decode index
      some (.setzeRecordFeld source indexLocal name' labels' types' index')
  | [37, name, labels, cases] => do
      let name' : List Char ← Encodable.decode name
      let labels' : List Identifier ← Encodable.decode labels
      let cases' : List (Option (Ty .value)) ← Encodable.decode cases
      some (.definiereVariante name' labels' cases')
  | [38, z, name, labels, cases, index] => do
      let name' : List Char ← Encodable.decode name
      let labels' : List Identifier ← Encodable.decode labels
      let cases' : List (Option (Ty .value)) ← Encodable.decode cases
      let index' : Fin cases'.length ← Encodable.decode index
      some (.baueVariante z name' labels' cases' index')
  | [39, source, name, labels, cases, branches] => do
      let name' : List Char ← Encodable.decode name
      let labels' : List Identifier ← Encodable.decode labels
      let cases' : List (Option (Ty .value)) ← Encodable.decode cases
      let branches' : List (Nat × Bool) ← Encodable.decode branches
      some (.waehleVariante source name' labels' cases' branches')
  | [40, z, decoded] =>
      let d : List Char ← Encodable.decode decoded
      some (.textLiteral z d)
  | [41, basis, a, b] => some (.textConcat basis a b)
  | [42, basis, cap] => some (.textIndex basis cap)
  | [43, basis, cap] => some (.substring basis cap)
  | [44, basis, cap] => some (.textLength basis cap)
  | [45, count, labels, layout, exported] => do
      let labels' : List (List Char) ← Encodable.decode labels
      let layout' : Ty .value ← Encodable.decode layout
      let exported' : Bool ← Encodable.decode exported
      some (.definiereTraeger count labels' layout' exported')
  | [46, z, count] => some (.optionIstBesetzt z count)
  | [47, effects] =>
      let e : List CarrierEffect ← Encodable.decode effects
      some (.definiereEffektgruppe e)
  | [48, name, abi, row] => do
      let nm : Identifier ← Encodable.decode name
      let abi' : DienstAbi ← Encodable.decode abi
      let row' : FirmwareZeile ← Encodable.decode row
      some (.waehleUmgebung nm abi' row')
  | [49, receiver, init] =>
      let init' : RegionInitializer ← Encodable.decode init
      some (.bindeRegion receiver init')
  | _ => none

instance : Encodable Befehl :=
  Encodable.ofLeftInjection befehlCode befehlDecode (by
    intro b
    cases b <;> simp [befehlCode, befehlDecode, Encodable.encodek, Fin.ext_iff])

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
