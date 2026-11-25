module

public import Core.Ast.Semantik.Runtime.Frame
public import Core.Ast.Semantik.Runtime.Atom.Form
import Init.Data.Vector.OfFn

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine

/-- One linearisation point per expression node or binding. A binary instruction
    consumes the slots left by its children. A binding takes its initializer's slot. -/
inductive Befehl where
  | literal (ziel : Nat) (wert : Nat)
  | binaer (op : Arith) (links : Nat)
  | binden (name : Identifier) (quelle : Nat)
  | wahrheitswert (ziel : Nat) (wert : Bool)
  | lesen (ziel index : Nat)
  | negativ (ziel : Nat) (betrag : Nat)
  | negieren (ziel : Nat)
  | verneinen (ziel : Nat)
  | teilen (links : Nat)
  | vergleichen (op : Compare) (links : Nat)
  | springeWenn (quelle : Nat) (bei : Bool) (abstand : Nat)
  | zuweisen (quelle index : Nat) (zieltyp : Ty .value)
  | zurueck (quelle : Nat) (zieltyp : Ty .value)
  | springe (abstand : Nat)
  | blockEnde (freigabe : Nat)
  | bindeWert (quelle : Nat) (ziel : Ty .value) (global : Bool)
  | definiere (name : Identifier) (parameter : List (Ty .value)) (result : Option (Ty .value))
      (globale ueberspringe : Nat) (misstAbstieg : Bool) (ruft : List Rufstelle)
      (effects : Option (List CarrierEffect))
  | rufe (name : Identifier) (args : List (Ty .value)) (bind : Option (Ty .value))
  | rueckVoid
  | pruefeMass (quelle : Nat)
  | setzePasszahl (quelle stelle : Nat)
  | whileTest (quelle ende : Nat) (handler : Identifier)
  | forAnfang (unter ober : Nat) (index : Ty .value) (skipEmpty : Nat) (shadowed missingHandler : Bool)
  | forTest (ende : Nat) (handler : Option Identifier)
  | forNaechster (zurueck : Nat) (index : Ty .value)
  | zurueckSprung (abstand : Nat)
  | starte (name : Identifier)
  | ende
  | baueArray (ziel : Nat) (element : Ty .value) (count : Nat)
  | liesArray (basis : Nat) (element : Ty .value) (count : Nat)
  | baueTupel (ziel : Nat) (types : List (Ty .value))
  | liesTupelfeld (basis : Nat) (types : List (Ty .value)) (index : Fin types.length)
  | bindeTupel (quelle : Nat) (types : List (Ty .value)) (bind : List Bool)
  | definiereRecord (name : List Char) (labels : List Identifier) (types : List (Ty .value))
  | baueRecord (ziel : Nat) (name : List Char) (labels : List Identifier)
      (types : List (Ty .value)) (sources : List Nat)
  | liesRecordFeld (basis : Nat) (name : List Char) (labels : List Identifier)
      (types : List (Ty .value)) (index : Fin types.length)
  | setzeRecordFeld (source indexLocal : Nat) (name : List Char) (labels : List Identifier)
      (types : List (Ty .value)) (index : Fin types.length)
  | definiereVariante (name : List Char) (labels : List Identifier) (cases : List (Option (Ty .value)))
  | baueVariante (ziel : Nat) (name : List Char) (labels : List Identifier)
      (cases : List (Option (Ty .value))) (index : Fin cases.length)
  | waehleVariante (source : Nat) (name : List Char) (labels : List Identifier)
      (cases : List (Option (Ty .value))) (branches : List (Nat × Bool))
  | textLiteral (ziel : Nat) (decoded : List Char)
  | textConcat (basis a b : Nat)
  | textIndex (basis capacity : Nat)
  | substring (basis capacity : Nat)
  | textLength (basis capacity : Nat)
  | definiereTraeger (count : Nat) (labels : List (List Char)) (layout : Ty .value) (exported : Bool)
  | optionIstBesetzt (ziel count : Nat)
  | definiereEffektgruppe (effects : List CarrierEffect)
  | waehleUmgebung (name : Identifier) (abi : Katalog.DienstAbi) (row : Katalog.FirmwareZeile)
  | bindeRegion (receiver : Nat) (init : RegionInitializer)
  | zugriff (form : Zugriffsform)

/-- Exact evaluation at the instruction boundary. Each result retains its source range. -/
def Befehl.auswerten (b : Befehl) (frame : Rahmen) (live : Nat → Bool := fun _slot => false) : Rahmen :=
  match b, frame with
  | .literal dst val, frame =>
    frame.schreibe dst (some ⟨.int val val, Zahl.literal val⟩)
  | .binaer op left, frame =>
    frame.schreibe left (do
      let a ← frame.zahl left
      let b ← frame.zahl (left + 1)
      pure (Ganzzahl.pack ⟨_, _, op.auswerten a.zahl b.zahl⟩))
  | .binden _ src, frame =>
    { frame with pc := frame.pc + 1, lokale := frame.temp src :: frame.lokale }
  | .wahrheitswert dst value, frame =>
    frame.schreibe dst (some ⟨.bool, value⟩)
  | .lesen dst index, frame =>
    frame.schreibe dst (frame.lokale[index]?.join)
  | .negativ dst magnitude, frame =>
    let value : Int := -(magnitude : Int)
    frame.schreibe dst (some ⟨.int value value, Zahl.literal value⟩)
  | .negieren dst, frame =>
    frame.schreibe dst ((frame.zahl dst).map fun a => Ganzzahl.pack ⟨_, _, a.zahl.neg⟩)
  | .verneinen dst, frame =>
    frame.schreibe dst (((frame.temp dst).bind alsBoolean).map fun bit => ⟨.bool, !bit⟩)
  | .teilen left, frame =>
    frame.schreibe left (do
      let a ← frame.zahl left
      let b ← frame.zahl (left + 1)
      if h : 1 ≤ b.lo ∨ b.hi ≤ -1 then
        pure ⟨quotientType a.lo a.hi b.lo, a.zahl.div b.zahl h⟩
      else none)
  | .vergleichen op left, frame =>
    frame.schreibe left (do
      let a ← frame.zahl left
      let b ← frame.zahl (left + 1)
      pure ⟨.bool, op.eval a.zahl.wert b.zahl.wert⟩)
  | .springeWenn src whenValue distance, frame =>
    let taken := (frame.temp src).bind alsBoolean = some whenValue
    { frame with pc := frame.pc + (if taken then distance else 1) }
  | .zuweisen src index target, frame =>
    let value := (frame.temp src).bind (wertIn target)
    { frame with pc := frame.pc + 1, lokale := frame.lokale.set index value }
  | .zurueck src target, frame =>
    frame.rueckkehr ((frame.temp src).bind (wertIn target))
  | .springe distance, frame =>
    { frame with pc := frame.pc + distance }
  | .blockEnde count, frame =>
    { frame with pc := frame.pc + 1, lokale := frame.lokale.drop count }

  | .bindeWert src target global, frame =>
    let value := (frame.temp src).bind (wertIn target)
    { frame with
      pc := frame.pc + 1, lokale := value :: frame.lokale,
      globale := if global then value :: frame.globale else frame.globale }
  | .definiere name ps result globals skip measure calls effects, frame =>
    let f : Funktion := ⟨name, frame.pc + 1, ps, result, globals, measure, calls, effects⟩
    { frame with pc := frame.pc + skip, funktionen := f :: frame.funktionen }
  | .rufe name args bind, frame => frame.ruf name args bind
  | .rueckVoid, frame => frame.rueckkehr none
  | .pruefeMass src, frame => frame.setzeMass src
  | .setzePasszahl src distance, frame =>
    match frame.zahl src with
    | some value => { frame with
        pc := frame.pc + 1,
        zaehler := Function.update frame.zaehler (frame.pc + distance) (some value.zahl.wert.toNat) }
    | none => frame.halt .ungueltigerWert
  | .whileTest src exit handler, frame =>
    match (frame.temp src).bind alsBoolean with
    | some test => frame.pass test exit (some handler)
    | none => frame.halt .ungueltigerWert
  | .forAnfang lower upper index skipEmpty shadowed missingHandler, frame => Id.run do
    let some a := frame.zahl lower | return frame.halt .ungueltigerWert
    let some b := frame.zahl upper | return frame.halt .ungueltigerWert
    if shadowed || (missingHandler && decide (a.zahl.wert < b.zahl.wert)) then
      return frame.halt .ungueltigerBereich
    if b.zahl.wert ≤ a.zahl.wert then return { frame with pc := frame.pc + skipEmpty }
    let some initial := wertIn index a.pack | return frame.halt .ungueltigerWert
    let next := frame.pc + 1
    return { frame with
      pc := next, lokale := some initial :: frame.lokale,
      obergrenzen := Function.update frame.obergrenzen next (some b),
      zaehler := Function.update frame.zaehler next (some (b.zahl.wert - a.zahl.wert).toNat) }
  | .forTest exit handler, frame => Id.run do
    let some current := frame.lokale.head?.join.bind alsGanzzahl | return frame.halt .ungueltigerWert
    let some upper := frame.obergrenzen frame.pc | return frame.halt .ungueltigerWert
    return frame.pass (decide (current.zahl.wert < upper.zahl.wert)) exit handler
  | .forNaechster back index, frame => Id.run do
    let some current := frame.lokale.head?.join.bind alsGanzzahl | return frame.halt .ungueltigerWert
    let next := current.zahl.wert + 1
    let some value := wertIn index (Ganzzahl.pack ⟨next, next, Zahl.literal next⟩)
      | return frame.halt .ungueltigerWert
    return { frame with pc := frame.pc - back, lokale := some value :: frame.lokale.drop 1 }
  | .zurueckSprung distance, frame => { frame with pc := frame.pc - distance }
  | .starte name, frame => Id.run do
    let names := frame.funktionen.map (fun f => f.name.val)
    if ¬ names.Nodup then return frame.halt (.ungueltigerRuf name)
    if let some f := frame.funktionen.find? (fun f =>
        !f.misstAbstieg && Funktion.rekursiv frame.funktionen f) then
      return frame.halt (.unbeschraenkteRekursion f.name)
    if let some bad := (frame.funktionen.flatMap Funktion.ruft).find? (fun call =>
        !(call.passt frame.funktionen)) then
      return frame.halt (.ungueltigerRuf bad.name)
    let some target := Funktion.finde frame.funktionen name | return frame.halt (.ungueltigerRuf name)
    let some entry := frame.eintrittArgumente target.parameter | return frame.halt (.ungueltigerRuf name)
    return entry.ruf name target.parameter target.result
  | .ende, frame => { frame with stopp := some .fertig, rueckgabe := frame.lokale.head?.join }
  | .baueArray dst element count, frame => frame.schreibe dst (do
    let values ← Vector.ofFnM (n := count) fun i => (frame.temp (dst + i.val)).bind (wertAls element)
    pure ⟨.array element count, values⟩)
  | .liesArray base element count, frame => frame.schreibe base (do
    let values : Vector (Wert element) count ← (frame.temp base).bind (wertAls (.array element count))
    let index ← frame.zahl (base + 1)
    if index.zahl.wert < 0 then none else
      if bound : index.zahl.wert.toNat < count then
        some ⟨element, values[index.zahl.wert.toNat]'bound⟩
      else none)
  | .baueTupel dst types, frame => frame.schreibe dst
    ((liesTupel frame.temp dst types).map fun values => ⟨tupleType types, values⟩)
  | .liesTupelfeld base types index, frame => frame.schreibe base (do
    let values ← (frame.temp base).bind (wertAls (tupleType types))
    pure ⟨types.get index, tupleGet types index values⟩)
  | .bindeTupel source types bind, frame =>
    let value := (frame.temp source).bind (wertAls (tupleType types))
    let locals := (value.map fun product => tupleLocals types product bind).getD []
    { frame with pc := frame.pc + 1, lokale := locals.reverse ++ frame.lokale }
  | .definiereRecord name labels types, frame =>
    frame.installSchema ⟨recordSchemaType name labels types, PUnit.unit⟩
  | .baueRecord dst name labels types sources, frame =>
    frame.schreibe dst ((liesRecord frame.temp types sources).map fun record =>
      ⟨recordValueType name labels types, record⟩)
  | .liesRecordFeld base name labels types index, frame => frame.schreibe base (do
    let record ← (frame.temp base).bind (wertAls (recordValueType name labels types))
    pure ⟨types.get index, tupleGet types index record⟩)
  | .setzeRecordFeld source indexLocal name labels types index, frame =>
    let type := recordValueType name labels types
    let updated : Option Dynamisch := do
      let old ← frame.lokale[indexLocal]?.join.bind (wertAls type)
      let value ← (frame.temp source).bind (wertAls (types.get index))
      pure ⟨type, tupleSet types index value old⟩
    { frame with pc := frame.pc + 1, lokale := frame.lokale.set indexLocal updated }
  | .definiereVariante name labels cases, frame =>
    frame.installSchema ⟨variantSchemaType name labels cases, PUnit.unit⟩
  | .baueVariante dst name labels cases index, frame => frame.schreibe dst (do
    let value ← variantActual (cases.get index) (frame.temp dst)
    pure ⟨variantValueType name labels cases, variantInject cases index value⟩)
  | .waehleVariante source name labels cases branches, frame => Id.run do
    let some value := (frame.temp source).bind (wertAls (variantValueType name labels cases)) |
      return frame.halt .ungueltigerWert
    let (tag, payload) := variantCase cases value
    let some (offset, bind) := branches[tag]? | return frame.halt .ungueltigerWert
    return { frame with pc := frame.pc + offset, lokale :=
      if bind then payload :: frame.lokale else frame.lokale }

  | .textLiteral dst decoded, frame =>
    frame.schreibe dst (some ⟨.text (sourceUtf8 decoded).size, TextValue.literal decoded⟩)
  | .textConcat base a b, frame =>
    frame.schreibe base (do
      let left ← (frame.temp base).bind (wertAls (.text a))
      let right ← (frame.temp (base + 1)).bind (wertAls (.text b))
      pure ⟨.text (a + b), left.concat right⟩)
  | .textIndex base capacity, frame => Id.run do
    let some text := (frame.temp base).bind (wertAls (.text capacity)) |
      return frame.halt .ungueltigerWert
    let some offset := frame.zahl (base + 1) | return frame.halt .ungueltigerWert
    if offset.zahl.wert < 0 then return frame.halt .ungueltigerWert
    let some byte := text.bytes[offset.zahl.wert.toNat]? | return frame.halt .ungueltigerWert
    return frame.schreibe base (some ⟨.int 0 255, byteValue byte⟩)
  | .substring base capacity, frame => Id.run do
    let some text := (frame.temp base).bind (wertAls (.text capacity)) |
      return frame.halt .ungueltigerWert
    let some first := frame.zahl (base + 1) | return frame.halt .ungueltigerWert
    let some last := frame.zahl (base + 2) | return frame.halt .ungueltigerWert
    if 0 ≤ first.zahl.wert ∧ first.zahl.wert ≤ last.zahl.wert ∧ last.zahl.wert ≤ (text.bytes.size : Int) then
      return frame.schreibe base (some ⟨.text capacity, text.slice first.zahl.wert.toNat last.zahl.wert.toNat⟩)
    return frame.halt .ungueltigerWert

  | .textLength base capacity, frame =>
    frame.schreibe base ((frame.temp base).bind (wertAls (.text capacity)) |>.map
      fun text => ⟨.int 0 capacity, text.lengthValue⟩)

  | .definiereTraeger count labels layout exported, frame =>
    frame.installSchema ⟨.carrierSchema count labels layout exported, PUnit.unit⟩

  | .optionIstBesetzt dst count, frame =>
    frame.schreibe dst (do
      let value ← (frame.temp dst).bind (wertAls (indexOptionType count))
      pure ⟨.bool, indexOptionPresent value⟩)
  | .definiereEffektgruppe effects, frame =>
    frame.installSchema ⟨.effectGroupSchema effects, PUnit.unit⟩
  | .waehleUmgebung name abi row, frame =>
    { frame with
      pc := frame.pc + 1
      environment := (name, abi, row) :: frame.environment }
  | .bindeRegion receiver init, frame => frame.bindeRegion receiver init live
  | .zugriff form, frame => form.uebertrag frame 0

abbrev Bedarf := (op : PartielleOperation) × Operanden op

/-- Division reports both operand magnitudes at the pre-state, as required by the natural-number guard row. -/
def Befehl.guard : Befehl → Rahmen → Option Bedarf
  | .teilen left, frame => do
    let a ← frame.zahl left
    let b ← frame.zahl (left + 1)
    pure ⟨.division, (a.zahl.wert.natAbs, b.zahl.wert.natAbs)⟩
  | .liesArray base _ count, frame => do
    let i ← frame.zahl (base + 1)
    pure ⟨.index, (if i.zahl.wert < 0 then count else i.zahl.wert.toNat, count)⟩
  | .textIndex base capacity, frame => do
    let text ← (frame.temp base).bind (wertAls (.text capacity))
    let offset ← frame.zahl (base + 1)
    pure ⟨.index, (if offset.zahl.wert < 0 then text.bytes.size else offset.zahl.wert.toNat, text.bytes.size)⟩
  | .substring base capacity, frame => do
    let text ← (frame.temp base).bind (wertAls (.text capacity))
    let first ← frame.zahl (base + 1)
    let last ← frame.zahl (base + 2)
    pure ⟨.teilfolge, (first.zahl.wert, last.zahl.wert, text.bytes.size)⟩
  | _, _ => none

end Gabbro.Core.Ast.Semantik
