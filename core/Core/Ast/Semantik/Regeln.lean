module

public import Core.Ast.Variant.Values
public import Core.Maschine.Start
public import Core.Ast.LowLevel.Meaning
import Init.Data.Vector.OfFn

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine

/-- The runtime integer package retains its two bounds and their proofs. -/
structure Ganzzahl where
  lo : Int
  hi : Int
  zahl : Zahl lo hi

def Ganzzahl.pack (value : Ganzzahl) : Dynamisch := ⟨.int value.lo value.hi, value.zahl⟩

def alsGanzzahl : Dynamisch → Option Ganzzahl
  | ⟨.int lo hi, value⟩ => some ⟨lo, hi, value⟩
  | ⟨.bool, _⟩ => none
  | ⟨.array .., _⟩ | ⟨.productEnd, _⟩ | ⟨.product .., _⟩ | ⟨.record .., _⟩ | ⟨.recordSchema .., _⟩
  | ⟨.address _, _⟩ | ⟨.ownedRegion, _⟩ | ⟨.regionView _, _⟩ => none
  | ⟨.sumEnd, _⟩ | ⟨.sum .., _⟩ | ⟨.variant .., _⟩ | ⟨.variantSchema .., _⟩ => none

def alsBoolean : Dynamisch → Option Bool
  | ⟨.bool, value⟩ => some value
  | ⟨.int .., _⟩ => none
  | ⟨.address _, _⟩ | ⟨.ownedRegion, _⟩ | ⟨.regionView _, _⟩ => none
  | ⟨.array .., _⟩ | ⟨.productEnd, _⟩ | ⟨.product .., _⟩ | ⟨.record .., _⟩ | ⟨.recordSchema .., _⟩
  | ⟨.sumEnd, _⟩ | ⟨.sum .., _⟩ | ⟨.variant .., _⟩ | ⟨.variantSchema .., _⟩ => none

def anfangswert : Ty .value → Option Dynamisch
  | .bool => some ⟨.bool, false⟩
  | .int lo hi =>
    if ordered : lo ≤ hi then some ⟨.int lo hi, ⟨lo, Int.le_refl _, ordered⟩⟩ else none
  | .recordSchema name labels layout => some ⟨.recordSchema name labels layout, PUnit.unit⟩
  | .variantSchema name labels payloads layout => some ⟨.variantSchema name labels payloads layout, PUnit.unit⟩
  | _ => none

inductive Abschluss where
  | fertig
  | ungueltigerRuf (name : Identifier)
  | unbeschraenkteRekursion (name : Identifier)
  | abstieg (name : Identifier)
  | ueberlauf (handler : Option Identifier)
  | ungueltigerBereich
  | ungueltigerWert

structure Rufstelle where
  name : Identifier
  args : List (Ty .value)
  bind : Option (Ty .value)

structure Funktion where
  name : Identifier
  adresse : Nat
  parameter : List (Ty .value)
  result : Option (Ty .value)
  konstanten : Nat
  misstAbstieg : Bool
  ruft : List Rufstelle

structure Fortsetzung where
  pc : Nat
  temp : Nat → Option Dynamisch
  lokale : List (Option Dynamisch)
  zaehler : Nat → Option Nat
  obergrenzen : Nat → Option Ganzzahl
  funktion : Option Identifier
  mass : Option Nat
  eingang : Option (Ty .value)

/-- Each context has its own instruction pointer, temporary slots and local values.
    Locals are stored in scope order. Temporaries are numbered by the elaborator. -/
structure Rahmen where
  pc : Nat
  temp : Nat → Option Dynamisch
  lokale : List (Option Dynamisch)
  rueckgabe : Option Dynamisch
  stopp : Option Abschluss := none
  zaehler : Nat → Option Nat := fun _slot => none
  obergrenzen : Nat → Option Ganzzahl := fun _slot => none
  globale : List (Option Dynamisch) := []
  funktionen : List Funktion := []
  fortsetzungen : List Fortsetzung := []
  funktion : Option Identifier := none
  mass : Option Nat := none
  arrivalRegions : List Katalog.Strecke := []
  platform : Katalog.Plattform := .x86_64
  environment : List (Identifier × Katalog.DienstAbi × Katalog.FirmwareZeile) := []

/-- Fragment entry chooses the lower endpoint of each nonempty incoming interval.
    A source unit starts with the empty scope. -/
def Rahmen.start (scope : Scope) : Rahmen :=
  { pc := 0, temp := fun _slot => none,
    lokale := scope.map (fun binding => anfangswert binding.type), rueckgabe := none }

def Rahmen.schreibe (frame : Rahmen) (ziel : Nat) (value : Option Dynamisch) : Rahmen :=
  { frame with pc := frame.pc + 1, temp := Function.update frame.temp ziel value }

def Rahmen.zahl (frame : Rahmen) (slot : Nat) : Option Ganzzahl :=
  (frame.temp slot).bind alsGanzzahl

def Rahmen.halt (frame : Rahmen) (reason : Abschluss) : Rahmen :=
  { frame with stopp := some reason }

def tyFits : Ty .value → Ty .value → Bool
  | .bool, .bool => true
  | .int lo hi, .int lower upper => decide (lower ≤ lo ∧ hi ≤ upper)
  | .array _ 0, .array _ 0 => true
  | a, b => decide (a = b)

def Funktion.finde (funktionen : List Funktion) (name : Identifier) : Option Funktion :=
  funktionen.find? (fun f => f.name.val == name.val)

def Funktion.erreichbar (funktionen : List Funktion) (ziel : Identifier) : Nat → Identifier → Bool
  | 0, name => name.val == ziel.val
  | fuel + 1, name =>
    name.val == ziel.val ||
      ((finde funktionen name).map (fun f => f.ruft.any (fun call =>
        erreichbar funktionen ziel fuel call.name))).getD false

def Funktion.rekursiv (funktionen : List Funktion) (f : Funktion) : Bool :=
  f.ruft.any fun call => erreichbar funktionen f.name funktionen.length call.name

def Rufstelle.passt (call : Rufstelle) (funktionen : List Funktion) : Bool :=
  match Funktion.finde funktionen call.name with
  | none => false
  | some target =>
    call.args.length == target.parameter.length &&
      (call.args.zip target.parameter).all (fun pair => tyFits pair.1 pair.2) &&
      match call.bind, target.result with
      | none, none | none, some _result => true
      | some written, some declared => tyFits declared written
      | some _written, none => false

def Rahmen.rufArgumente (frame : Rahmen) (slot : Nat) :
    List (Ty .value) → List (Ty .value) → Option (List (Option Dynamisch))
  | [], [] => some []
  | source :: sources, target :: targets => do
    if !tyFits source target then none else
      let v ← (frame.temp slot).bind (wertIn target)
      let rest ← frame.rufArgumente (slot + 1) sources targets
      pure (some v :: rest)
  | [], _target :: _targets | _source :: _sources, [] => none

def Rahmen.ruf (frame : Rahmen) (name : Identifier) (sources : List (Ty .value))
    (bind : Option (Ty .value)) : Rahmen := Id.run do
  let bad := frame.halt (.ungueltigerRuf name)
  let some callee := Funktion.finde frame.funktionen name | return bad
  let some args := frame.rufArgumente 0 sources callee.parameter | return bad
  if let some target := bind then
    let some source := callee.result | return bad
    if !tyFits source target then return bad
  let kont : Fortsetzung :=
    ⟨frame.pc + 1, frame.temp, frame.lokale, frame.zaehler, frame.obergrenzen, frame.funktion, frame.mass, bind⟩
  let stack := kont :: frame.fortsetzungen
  if stack.any (fun k => (k.funktion.map Subtype.val) == some name.val) && !callee.misstAbstieg then
    return frame.halt (.abstieg name)
  return { frame with
    pc := callee.adresse, temp := fun _slot => none,
    lokale := args.reverse ++ frame.globale.drop (frame.globale.length - callee.konstanten),
    zaehler := fun _slot => none, obergrenzen := fun _slot => none, fortsetzungen := stack, funktion := some name, mass := none }

def Rahmen.rueckkehr (frame : Rahmen) (result : Option Dynamisch) : Rahmen :=
  match frame.fortsetzungen with
  | [] => { frame with
      pc := frame.pc + 1, rueckgabe := result,
      stopp := if result.isSome then none else some .fertig }
  | k :: stack =>
    let locals := match k.eingang with
      | none => k.lokale
      | some target => result.bind (wertIn target) :: k.lokale
    { frame with
      pc := k.pc, temp := k.temp, lokale := locals, zaehler := k.zaehler,
      obergrenzen := k.obergrenzen,
      funktion := k.funktion, mass := k.mass, fortsetzungen := stack }

def Rahmen.setzeMass (frame : Rahmen) (slot : Nat) : Rahmen := Id.run do
  let some name := frame.funktion | return frame.halt .ungueltigerWert
  let some value := frame.zahl slot | return frame.halt (.abstieg name)
  let n := value.zahl.wert.toNat
  let previous := frame.fortsetzungen.find? (fun k => (k.funktion.map Subtype.val) == some name.val)
  if value.zahl.wert < 0 then return frame.halt (.abstieg name)
  if let some k := previous then
    let some old := k.mass | return frame.halt (.abstieg name)
    if n ≥ old then return frame.halt (.abstieg name)
  return { frame with pc := frame.pc + 1, mass := some n }

def Rahmen.pass (frame : Rahmen) (takePass : Bool) (exit : Nat)
    (handler : Option Identifier) : Rahmen :=
  if !takePass then
    { frame with pc := frame.pc + exit, zaehler := Function.update frame.zaehler frame.pc none }
  else match frame.zaehler frame.pc with
    | some (n + 1) =>
      { frame with pc := frame.pc + 1, zaehler := Function.update frame.zaehler frame.pc (some n) }
    | some 0 | none => frame.halt (.ueberlauf handler)

/-- Entry slots are the positions of the platform's owned RAM grants.
    Ordinary calls cannot supply regions through copyable expressions. -/
def Rahmen.eintrittArgumente (frame : Rahmen) (types : List (Ty .value)) : Option Rahmen :=
  if types = [] then some { frame with lokale := [] }
  else if types.all (· == .ownedRegion) && types.length ≤ frame.arrivalRegions.length then
    some { frame with lokale := [], temp := fun slot =>
      if slot < types.length then some ⟨.ownedRegion, slot⟩ else none }
  else none

def Dynamisch.borrowsRegion (slot : Nat) : Dynamisch → Bool
  | ⟨.regionView _, view⟩ => view.slot == slot
  | _ => false

def Rahmen.borrowsRegion (frame : Rahmen) (slot : Nat) : Bool :=
  let hasView := List.any (fun v : Option Dynamisch => v.any (Dynamisch.borrowsRegion slot))
  hasView frame.lokale || frame.fortsetzungen.any (fun continuation => hasView continuation.lokale)

def Rahmen.bindeRegion (frame : Rahmen) (receiver : Nat) (init : RegionInitializer)
    (live : Nat → Bool) : Rahmen := Id.run do
  let refused := frame.halt .ungueltigerBereich
  let some slot := frame.lokale[receiver]?.join.bind (wertAls .ownedRegion) | return refused
  let some extent := frame.arrivalRegions[slot]? | return refused
  if !live slot || frame.borrowsRegion slot then return refused
  let some value := LowLevel.RegionInitializer.value frame.platform.ziel slot extent init | return refused
  return { frame with pc := frame.pc + 1, lokale := some value :: frame.lokale }

abbrev Zustand := Maschine.Zustand PUnit PUnit Int PUnit Rahmen PUnit
abbrev Plan := SchrittPlan PUnit PUnit Int PUnit
abbrev Regel := Maschine.Regel Zustand Plan PUnit

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
  | waehleUmgebung (name : Identifier) (abi : Katalog.DienstAbi) (row : Katalog.FirmwareZeile)
  | bindeRegion (receiver : Nat) (init : RegionInitializer)

/-- Exact evaluation at the instruction boundary. Each result retains its source range. -/
def Befehl.auswerten (b : Befehl) (frame : Rahmen) (live : Nat → Bool := fun _ => false) : Rahmen :=
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
  | .definiere name ps result globals skip measure calls, frame =>
    let f : Funktion := ⟨name, frame.pc + 1, ps, result, globals, measure, calls⟩
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
    let schema : Dynamisch := ⟨recordSchemaType name labels types, PUnit.unit⟩
    { frame with pc := frame.pc + 1, lokale := some schema :: frame.lokale, globale := some schema :: frame.globale }
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
    let schema : Dynamisch := ⟨variantSchemaType name labels cases, PUnit.unit⟩
    { frame with pc := frame.pc + 1, lokale := some schema :: frame.lokale, globale := some schema :: frame.globale }
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

  | .bindeRegion receiver init, frame => frame.bindeRegion receiver init live
  | .waehleUmgebung name abi row, frame =>
    { frame with
      pc := frame.pc + 1
      environment := (name, abi, row) :: frame.environment }

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
  | _, _ => none

def plan : Plan := ⟨.intern, [], [], fun _ort => false, fun _ort => .na, fun _ort => 0⟩

def Befehl.nach (b : Befehl) (c : Kontext) (s : Zustand) : Zustand :=
  let live := fun slot => c == Kontext.faden 0 && s.rechte.lebt slot &&
    s.rechte.gen slot == 0 && (match s.leihen slot with | .eigen => true | .verliehen _ => false)
  { s with lokal := Function.update s.lokal c (b.auswerten (s.lokal c) live) }

/-- The context-local transition used by the ideal rule. -/
def Befehl.ideal (b : Befehl) (c : Kontext) (s : Zustand) (_ : PUnit.{1})
    (plans : List Plan) (u : Zustand) : Prop :=
  plans = [plan] ∧ u = b.nach c s

/-- The concrete one-step realization uses the same mathematical transfer on
    context-local values. Shared events go through the machine protocol. -/
def Befehl.impl (b : Befehl) (c : Kontext) (s : Zustand) (_ : PUnit.{1})
    (plans : List Plan) (u : Zustand) : Prop :=
  plans = [plan] ∧ u = b.nach c s

def Befehl.regel (b : Befehl) : Regel := ⟨b.impl, b.ideal⟩

abbrev LokalSystem := MaschinenSystem PUnit PUnit Int PUnit Rahmen PUnit PUnit PUnit Befehl

def eintritt : Kontext := .faden 0

def kopf (code : List Befehl) (s : Zustand) (c : Kontext) : Option Befehl :=
  if c = eintritt then
    match s.status c with
    | .ruht => none
    | .laeuft =>
      match (s.lokal c).rueckgabe with
      | none => if (s.lokal c).stopp.isNone then code[(s.lokal c).pc]? else none
      | some _ => none
    | .beendet _ => none
  else none

def system (code : List Befehl) : LokalSystem :=
  ⟨Befehl.regel, kopf code, fun s c => kopf code s c = none, fun _ _ _ => False⟩

end Gabbro.Core.Ast.Semantik
