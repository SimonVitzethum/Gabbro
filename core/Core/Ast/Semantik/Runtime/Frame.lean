module

public import Core.Ast.Variant.Values
public import Core.Maschine.Start
public import Core.Katalog.FirmwareNamen
public import Core.Ast.LowLevel.Meaning

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
  | ⟨.sumEnd, _⟩ | ⟨.sum .., _⟩ | ⟨.variant .., _⟩ | ⟨.variantSchema .., _⟩ | ⟨.text _, _⟩ | ⟨.carrierSchema .., _⟩ | ⟨.effectGroupSchema _, _⟩ => none
  | ⟨.address _, _⟩ | ⟨.ownedRegion, _⟩ | ⟨.regionView _, _⟩ => none

def alsBoolean : Dynamisch → Option Bool
  | ⟨.bool, value⟩ => some value
  | ⟨.int .., _⟩ => none
  | ⟨.array .., _⟩ | ⟨.productEnd, _⟩ | ⟨.product .., _⟩ | ⟨.record .., _⟩ | ⟨.recordSchema .., _⟩
  | ⟨.sumEnd, _⟩ | ⟨.sum .., _⟩ | ⟨.variant .., _⟩ | ⟨.variantSchema .., _⟩ | ⟨.text _, _⟩ | ⟨.carrierSchema .., _⟩ | ⟨.effectGroupSchema _, _⟩ => none
  | ⟨.address _, _⟩ | ⟨.ownedRegion, _⟩ | ⟨.regionView _, _⟩ => none

def anfangswert : Ty .value → Option Dynamisch
  | .bool => some ⟨.bool, false⟩
  | .int lo hi =>
    if ordered : lo ≤ hi then some ⟨.int lo hi, ⟨lo, Int.le_refl _, ordered⟩⟩ else none
  | .recordSchema name labels layout => some ⟨.recordSchema name labels layout, PUnit.unit⟩
  | .variantSchema name labels payloads layout => some ⟨.variantSchema name labels payloads layout, PUnit.unit⟩
  | .carrierSchema count labels layout exported => some ⟨.carrierSchema count labels layout exported, PUnit.unit⟩
  | .effectGroupSchema effects => some ⟨.effectGroupSchema effects, PUnit.unit⟩
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
  effects : Option (List CarrierEffect)

structure Funktion where
  name : Identifier
  adresse : Nat
  parameter : List (Ty .value)
  result : Option (Ty .value)
  konstanten : Nat
  misstAbstieg : Bool
  ruft : List Rufstelle
  effects : Option (List CarrierEffect)

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

def Rahmen.installSchema (frame : Rahmen) (schema : Dynamisch) : Rahmen :=
  { frame with pc := frame.pc + 1, lokale := some schema :: frame.lokale, globale := some schema :: frame.globale }

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

/-- Explicit contracts bound the effect hull at their call sites. An omitted
    contract follows the outgoing calls, visiting each function at most once. -/
def Funktion.effectHull (funktionen : List Funktion) :
    Nat → List (List Char) → List Identifier → List CarrierEffect
  | 0, _, _ | _, _, [] => []
  | fuel + 1, visited, name :: pending =>
    if visited.contains name.val then effectHull funktionen fuel visited pending
    else
      let seen := name.val :: visited
      match finde funktionen name with
      | none => effectHull funktionen fuel seen pending
      | some target =>
        match target.effects with
        | some effects => effects ++ effectHull funktionen fuel seen pending
        | none => effectHull funktionen fuel seen (target.ruft.map Rufstelle.name ++ pending)

def Funktion.requiredEffects (funktionen : List Funktion) (target : Funktion) : List CarrierEffect :=
  match target.effects with
  | some effects => effects
  | none =>
    let fuel := funktionen.foldl (fun n f => n + f.ruft.length) 1
    effectHull funktionen fuel [] [target.name]

def Rufstelle.passt (call : Rufstelle) (funktionen : List Funktion) : Bool :=
  match Funktion.finde funktionen call.name with
  | none => false
  | some target =>
    let effectsPass := match call.effects with
      | none => true
      | some provided =>
        (Funktion.requiredEffects funktionen target).all (fun effect => decide (effect ∈ provided))
    call.args.length == target.parameter.length &&
      (call.args.zip target.parameter).all (fun pair => tyFits pair.1 pair.2) &&
      effectsPass &&
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

abbrev Zustand := Maschine.Zustand PUnit PUnit Int PUnit Rahmen PUnit
abbrev Plan := SchrittPlan PUnit PUnit Int PUnit
abbrev Regel := Maschine.Regel Zustand Plan PUnit


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
  let hasView := fun (values : List (Option Dynamisch)) =>
    values.any (fun v => v.any (Dynamisch.borrowsRegion slot))
  hasView frame.lokale || frame.fortsetzungen.any (fun continuation => hasView continuation.lokale)

def Rahmen.bindeRegion (frame : Rahmen) (receiver : Nat) (init : RegionInitializer)
    (live : Nat → Bool) : Rahmen := Id.run do
  let refused := frame.halt .ungueltigerBereich
  let some (slot : Nat) := frame.lokale[receiver]?.join.bind (wertAls .ownedRegion) | return refused
  let some extent := frame.arrivalRegions[slot]? | return refused
  if !live slot || frame.borrowsRegion slot then return refused
  let some value := LowLevel.RegionInitializer.value frame.platform.ziel slot extent init | return refused
  return { frame with pc := frame.pc + 1, lokale := some value :: frame.lokale }

abbrev Zustand := Maschine.Zustand PUnit PUnit Int PUnit Rahmen PUnit
abbrev Plan := SchrittPlan PUnit PUnit Int PUnit
abbrev Regel := Maschine.Regel Zustand Plan PUnit

/-- One linearisation point per expression node or binding. A binary instruction
    consumes the slots left by its children. A binding takes its initializer's slot. -/
end Gabbro.Core.Ast.Semantik
