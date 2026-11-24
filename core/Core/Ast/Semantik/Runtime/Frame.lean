module

public import Core.Ast.Variant.Values
public import Core.Maschine.Start

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

def alsBoolean : Dynamisch → Option Bool
  | ⟨.bool, value⟩ => some value
  | ⟨.int .., _⟩ => none
  | ⟨.array .., _⟩ | ⟨.productEnd, _⟩ | ⟨.product .., _⟩ | ⟨.record .., _⟩ | ⟨.recordSchema .., _⟩
  | ⟨.sumEnd, _⟩ | ⟨.sum .., _⟩ | ⟨.variant .., _⟩ | ⟨.variantSchema .., _⟩ | ⟨.text _, _⟩ | ⟨.carrierSchema .., _⟩ | ⟨.effectGroupSchema _, _⟩ => none

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
  effects : List CarrierEffect

structure Funktion where
  name : Identifier
  adresse : Nat
  parameter : List (Ty .value)
  result : Option (Ty .value)
  konstanten : Nat
  misstAbstieg : Bool
  ruft : List Rufstelle
  effects : List CarrierEffect

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

def Rufstelle.passt (call : Rufstelle) (funktionen : List Funktion) : Bool :=
  match Funktion.finde funktionen call.name with
  | none => false
  | some target =>
    call.args.length == target.parameter.length &&
      (call.args.zip target.parameter).all (fun pair => tyFits pair.1 pair.2) &&
      target.effects.all (fun effect => decide (effect ∈ call.effects)) &&
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


end Gabbro.Core.Ast.Semantik
