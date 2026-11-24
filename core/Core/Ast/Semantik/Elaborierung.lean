module

public import Core.Ast.Grammar
public import Core.Ast.Semantik.Runtime.ExpressionCode

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

def callInstruction (call : DirectCall scope) (bind : Option (Ty .value)) : Befehl :=
  .rufe call.name (call.args.map Sigma.fst) bind

def optionInstruction (slot : Nat) (value : OptionInitializer scope count) : Befehl :=
  let tag : Fin (indexOptionPayloads count).length :=
    match value with
    | .absent => ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩
    | .present .. => ⟨0, Nat.zero_lt_succ _⟩
  .baueVariante slot [] indexOptionLabels (indexOptionPayloads count) tag

def optionOperand (slot : Nat) : OptionInitializer scope count → Fragment
  | .absent => .leer
  | .present value _ => expr slot value

def optionCode (slot : Nat) (value : OptionInitializer scope count) : Fragment :=
  (optionOperand slot value).anhaengen (.einzel (optionInstruction slot value))

def callCode (call : DirectCall scope) (bind : Option (Ty .value)) : Fragment :=
  (argsCode 0 call.args).anhaengen (.einzel (callInstruction call bind))

def whileInstruction (condition : Expr scope .bool) (body : Fragment) (handler : Identifier) :
    Befehl := .whileTest 0 (body.code.length + 2) handler

def forInstruction (body : Fragment) (handler : Option Identifier) : Befehl :=
  .forTest (body.code.length + 2) handler

def BracedBlock.freigabe : BracedBlock result before → Nat
  | @BracedBlock.braces _ _ after _ => after.length - before.length

mutual
/-- Record whether the range index is shadowed or written in its body. -/
def Stmt.rangeUses (index : Identifier) : Stmt result before after → Bool × Bool
  | .letValue name _ _ | .letMutable name _ _ _ _ _ | .bindDirect name _ _ _ _
  | .letOption _ name _ _ _ _ =>
    (name.val == index.val, false)
  | .assignVar ref _ _ _ _ => (false, ref.binding.name.val == index.val)
  | .letMutableValue name _ _ => (name.val == index.val, false)
  | .tupleBind pattern _ _ _ =>
    ((pattern.names.filterMap id).any (fun name => name.val == index.val), false)
  | .ite _ yes no =>
    let (ys, yw) := BracedBlock.rangeUses index yes
    let (ns, nw) := BracedBlock.rangeUses index no
    (ys || ns, yw || nw)
  | .variantMatch _ arms => VariantArms.rangeUses index arms
  | .whileBounded _ _ _ _ _ body => BracedBlock.rangeUses index body
  | .forRange name _ _ _ _ _ body =>
    let (shadow, writes) := BracedBlock.rangeUses index body
    (name.val == index.val || shadow, writes)
  | _ => (false, false)

def Block.rangeUses (index : Identifier) : Block result before after → Bool × Bool
  | .done => (false, false)
  | .step first rest =>
    let (fs, fw) := Stmt.rangeUses index first
    let (rs, rw) := Block.rangeUses index rest
    (fs || rs, fw || rw)

def BracedBlock.rangeUses (index : Identifier) : BracedBlock result before → Bool × Bool
  | .braces body => Block.rangeUses index body
def VariantArms.rangeUses (index : Identifier) : VariantArms result scope allowed labels payloads → Bool × Bool
  | .done => (false, false)
  | .nullary _ _ body rest =>
    let a := BracedBlock.rangeUses index body
    let b := VariantArms.rangeUses index rest
    (a.1 || b.1, a.2 || b.2)
  | .payload _ binder _ body rest =>
    let a := BracedBlock.rangeUses index body
    let b := VariantArms.rangeUses index rest
    (a.1 || b.1 || binder.val == index.val, a.2 || b.2)
  | .wildcard body _ _ => BracedBlock.rangeUses index body
end

structure MatchCode where
  body : Fragment
  branches : List (Nat × Bool)

def MatchCode.prepend (rest : MatchCode) (arm : Fragment) (bind : Bool) : MatchCode :=
  let effective := if bind then arm.anhaengen (.einzel (.blockEnde 1)) else arm
  let length := effective.code.length + 1
  let branch := effective.anhaengen (.einzel (.springe (rest.body.code.length + 1)))
  ⟨branch.anhaengen rest.body, (1, bind) :: rest.branches.map (fun (offset, payload) => (length + offset, payload))⟩

mutual

def stmt : Stmt result before after → Fragment
  | .letValue name _ value => (expr 0 value).anhaengen (.einzel (.binden name 0))
  | .assignVar ref _ _ value _ =>
    (expr 0 value).anhaengen (.einzel (.zuweisen 0 ref.index ref.binding.type))
  | @Stmt.ret _ expected _ _ _ value _ =>
    (expr 0 value).anhaengen (.einzel (.zurueck 0 expected))
  | .ite condition yes no =>
    let yesCode := bracedBlock yes
    let noCode := bracedBlock no
    let head := (expr 0 condition).anhaengen (.einzel (.springeWenn 0 false (yesCode.code.length + 2)))
    ((head.anhaengen yesCode).anhaengen (.einzel (.springe (noCode.code.length + 1)))).anhaengen noCode

  | .retVoid _ => .einzel .rueckVoid
  | .letMutable _ _ written _ value _ =>
    (expr 0 value).anhaengen (.einzel (.bindeWert 0 written.type false))
  | .directCall call => callCode call none
  | .bindDirect _ _ written _ call => callCode call (some written.type)
  | .whileBounded condition bound _ _ handler body =>
    let test := expr 0 condition
    let body := bracedBlock body
    let set := Fragment.einzel (.setzePasszahl 0 (test.code.length + 1))
    let branch := Fragment.einzel (whileInstruction condition body handler)
    let again := Fragment.einzel (.zurueckSprung (test.code.length + body.code.length + 1))
    (((((expr 0 bound).anhaengen set).anhaengen test).anhaengen branch).anhaengen body).anhaengen again
  | @Stmt.forRange _ scope low _ _ high name _ lo hi _ overflow body =>
    let index := (rangeBinding name low high).type
    let (shadow, writes) := BracedBlock.rangeUses name body
    let body := bracedBlock body
    let endpoints := (expr 0 lo).anhaengen (expr 1 hi)
    let setup := Fragment.einzel (.forAnfang 0 1 index (body.code.length + 4) shadow (writes && overflow.isNone))
    let branch := Fragment.einzel (forInstruction body overflow)
    let again := Fragment.einzel (.forNaechster (body.code.length + 1) index)
    (((((endpoints.anhaengen setup).anhaengen branch).anhaengen body).anhaengen again).anhaengen
      (.einzel (.blockEnde 1)))

  | .tupleBind (first := first) (second := second) (types := tail) pattern _ _ value =>
    (expr 0 value).anhaengen (.einzel (.bindeTupel 0
      (first :: second :: tail) (pattern.names.map Option.isSome)))
  | .assignField (name := name) (labels := labels) (types := types) ref _ _ _ index _ value _ =>
    (expr 0 value).anhaengen (.einzel (.setzeRecordFeld 0 ref.index name labels types index))
  | .letMutableValue (type := type) _ _ value =>
    (expr 0 value).anhaengen (.einzel (.bindeWert 0 type false))
  | .variantMatch (name := name) (labels := labels) (payloads := payloads) value arms =>
    let matchCode := variantArms arms
    ((expr 0 value).anhaengen (.einzel (.waehleVariante 0 name labels payloads matchCode.branches))).anhaengen
      matchCode.body
  | .letOption (count := count) _ _ _ _ _ value =>
    (optionCode 0 value).anhaengen (.einzel (.bindeWert 0 (indexOptionType count) false))
  | .retOption (count := count) _ value =>
    (optionCode 0 value).anhaengen (.einzel (.zurueck 0 (indexOptionType count)))

def block : Block result before after → Fragment
  | .done => .leer
  | .step first rest => (stmt first).anhaengen (block rest)

def bracedBlock : BracedBlock result before → Fragment
  | @BracedBlock.braces _ _ after body =>
    (block body).anhaengen (.einzel (.blockEnde (after.length - before.length)))

def variantArms : VariantArms result scope allowed labels payloads → MatchCode
  | .done => ⟨.leer, []⟩
  | .nullary _ _ body rest => (variantArms rest).prepend (bracedBlock body) false
  | .payload _ _ _ body rest => (variantArms rest).prepend (bracedBlock body) true
  | .wildcard (labels := labels) body _ _ => ⟨bracedBlock body, List.replicate labels.length (1, false)⟩

end

def functionCode (result : Option WrittenType) (measure : Option (Measure scope))
    (body : BracedBlock (writtenResult result) scope) : Fragment :=
  let prologue := match measure with
    | none => Fragment.leer
    | some m => (expr 0 m.expression).anhaengen (.einzel (.pruefeMass 0))
  (prologue.anhaengen (bracedBlock body)).anhaengen (.einzel .rueckVoid)

def functionInstruction (before : Scope) (name : Identifier) (parameters : List (Parameter before))
    (result : Option WrittenType) (hasMeasure : Bool) (body : Fragment)
    (effects : Option (List CarrierEffect)) : Befehl :=
  .definiere name (parameters.map (fun p => p.written.type)) (writtenResult result)
    before.length (body.code.length + 1) hasMeasure
    (body.code.filterMap fun
      | .rufe target args bind => some ⟨target, args, bind, effects⟩
      | _ => none) effects

def tableInstruction (item : TableDeclaration before) : Befehl :=
  .definiereTraeger item.count ((recordLabels item.fields).map Subtype.val)
    (tupleType (recordTypes item.fields)) item.exported

def decl : Decl before after → Fragment
  | .constant _ _ written _ value _ _ =>
    (expr 0 value).anhaengen (.einzel (.bindeWert 0 written.type true))
  | .function name _ parameters result _ measure body _ _ effects =>
    let code := functionCode result measure body
    (Fragment.einzel (functionInstruction before name parameters result measure.isSome code
      (declaredEffects effects))).anhaengen code

  | .record _ name members _ _ =>
    .einzel (.definiereRecord name.val (recordLabels members) (recordTypes members))
  | .tagged _ name first tail _ _ =>
    let cases := first :: tail
    .einzel (.definiereVariante name.val (variantLabels cases) (variantPayloads cases))
  | .table item => .einzel (tableInstruction item)
  | .effectGroup item => .einzel (.definiereEffektgruppe item.resolved)
  | .environment name abi row => .einzel (.waehleUmgebung name abi row)

def unitBody : UnitBody before after → Fragment
  | .done => .leer
  | .step first rest => (decl first).anhaengen (unitBody rest)

-- Mirror returnName for the ordinary Stage-0 profile entry.
def mainName : Identifier := keywordName 'm' ['a', 'i', 'n'] (by decide) (by
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩)

theorem mainName_direct : directName mainName := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals first | (intro same; cases same; done) | skip
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  rintro (same | same | same | same | same | same | same | same) <;> cases same

def programm (tree : Ast.Unit) : Fragment :=
  ((unitBody tree.2).anhaengen (.einzel (.starte mainName))).anhaengen (.einzel .ende)

def fragment : (category : Category) → category.Tree → Fragment
  | .expression scope, tree => { expr 0 tree.2 with eingang := scope }
  | .statement scope _, tree => { stmt tree.2 with eingang := scope }
  | .block scope _, tree => { bracedBlock tree with eingang := scope }
  | .unit, tree => programm tree
  | .declaration scope, tree => { decl tree.2 with eingang := scope }

abbrev Einheit := Maschine.Einheit PUnit PUnit Int PUnit Rahmen PUnit PUnit PUnit Befehl


def startdaten (scope : Scope) (kern : Option Nat) : Startdaten Int PUnit Rahmen PUnit :=
  ⟨fun _ => .start scope, fun c => if c = eintritt then .laeuft else .ruht,
    fun k => ⟨if some k = kern then some eintritt else none, .nutzer, (), fun _ => false,
      0, false, []⟩, ⟨fun _ => false, fun _ => 0⟩⟩

def einrichtung (scope : Scope) : Einrichtung PUnit PUnit Int PUnit Rahmen PUnit PUnit :=
  ⟨fun _ => 0, fun _ => (), fun _ => (), fun _ => 0, fun _ _ _ => False, fun _ _ => True,
    ⟨0, 0⟩, ⟨eintritt, 0, fun _ => startdaten scope (some 0), fun _ _ => 0⟩,
    fun _ => 0, fun _ _ _ => none⟩

/-- The model's entry slot. An image compiler and its byte-level proof are later milestones. -/
def bild : Bild := ⟨.elf, fun a => if a = 0 then some 0 else none, [0]⟩

def startmedium (_ : AussenStart) (_ : Nat) : UInt8 := 0

def laden (scope : Scope) (start : AussenStart) (image : Ladung) : Option Zustand :=
  if image.starts 0 = some 0 ∧ image.bytes 0 = some 0 then
    let d := startdaten scope (start.assignment 0)
    some (Maschine.Zustand.start d.lokal d.status d.kerne d.rechte (einrichtung scope).initial
      (.leer (startmedium start)))
  else none

/-- Guards are collected at the source head, including at a cut with no hardware opportunity. -/
def Fragment.tabellen (p : Fragment) : Quelltabellen Zustand :=
  ⟨p.klauseln, fun s op args => ∃ c b, kopf p.code s c = some b ∧
    b.guard (s.lokal c) = some ⟨op, args⟩⟩

/-- The current forms each take one concrete step at their linearisation point. State
    matching is equality at those points and the number of private steps is zero. -/
def Fragment.einheit (p : Fragment) (platform : Plattform) : Einheit where
  katalog := platform.katalog
  bild := bild
  einrichtung := einrichtung p.eingang
  system := system p.code
  startdaten := fun start => startdaten p.eingang (start.assignment 0)
  startmedium := startmedium
  laden := laden p.eingang
  lokalerBezug := Eq
  stotterLaenge := fun _ => 0
  quelltabellen := p.tabellen

def elaborieren (platform : Plattform) {category : Category} (tree : category.Tree) : Einheit :=
  (fragment category tree).einheit platform

/-- Platform selection binds the hardware catalogue without changing the source system or its guards. -/
theorem elaborieren_quellbedeutung (left right : Plattform) {category : Category}
    (tree : category.Tree) :
    (elaborieren left tree).system = (elaborieren right tree).system ∧
      (elaborieren left tree).quelltabellen = (elaborieren right tree).quelltabellen :=
  ⟨rfl, rfl⟩

def Fragment.environment (p : Fragment) : List (Identifier × DienstAbi × FirmwareZeile) :=
  p.code.filterMap fun
    | .waehleUmgebung name abi row => some (name, abi, row)
    | _ => none

def Fragment.environmentAllowed (p : Fragment) (k : Katalog) : Prop :=
  (p.environment.map (fun e => e.1.val)).Nodup ∧
    ∀ e ∈ p.environment, e.2.2.zugelassen k e.2.1

/-- Whole-unit elaboration checks catalogue availability and name uniqueness.
    An isolated declaration gets the same admission check as its occurrence in a unit. -/
def zugelassen (platform : Plattform) : (category : Category) → category.Tree → Prop
  | .unit, tree => (programm tree).environmentAllowed platform.katalog
  | .declaration _, tree => (decl tree.2).environmentAllowed platform.katalog
  | .expression _, _ | .statement .., _ | .block .., _ => True

def Elaboriert (platform : Plattform) {category : Category}
    (tree : category.Tree) (E : Einheit) : Prop :=
  E = elaborieren platform tree ∧ zugelassen platform category tree

theorem elab_korrekt (platform : Plattform) {category : Category} (tree : category.Tree)
    (allowed : zugelassen platform category tree) :
    Elaboriert platform tree (elaborieren platform tree) := ⟨rfl, allowed⟩

theorem elab_vollstaendig {category : Category} {tree : category.Tree}
    (meaning : Elaboriert platform tree E) : E = elaborieren platform tree := meaning.1

theorem Elaboriert.deterministisch {category : Category} {tree : category.Tree}
    (a : Elaboriert platform tree E) (b : Elaboriert platform tree F) : E = F :=
  a.1.trans b.1.symm

def Bezeichnet (platform : Plattform) (category : Category) : Text.RawText → Einheit → Prop :=
  Ast.Bezeichnet (@Elaboriert platform category)

theorem bezeichnet_deterministisch
    (a : Bezeichnet platform category text E) (b : Bezeichnet platform category text F) : E = F :=
  Ast.bezeichnet_deterministic (elaborates := @Elaboriert platform category)
    (fun left right => left.deterministisch right) a b

end Gabbro.Core.Ast.Semantik
