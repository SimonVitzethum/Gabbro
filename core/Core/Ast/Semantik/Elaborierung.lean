module

public import Core.Ast.Grammar
public import Core.Ast.Semantik.Runtime.ExpressionCode
public import Core.Ast.LowLevel.Admission
public import Core.Ast.Semantik.Runtime.Praedikat

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

/-- The memory order of the memory model that a written order names. -/
def _root_.Gabbro.Core.Ast.AccessMode.modus : AccessMode → Gabbro.Core.Speicher.Modus
  | .na => .na
  | .rlx => .rlx
  | .ra => .ra
  | .sc => .sc

/-- **The code of an access form**: the index (and the value) are evaluated into the temporaries `0` (and `1`), then ONE
    access instruction names the region by the position of its owner local, and a load binds the value it read. -/
def accessCode : Access before after → Fragment
  | .load _ _ written _ region _ _ index mode =>
    ((expr 0 index).anhaengen
      (.einzel (.zugriff (.lade 0 region.index 0 written.type mode.modus)))).anhaengen
      (.einzel (.bindeWert 0 written.type false))
  | .store region _ _ index value mode =>
    ((expr 0 index).anhaengen (expr 1 value)).anhaengen
      (.einzel (.zugriff (.speichere region.index 0 1 mode.modus)))
  | .swap _ _ written _ region _ _ index value mode =>
    ((((expr 0 index).anhaengen (expr 1 value)).anhaengen
      (.einzel (.zugriff (.tausche 0 region.index 0 1 written.type mode.modus)))).anhaengen
      (.einzel (.bindeWert 0 written.type false)))
  | .vergleicheTausche _ _ written _ region _ _ index expected neu mode =>
    (((((expr 0 index).anhaengen (expr 1 expected)).anhaengen (expr 2 neu)).anhaengen
      (.einzel (.zugriff (.vergleicheTausche 0 region.index 0 1 2 written.type mode.modus)))).anhaengen
      (.einzel (.bindeWert 0 written.type false)))
  | .holeUndAddiere _ _ written _ region _ _ index betrag mode =>
    ((((expr 0 index).anhaengen (expr 1 betrag)).anhaengen
      (.einzel (.zugriff (.holeUndAddiere 0 region.index 0 1 written.type mode.modus)))).anhaengen
      (.einzel (.bindeWert 0 written.type false)))
  | .erwarte _ _ written _ region _ _ index marker mode =>
    (((expr 0 index).anhaengen
      (.einzel (.zugriff (.erwarte 0 region.index 0 marker written.type mode.modus)))).anhaengen
      (.einzel (.bindeWert 0 written.type false)))

  | .veroeffentliche region _ _ index value mode =>
    ((expr 0 index).anhaengen (expr 1 value)).anhaengen
      (.einzel (.zugriff (.veroeffentliche region.index 0 1 mode.modus)))

mutual
/-- Record whether the range index is shadowed or written in its body. -/
def Stmt.rangeUses (index : Identifier) : Stmt result before after → Bool × Bool
  | .letValue name _ _ | .letMutable name _ _ _ _ _ | .bindDirect name _ _ _ _
  | .letOption _ name _ _ _ _ =>
    (name.val == index.val, false)
  | .assignVar ref _ _ _ _ => (false, ref.binding.name.val == index.val)
  | .letMutableValue name _ _ | .letRegion name _ _ _ _ _ => (name.val == index.val, false)
  | .tupleBind pattern _ _ _ =>
    ((pattern.names.filterMap id).any (fun name => name.val == index.val), false)
  | .ite _ yes no =>
    let (ys, yw) := BracedBlock.rangeUses index yes
    let (ns, nw) := BracedBlock.rangeUses index no
    (ys || ns, yw || nw)
  | .variantMatch _ arms => VariantArms.rangeUses index arms
  | .whileBounded _ _ _ _ _ body => BracedBlock.rangeUses index body
  | .forever _ body => BracedBlock.rangeUses index body
  | .access (.load name ..) => (name.val == index.val, false)
  | .access (.swap name ..) => (name.val == index.val, false)
  | .access (.vergleicheTausche name ..) => (name.val == index.val, false)
  | .access (.holeUndAddiere name ..) => (name.val == index.val, false)
  | .access (.erwarte name ..) => (name.val == index.val, false)
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
    let branch := Fragment.schleifentest (whileInstruction condition body handler)
      (SchleifenGrenze.whileBounded bound)
    let again := Fragment.einzel (.zurueckSprung (test.code.length + body.code.length + 1))
    (((((expr 0 bound).anhaengen set).anhaengen test).anhaengen branch).anhaengen body).anhaengen again
  | @Stmt.forRange _ scope low _ _ high name _ lo hi _ overflow body =>
    let index := (rangeBinding name low high).type
    let (shadow, writes) := BracedBlock.rangeUses name body
    let body := bracedBlock body
    let endpoints := (expr 0 lo).anhaengen (expr 1 hi)
    let setup := Fragment.einzel (.forAnfang 0 1 index (body.code.length + 4) shadow (writes && overflow.isNone))
    let branch := Fragment.schleifentest (forInstruction body overflow)
      (SchleifenGrenze.forRange lo hi)
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
  | .letRegion _ _ region _ _ init => .einzel (.bindeRegion region.index init)
  | .forever _ body =>
    let pass := bracedBlock body
    pass.anhaengen (.einzel (.zurueckSprung pass.code.length))
  | .access form => accessCode form

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
  rintro (same | same | same | same | same | same | same | same | same | same) <;> cases same

def programm (tree : Ast.Unit) : Fragment :=
  ((unitBody tree.2).anhaengen (.einzel (.starte mainName))).anhaengen (.einzel .ende)

/-- A source unit together with the invariants it declares. The observable state is the unit
    state `Zustand`; the declared invariants are expressions of the decidable predicate
    language (`Praedikat`), elaborated into denotations in the fragment's clause
    table. Surface syntax for the declarations is MK-19/3; until then units elaborate with
    the empty list. -/
structure UnitMitInvarianten where
  baum : Ast.Unit
  invarianten : List Praedikat

/-- Elaboration carries the declared invariants into the fragment's clause table. Code,
    entries and memory plan are those of `programm`; the clause table is exactly the
    denotations, so facts about it are `rfl` and need no induction over the unit body. -/
def programmMitInvarianten (u : UnitMitInvarianten) : Fragment :=
  { programm u.baum with klauseln := ⟨[], [], u.invarianten.map Praedikat.gilt⟩ }

theorem programmMitInvarianten_klauseln (u : UnitMitInvarianten) :
    (programmMitInvarianten u).klauseln.invariant = u.invarianten.map Praedikat.gilt :=
  rfl

def fragment : (category : Category) → category.Tree → Fragment
  | .expression scope, tree => { expr 0 tree.2 with eingang := scope }
  | .statement scope _, tree => { stmt tree.2 with eingang := scope }
  | .block scope _, tree => { bracedBlock tree with eingang := scope }
  | .unit, tree => programmMitInvarianten ⟨tree, []⟩
  | .declaration scope, tree => { decl tree.2 with eingang := scope }

/-- The whole checker for a fragment: the loader premise on the memory plan, the
    crash-recovery premise, and preservation per command. -/
def pruefeEinheit (p : Fragment) (ps : List Praedikat) : Bool :=
  pruefeStart p.speicher.initial ps && pruefeNeustart ps &&
    p.code.all (pruefeBefehlErhalt ps)

/-- A passing unit satisfies every declared predicate on its memory plan. -/
theorem pruefeEinheit_start (p : Fragment) (ps : List Praedikat)
    (ok : pruefeEinheit p ps = true) : ∀ q ∈ ps, q.haelt p.speicher.initial := by
  simp only [pruefeEinheit, Bool.and_eq_true] at ok
  obtain ⟨⟨hstart, _⟩, _⟩ := ok
  exact (pruefeStart_richtig _ _).mp hstart

/-- A passing unit satisfies every declared predicate after crash recovery. -/
theorem pruefeEinheit_neustart (p : Fragment) (ps : List Praedikat)
    (ok : pruefeEinheit p ps = true) : ∀ q ∈ ps, q.haelt (fun _ => 0) := by
  simp only [pruefeEinheit, Bool.and_eq_true] at ok
  obtain ⟨⟨_, hrestart⟩, _⟩ := ok
  exact (pruefeNeustart_richtig _).mp hrestart

/-- A passing unit preserves every declared predicate across each of its commands. -/
theorem pruefeEinheit_befehl (p : Fragment) (ps : List Praedikat) (b : Befehl)
    (hmem : b ∈ p.code) (ok : pruefeEinheit p ps = true) :
    pruefeBefehlErhalt ps b = true := by
  simp only [pruefeEinheit, Bool.and_eq_true] at ok
  obtain ⟨_, hcode⟩ := ok
  simp only [List.all_eq_true] at hcode
  exact hcode b hmem

/-- A fragment with an empty clause table denotes the empty predicate list. -/
theorem tabLeer (p : Fragment) (h : p.klauseln.invariant = []) :
    p.klauseln.invariant = [].map Praedikat.gilt := by
  simp only [h, List.map_nil]

/-- Plain units elaborate with the empty predicate list: the clause table is empty. -/
theorem fragment_unit_invarianten (tree : Ast.Unit) :
    (fragment .unit tree).klauseln.invariant = [].map Praedikat.gilt := rfl

/-- The checker accepts the empty predicate list on every fragment. -/
theorem pruefeEinheit_leer (p : Fragment) : pruefeEinheit p [] = true := by
  have h1 : pruefeStart p.speicher.initial [] = true := rfl
  have h2 : pruefeNeustart [] = true := rfl
  have h3 : p.code.all (pruefeBefehlErhalt []) = true :=
    List.all_eq_true.mpr (fun b _ => rfl)
  simp only [pruefeEinheit, Bool.and_eq_true]
  exact ⟨⟨h1, h2⟩, h3⟩

abbrev Einheit := Maschine.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit Befehl


/-- **Boot data of every context.** The entry context starts at the first instruction and owns the
    arrival regions; every other context rests, with its frame at the entry of its own body (the
    position `eintritte` gives, `0` if it has none). -/
def startdaten (scope : Scope) (eintritte : Kontext → Option Nat) (kern : Option Nat)
    (platform : Plattform := .x86_64) (regions : List Strecke := []) :
    Startdaten Int Nat Rahmen PUnit :=
  let bootFrame (c : Kontext) : Rahmen :=
    { Rahmen.start scope with
      platform := platform
      pc := if c = eintritt then 0 else (eintritte c).getD 0
      arrivalRegions := if c = eintritt then regions else [] }
  ⟨bootFrame,
    fun c => if c = eintritt then .laeuft else .ruht,
    fun k => ⟨if some k = kern then some eintritt else none, .nutzer, 0, fun _ => false,
      0, false, []⟩, ⟨fun i => decide (i < regions.length), fun _ => 0⟩⟩

/-- **The unit's interpretation of memory** from its memory plan: the declared initial cells, the
    lock words, the one event location, the region slot as the object of a cell, and the handle a
    context holds. -/
def einrichtung (scope : Scope) (eintritte : Kontext → Option Nat) (plan : Speicherplan) :
    Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit :=
  ⟨plan.initial, Zelle.sperre, fun _ => Zelle.aussen, fun _ => 0, fun _ _ _ => False, fun _ _ => True,
    ⟨0, 0⟩, ⟨eintritt, 0, fun _ => startdaten scope eintritte (some 0), fun _ _ => 0, id⟩,
    Zelle.objekt, Zustand.griff⟩

/-- The model's entry slot. An image compiler and its byte-level proof are later milestones. -/
def bild : Bild := ⟨.elf, fun a => if a = 0 then some 0 else none, [0]⟩

def startmedium (_ : AussenStart) (_ : Nat) : UInt8 := 0

def laden (scope : Scope) (eintritte : Kontext → Option Nat) (plan : Speicherplan)
    (platform : Plattform) (start : AussenStart) (image : Ladung) : Option Zustand :=
  if image.starts 0 = some 0 ∧ image.bytes 0 = some 0 then
    let d := startdaten scope eintritte (start.assignment 0) platform start.regions
    some (Maschine.Zustand.start d.lokal d.status d.kerne d.rechte (einrichtung scope eintritte plan).initial
      (.leer (startmedium start)))
  else none

/-- Guards are collected at the source head, including at a cut with no hardware opportunity. -/
def Fragment.tabellen (p : Fragment) : Quelltabellen Zustand :=
  ⟨p.klauseln, fun s op args => ∃ c b, kopf p.code s c = some b ∧
    b.guard (s.lokal c) = some ⟨op, args⟩⟩

/-- The current source fragment has no classified local-place declarations. Its frame
    and control are public, and no instruction declares an output or release journal. -/
def fragmentFlussdaten : Beobachtung.Flussdaten Befehl Rahmen Zelle Int :=
  { lokal := fun _ => .ganz ∅, kontrolle := fun _ => ∅ }

/-- The current forms each take one concrete step at their linearisation point. State
    matching is equality at those points and the number of private steps is zero. -/
def Fragment.einheit (p : Fragment) (platform : Plattform) : Einheit where
  katalog := platform.katalog
  bild := bild
  einrichtung := einrichtung p.eingang p.eintritte p.speicher
  system := system p.code
  startdaten := fun start => startdaten p.eingang p.eintritte (start.assignment 0) platform start.regions
  startmedium := startmedium
  laden := laden p.eingang p.eintritte p.speicher platform
  lokalerBezug := Eq
  stotterLaenge := fun _ => 0
  quelltabellen := p.tabellen
  fluss := fragmentFlussdaten

def elaborieren (platform : Plattform) {category : Category} (tree : category.Tree) : Einheit :=
  (fragment category tree).einheit platform

/-- A source unit with the invariants it declares denotes the elaborated unit of the fragment
    carrying the invariant denotations (`programmMitInvarianten`). -/
def elaborierenMitInvarianten (platform : Plattform) (u : UnitMitInvarianten) : Einheit :=
  (programmMitInvarianten u).einheit platform

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
  | category, tree =>
    let p := fragment category tree
    p.environmentAllowed platform.katalog ∧ p.code.all (Befehl.platformAllowed platform) = true

def Elaboriert (platform : Plattform) {category : Category}
    (tree : category.Tree) (E : Einheit) : Prop :=
  E = elaborieren platform tree

theorem elab_korrekt (platform : Plattform) {category : Category} (tree : category.Tree) :
    Elaboriert platform tree (elaborieren platform tree) := rfl

theorem elab_vollstaendig {category : Category} {tree : category.Tree}
    (meaning : Elaboriert platform tree E) : E = elaborieren platform tree := meaning

theorem Elaboriert.deterministisch {category : Category} {tree : category.Tree}
    (a : Elaboriert platform tree E) (b : Elaboriert platform tree F) : E = F :=
  a.trans b.symm

/-- The source denotes its elaborated unit only under the platform admission rules.
    Compositional elaboration can also describe intermediate fragments. -/
def ZugelassenElaboriert (platform : Plattform) {category : Category}
    (tree : category.Tree) (E : Einheit) : Prop :=
  Elaboriert platform tree E ∧ zugelassen platform category tree

def Bezeichnet (platform : Plattform) (category : Category) : Text.RawText → Einheit → Prop :=
  Ast.Bezeichnet (@ZugelassenElaboriert platform category)

theorem bezeichnet_deterministisch
    (a : Bezeichnet platform category text E) (b : Bezeichnet platform category text F) : E = F :=
  Ast.bezeichnet_deterministic (elaborates := @ZugelassenElaboriert platform category)
    (fun left right => left.1.deterministisch right.1) a b

end Gabbro.Core.Ast.Semantik
