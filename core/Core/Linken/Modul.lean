module

public import Core.Ast.Semantik.Runtime.ExpressionCode
public import Core.Katalog.Ziel

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Katalog

/-- A linked module: its name, its source fragment, the names it exports and the names it imports.
    The full source of every module is present; nothing is hidden. -/
structure Modul where
  name : String
  fragment : Fragment
  exporte : List String
  importe : List String

/-- A declarative build file: the modules, the dependency edges, the target platform and the entry. -/
structure Bauplan where
  module : List Modul
  abhaengigkeiten : List (String × String)
  plattform : Plattform
  einstieg : String

/-- The module names of the plan. -/
def modulNamen (plan : Bauplan) : List String :=
  plan.module.map Modul.name

/-- All exported names of the plan. -/
def alleExporte (plan : Bauplan) : List String :=
  plan.module.flatMap Modul.exporte

/-- Module names are unique. -/
def modulNamenEindeutig (plan : Bauplan) : Bool :=
  (modulNamen plan).eraseDups.length == (modulNamen plan).length

/-- Exported names are unique across the whole plan. -/
def exporteEindeutig (plan : Bauplan) : Bool :=
  (alleExporte plan).eraseDups.length == (alleExporte plan).length

/-- The entry names a module of the plan. -/
def einstiegVorhanden (plan : Bauplan) : Bool :=
  (modulNamen plan).contains plan.einstieg

/-- Every import is exported by some module of the plan. -/
def importeGedeckt (plan : Bauplan) : Bool :=
  plan.module.all fun mod => mod.importe.all fun imp => (alleExporte plan).contains imp

/-- Every dependency edge names two modules of the plan. -/
def abhaengigkeitenOk (plan : Bauplan) : Bool :=
  plan.abhaengigkeiten.all fun p => (modulNamen plan).contains p.1 && (modulNamen plan).contains p.2

/-- A function signature named for linking: name with parameter and result types.
    A definition and a call share the shape; a call fits a definition when the
    arity matches, every argument fits its parameter and the binding fits the result. -/
structure Signatur where
  name : Identifier
  params : List (Ty .value)
  result : Option (Ty .value)

/-- All function definitions of a fragment: name with parameter and result types. -/
def definitionen (frag : Fragment) : List Signatur :=
  frag.code.filterMap fun
    | .definiere name params result _ _ _ _ _ => some ⟨name, params, result⟩
    | _ => none

/-- All function calls of a fragment: name with argument and binding types. -/
def aufrufe (frag : Fragment) : List Signatur :=
  frag.code.filterMap fun
    | .rufe name args bind => some ⟨name, args, bind⟩
    | _ => none

/-- All entry targets of a fragment. -/
def starteZiele (frag : Fragment) : List Identifier :=
  frag.code.filterMap fun
    | .starte name => some name
    | _ => none

/-- A call fits a definition: same arity, every argument fits its parameter (`tyFits`),
    and the binding fits the result, mirroring `Rahmen.ruf`. No binding always fits. -/
def signaturPasst (args : List (Ty .value)) (bind : Option (Ty .value))
    (params : List (Ty .value)) (result : Option (Ty .value)) : Bool :=
  args.length == params.length &&
    (args.zip params).all (fun p => tyFits p.1 p.2) &&
    match bind, result with
    | none, _ => true
    | some geschrieben, some deklariert => tyFits deklariert geschrieben
    | some _, none => false

/-- Every defined function of the plan, in plan order. -/
def alleDefinitionen (plan : Bauplan) : List Signatur :=
  plan.module.flatMap fun m => definitionen m.fragment

/-- Defined function names are unique across the whole plan: a duplicate definition
    would silently shadow at `Funktion.finde` and halt `starte` on a broken `Nodup`. -/
def definitionenEindeutig (plan : Bauplan) : Bool :=
  let namen := (alleDefinitionen plan).map fun d => d.name.val
  namen.eraseDups.length == namen.length

/-- Every call of every module resolves to a definition of the plan with a fitting
    signature, and every entry target is defined. A dangling or mistyped call halts
    at `Rahmen.ruf`, so the linker refuses it here. -/
def aufrufeGedeckt (plan : Bauplan) : Bool :=
  let defs := alleDefinitionen plan
  let gedeckt (name : Identifier) (args : List (Ty .value)) (bind : Option (Ty .value)) : Bool :=
    defs.any fun d => (d.name.val == name.val) && signaturPasst args bind d.params d.result
  plan.module.all fun m =>
    ((aufrufe m.fragment).all fun c => gedeckt c.name c.params c.result) &&
      ((starteZiele m.fragment).all fun z => defs.any fun d => d.name.val == z.val)

/-- Every exported name is defined by some module of the plan: the interface is honest.
    Only function exports are covered; type and table exports extend this check. -/
def exporteDefiniert (plan : Bauplan) : Bool :=
  let definiert := (alleDefinitionen plan).map fun d => d.name.val
  plan.module.all fun m => m.exporte.all fun s => definiert.contains s.toList

/-- A fragment carries no written clauses. -/
def klauselnLeer (frag : Fragment) : Bool :=
  frag.klauseln.voraus.isEmpty && frag.klauseln.sicher.isEmpty && frag.klauseln.invariant.isEmpty

/-- Every static control target of an instruction at module-relative `pos` in a module
    of length `len` stays strictly inside the module. Instruction-relative jumps keep
    their meaning only there; past the boundary they would carry temporary state into
    another module's guard. `zurueckSprung` uses saturating subtraction, so the check
    also rules out wrap-around to the start. -/
def sprungZielInnen (pos len : Nat) : Befehl → Bool
  | .springe abstand => pos + abstand < len
  | .springeWenn _ _ abstand => pos + abstand < len
  | .zurueckSprung abstand => abstand ≤ pos
  | .definiere _ _ _ _ ueberspringe _ _ _ => pos + ueberspringe < len
  | .whileTest _ ausgang _ => pos + ausgang < len
  | .forAnfang _ _ _ skipEmpty _ _ => pos + skipEmpty < len
  | .forTest ausgang _ => pos + ausgang < len
  | .forNaechster zurueck _ => zurueck ≤ pos
  | .waehleVariante _ _ _ _ zweige => zweige.all fun z => pos + z.1 < len
  | .setzePasszahl _ stelle => pos + stelle < len
  | _ => true

/-- Instructions that never fall through to the next instruction with a live context:
    `ende` stops, `rueckVoid` and `zurueck` leave through the call stack or stop the
    context, and the static jumps move away. Combined with `sprungZielInnen` the last
    two only stay inside their own module. -/
def istAbschluss : Befehl → Bool
  | .ende => true
  | .rueckVoid => true
  | .zurueck _ _ => true
  | .springe _ => true
  | .zurueckSprung _ => true
  | _ => false

/-- A module is sealed when every static control target stays inside its own code;
    unless it is the last module, its last instruction must not fall through.
    Calls (`rufe`, `starte`) stay dynamic and keep the shared function mechanism:
    they clear temporaries on entry and restore them on return. -/
def modulAbgeschottet (m : Modul) (letzter : Bool) : Bool :=
  let code := m.fragment.code
  let len := code.length
  let spruenge := (List.range len).all fun pos =>
    match code[pos]? with
    | some b => sprungZielInnen pos len b
    | none => true
  spruenge &&
    (letzter ||
      match code.getLast? with
      | some b => istAbschluss b
      | none => true)

/-- Control-flow seal over the whole plan: every module keeps its static control flow
    inside its own code, and only the last module may fall through past the end of
    the linked code. Entries are relocated by concatenation and start with fresh
    temporaries; the seal carries no condition for them. -/
def kontrollflussAbgeschottet (plan : Bauplan) : Bool :=
  match plan.module with
  | [] => true
  | mods =>
    let letzter := mods.length - 1
    (List.range mods.length).all fun i =>
      match mods[i]? with
      | some m => modulAbgeschottet m (i == letzter)
      | none => true

/-- The modules' assumptions fit together: no module carries written clauses.
    A clause of one module would have to hold during every other module's code;
    linking clause-carrying modules needs the clause language (MK-19). No syntax
    produces clauses today, so nothing elaborated is refused. -/
def annahmenKompatibel (plan : Bauplan) : Bool :=
  plan.module.all fun m => klauselnLeer m.fragment

/-- The declarative link check: names unique, imports resolved, entry and edges valid,
    defined functions unique, every call resolved with a fitting signature, every export
    defined, no module carries written clauses, and control flow is sealed: no
    fall-through out of a non-final module, every static jump target inside its own
    module. -/
def bauplanOk (plan : Bauplan) : Bool :=
  modulNamenEindeutig plan && exporteEindeutig plan && einstiegVorhanden plan &&
    importeGedeckt plan && abhaengigkeitenOk plan &&
    definitionenEindeutig plan && aufrufeGedeckt plan && exporteDefiniert plan &&
    annahmenKompatibel plan && kontrollflussAbgeschottet plan

/-- Concatenation of all fragments in plan order. -/
def verknuepfteFragmente (plan : Bauplan) : Fragment :=
  plan.module.foldl (fun acc m => acc.anhaengen m.fragment) Fragment.leer

/-- Linking: resolve imports, append fragments, keep names unique. Returns `none` when the
    declarative check fails; the linked whole program is then checked as one unit. -/
def linke (plan : Bauplan) : Option Fragment :=
  if bauplanOk plan then some (verknuepfteFragmente plan) else none

end Gabbro.Core.Linken
