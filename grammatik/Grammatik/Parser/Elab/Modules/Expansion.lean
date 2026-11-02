module
public import Grammatik.Parser.Elab.Modules.Shape
@[expose] public section
namespace Gabbro.Grammatik.Parser.Modules
open Generic Aufloesung
open Namensraum (Pfad Quelle aufloeseK)

structure Expansion where
  items : List SItemTief
  literals : List (FnSig × SAnw) := []
  requirements : List (STyp × String) := []

structure Work where
  locations : List Located := []
  occupied : List Pfad := []
  literals : List (FnSig × SAnw) := []
  requirements : List (STyp × String) := []
  remaining : Nat

abbrev ExpandM := StateT Work (Except String)

def fail {α : Type} (message : String) : ExpandM α := fun _ => .error message

def lift {α : Type} (result : Except String α) : ExpandM α :=
  fun work => do pure (← result, work)

/-- Predeclare every ordinary sibling before evaluating uses, including forward function arguments. -/
mutual
def locateItem (position : Located) : SItemTief → List Located
  | .modT name body => locateList { position with
      origin := position.origin ++ segmente name,
      destination := position.destination ++ segmente name, exported := false } body
  | .pubT item => locateItem { position with exported := position.exportMembers } item
  | .moduleTemplateT .. | .moduleUseT .. | .useT .. => []
  | item => [{ position with item }]
def locateList (position : Located) : List SItemTief → List Located
  | [] => []
  | item :: rest => locateItem position item ++ locateList position rest
end

/-- Lookup module templates lexically, with the ordinary source import rule. -/
def template (all : List Template) (base : Quelle) (scope path : Pfad) : Except String Template := do
  let q : Quelle := ⟨all.map Template.path, base.verwendet⟩
  let target ← match aufloeseK q ⟨none, []⟩ scope path with
    | some target => pure target
    | none => throw ("parametric-module-unknown: " ++ String.intercalate "::" path)
  match all.filter (fun entry => entry.path == target) with
  | [entry] => pure entry
  | _ => throw ("parametric-module-duplicate: " ++ String.intercalate "::" target)

/-- Resolve declarations already in the work list for the shared argument checker. Pending
    applications stay pending, so module instantiation never runs generic-function expansion. -/
def argumentEnvironment (base : Quelle) (work : Work) : Except String Environment := do
  let initial := Generic.environment []
  let items ← work.locations.mapM (resolve initial base work.locations)
  pure (Generic.environment (Uebersetze.uMembers items))

mutual
/-- Every written use is visited, including unused instances. Recursion is checked by template
    identity (not its arguments); no recursive functor application is treated as sharing storage. -/
def visitItem (all : List Template) (base : Quelle) (ancestors : List Pfad)
    (position : Located) : Nat → SItemTief → ExpandM Unit
  | 0, _ => fail "parametric-module-limit: unbounded module expansion"
  | fuel + 1, .modT name body => visitList all base ancestors { position with
      origin := position.origin ++ segmente name,
      destination := position.destination ++ segmente name, exported := false } fuel body
  | fuel + 1, .pubT item => visitItem all base ancestors
      { position with exported := position.exportMembers } fuel item
  | _, .moduleTemplateT .. => pure ()
  | fuel + 1, .moduleUseT alias path arguments => do
    let entry ← lift (template all { base with verwendet := base.verwendet ++ position.imports }
      position.origin path)
    if ancestors.contains entry.path then
      fail ("parametric-module-recursion: " ++ String.intercalate "::" entry.path)
    let destination := position.destination ++ [alias]
    let work ← get
    if work.occupied.contains destination then
      fail ("parametric-module-alias-collision: " ++ String.intercalate "::" destination)
    if work.remaining == 0 then fail "parametric-module-limit: instance budget exhausted"
    let env ← lift (argumentEnvironment base work)
    let k := context base work.locations position
    let arguments ← lift (arguments.mapM fun word =>
      argument env position.bindings (genericArgument k word))
    let captured := match position.copy with
      | some (origin, _) => if origin.isPrefixOf entry.path then
          { position.bindings with literals := [], requirements := [] } else {}
      | none => ({} : Bindings)
    let parameterContext := { k with von := entry.path }
    let params := (Aufloesung.sig parameterContext
      { art := "", name := "", params := [], res := none, fehler := none,
        klauseln := [], generics := entry.params }).generics
    let (_, bindings) ← lift (normalizeArguments env {} params arguments
      (underGenerics captured entry.params))
    let location : Located := { origin := entry.path, destination,
      copy := some (entry.path, destination), bindings,
      exportMembers := position.exported,
      imports := position.imports ++ (sammleL entry.path (ordinaryList entry.body)).2,
      item := .useT [] }
    let declarations := locateList location entry.body
    modify fun state => { state with locations := state.locations ++ declarations,
      occupied := destination :: (occupiedList destination entry.body ++ state.occupied),
      remaining := state.remaining - 1,
      literals := state.literals ++ bindings.literals,
      requirements := state.requirements ++ bindings.requirements }
    visitList all base (entry.path :: ancestors) location fuel entry.body
  | _, .gateT _ => fail "parametric-module-selection: select build gates before instantiation"
  | _, _ => pure ()

def visitList (all : List Template) (base : Quelle) (ancestors : List Pfad)
    (position : Located) : Nat → List SItemTief → ExpandM Unit
  | _, [] => pure ()
  | 0, _ :: _ => fail "parametric-module-limit: unbounded module expansion"
  | fuel + 1, item :: rest => do
    visitItem all base ancestors position fuel item
    visitList all base ancestors position fuel rest
end

/-- The generic syntactic guarantee is checked on the same output sent to the exporter. -/
def ordinary (items : List SItemTief) : Bool := !syntaxList items

/-- Model A: flatten generative copies, resolve their hygienic names, then substitute. Every
    resulting declaration still passes the ordinary G elaborator and checker. No kernel rule or
    goal premise is changed. The size budget is a refusal gate, never a partial expansion. -/
def expandRaw (items : List SItemTief) : Except String Expansion := do
  if !syntaxList items then pure { items } else
    let all := templatesList [] items
    for entry in all do
      if (all.filter (fun other => other.path == entry.path)).length != 1 then
        throw ("parametric-module-duplicate: " ++ String.intercalate "::" entry.path)
    let plain := ordinaryList items
    let base := quelle plain
    let root : Located := { origin := [], destination := [], item := .useT [] }
    let locations := locateList root items
    let (_, work) ← (visitList all base [] root (sizeOf items + 1) items).run
      { locations, occupied := occupiedList [] items, remaining := sizeOf items + 1 }
    let env ← argumentEnvironment base work
    let target ← work.locations.mapM (resolve env base work.locations)
    let sourceNames := base.namen.map (schluessel base.namen)
    let mut names := sourceNames
    for (_, name) in instanceKeys work.locations do
      if names.contains name then throw "parametric-module-name-collision: generated name is already declared"
      names := name :: names
    if !Oeffentlich.huelleZu target then throw "parametric-module-export: public signature names a private item"
    pure { items := target, literals := work.literals, requirements := work.requirements }

/-- Refuse any residual surface form at the actual frontend boundary. -/
def expandWithRequirements (items : List SItemTief) : Except String Expansion := do
  let result ← expandRaw items
  if ordinary result.items then pure result
  else throw "parametric-module-output: template or use remains"

def expand (items : List SItemTief) : Except String (List SItemTief) :=
  (expandWithRequirements items).map Expansion.items

/-- Successful expansion contains only existing item forms. This attaches to the actual
    instantiation entry point, rather than a separate unchecked emitter. -/
theorem expand_ordinary (items target : List SItemTief) (h : expand items = .ok target) :
    ordinary target = true := by
  cases hr : expandRaw items with
  | error error => simp [expand, expandWithRequirements, hr] at h
  | ok result =>
    cases ho : ordinary result.items with
    | false => simp [expand, expandWithRequirements, hr, ho] at h
    | true =>
      simp [expand, expandWithRequirements, hr, ho] at h
      cases h
      exact ho

end Gabbro.Grammatik.Parser.Modules
