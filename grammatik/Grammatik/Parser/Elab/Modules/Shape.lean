module
public import Grammatik.Parser.Elab.Modules.Substitution
@[expose] public section
namespace Gabbro.Grammatik.Parser.Modules
open Generic Aufloesung
open Namensraum (Pfad Quelle aufloeseK)

structure Template where
  path : Pfad
  params : List SGenericParam
  body : List SItemTief

/-- A declaration retains both its lexical origin and its generative destination. -/
structure Located where
  origin : Pfad
  destination : Pfad
  copy : Option (Pfad × Pfad) := none
  bindings : Bindings := {}
  imports : List (Pfad × Pfad) := []
  exported : Bool := false
  /-- A private use keeps its instance's member visibility inside the current unit. -/
  exportMembers : Bool := true
  item : SItemTief

mutual
def syntaxItem : SItemTief → Bool
  | .moduleTemplateT .. | .moduleUseT .. => true
  | .modT _ body => syntaxList body
  | .pubT item | .gateT item => syntaxItem item
  | _ => false
def syntaxList : List SItemTief → Bool
  | [] => false
  | item :: rest => syntaxItem item || syntaxList rest
end

mutual
/-- Templates are lexical declarations, including templates nested in other templates. -/
def templatesItem (scope : Pfad) : SItemTief → List Template
  | .moduleTemplateT name params body =>
    let path := scope ++ segmente name
    ⟨path, params, body⟩ :: templatesList path body
  | .modT name body => templatesList (scope ++ segmente name) body
  | .pubT item | .gateT item => templatesItem scope item
  | _ => []
def templatesList (scope : Pfad) : List SItemTief → List Template
  | [] => []
  | item :: rest => templatesItem scope item ++ templatesList scope rest
end

mutual
/-- Only ordinary declarations contribute to the original unit's namespace. -/
def ordinaryItem : SItemTief → List SItemTief
  | .moduleTemplateT .. | .moduleUseT .. => []
  | .modT name body => [.modT name (ordinaryList body)]
  | .pubT item => (ordinaryItem item).map SItemTief.pubT
  | item => [item]
def ordinaryList : List SItemTief → List SItemTief
  | [] => []
  | item :: rest => ordinaryItem item ++ ordinaryList rest
end

mutual
/-- Modules occupy names even when empty; an instance cannot silently merge into one. -/
def occupiedItem (scope : Pfad) : SItemTief → List Pfad
  | .modT name body =>
    let path := scope ++ segmente name
    path :: occupiedList path body
  | .moduleTemplateT name _ _ => [scope ++ segmente name]
  | .pubT item | .gateT item => occupiedItem scope item
  | .moduleUseT .. => []
  | item => ((itemName item).map (fun name => scope ++ [name])).toList
def occupiedList (scope : Pfad) : List SItemTief → List Pfad
  | [] => []
  | item :: rest => occupiedItem scope item ++ occupiedList scope rest
end

/-- Length encoding follows function instances, using identifier-safe delimiters because these
    names may occur in a later generic argument. Arguments deliberately do not identify a
    module instance: two aliases with equal arguments own different storage. -/
def memberName (path : Pfad) : String :=
  "__gabbro_module_" ++ String.join (path.map fun part =>
    toString part.length ++ "_" ++ part ++ "_")

def locatedPath (item : Located) : Option Pfad :=
  (itemName item.item).map (fun name => item.destination ++ [name])

/-- The source namespace plus virtual alias members; only their checked keys enter the output. -/
def source (base : Quelle) (items : List Located) : Quelle :=
  ⟨base.namen ++ items.filterMap locatedPath, base.verwendet⟩

def instanceKeys (items : List Located) : List (Pfad × String) :=
  items.filterMap fun item => do
    let _ ← item.copy
    let path ← locatedPath item
    pure (path, memberName path)

/-- Keep the original unit's canonical keys stable when virtual alias paths add short names. -/
def globalKeys (base : Quelle) (items : List Located) : List (Pfad × String) :=
  instanceKeys items ++ base.namen.map (fun path => (path, schluessel base.namen path))

/-- A copied declaration resolves in its definition's scope. Its local paths are rebound to the
    destination, while free global names retain the original unit's keys. Substitution runs later,
    so a type argument cannot be captured by a member with the same spelling. -/
def context (base : Quelle) (items : List Located) (location : Located) : Kontext :=
  let q := source base items
  let keys := globalKeys base items
  let (localNames, localKeys) := match location.copy with
    | none => ([], [])
    | some (origin, destination) =>
      let entries := (instanceKeys items).filterMap fun (path, key) =>
        if destination.isPrefixOf path then
          some (origin ++ path.drop destination.length, key)
        else none
      (entries.map Prod.fst, entries)
  { q := ⟨q.namen ++ localNames, q.verwendet ++ location.imports⟩, von := location.origin,
    lok := location.bindings.types.map Prod.fst ++ location.bindings.values.map Prod.fst ++
      location.bindings.functions.map Prod.fst,
    keys := localKeys ++ keys }

def resolve (env : Environment) (base : Quelle) (items : List Located)
    (location : Located) : Except String SItemTief := do
  let item := Aufloesung.item (context base items location) location.item
  let item ← match location.copy with
    | none => pure item
    | some _ => substitute env location.bindings item
  pure (if location.exported then .pubT item else item)

end Gabbro.Grammatik.Parser.Modules
