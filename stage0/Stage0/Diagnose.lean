/- Context for a refused compilation: every item the export gate refuses and every function
   whose elaboration to G fails, by name. The driver prints it after the compiler's own
   diagnostic; nothing here decides acceptance, so it is off the proof path. -/
module
public import Stage0.IRBild
@[expose] public section

namespace Gabbro.Stage0.Diagnose
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- The notes for one source text under the given options. -/
def notes (text : String) (options : Profil.Options := {}) : List String := Id.run do
  let tokens ← match lex text with
    | .error _ => return []
    | .ok tokens => pure tokens
  let items ← match parseTopTief tokens with
    | .error _ => return []
    | .ok items => pure items
  let prepared ← match Profil.prepareItems options items with
    | .error _ => return []
    | .ok prepared => pure prepared
  let declarations := pre108 prepared.elaborierbar
  let members := uMembers declarations
  let refused := ((Konst.ohneKonst members).filter ExportMetadata.itemMetadata).map
    ExportMetadata.metadataReason
  let gate := refused.eraseDups.map fun reason => "export gate refuses: " ++ reason
  let derived ← match Frontend.elaborateConstantScopes members with
    | .error _ => return gate
    | .ok derived => pure derived
  let unit ← match (Frontend.elabWithScopes declarations derived.scope.values derived.scope.types
      derived.scope.functions (Frontend.tableWithEmpty derived.scope.values derived.scope.types)).bind
        (Profil.selectUnit options) with
    | .error _ =>
      -- The same elaboration once more, asked for the place: the function an error arose in.
      let place := match expandU declarations with
        | .error _ => []
        | .ok (expanded, requirements) =>
          match elabExpandedWithScopes (expanded.map OldSource.normalizeItem) derived.scope.values
              derived.scope.types derived.scope.functions
              (Frontend.tableWithEmpty derived.scope.values derived.scope.types) requirements (ort := true) with
          | .error reason => ["elaboration: " ++ reason]
          | .ok _ => []
      return gate ++ place
    | .ok unit => pure unit
  let functions := (List.finRange unit.fns.length).filterMap fun f =>
    match lowerFnAt unit f with
    | .ok _ => none
    | .error reason => some ("function " ++ (fnAt unit f).name ++ ": " ++ reason)
  return gate ++ functions

end Gabbro.Stage0.Diagnose
