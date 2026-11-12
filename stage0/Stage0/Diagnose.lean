/- Context for a refused compilation: every item the export gate refuses and every function
   whose elaboration to G fails, by name. The driver prints it after the compiler's own
   diagnostic; nothing here decides acceptance, so it is off the proof path. -/
module
public import Stage0.IRBild
@[expose] public section

namespace Gabbro.Stage0.Diagnose
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- What a statement is, in a few words, for a diagnosis. -/
def statementKind : SAnw → String
  | .bind _ x _ _ | .bindQ _ x _ _ | .bindElse x _ _ _ _ => "let " ++ x
  | .set .. => "assignment"
  | .call f _ | .callElse f _ _ _ | .callQ f _ => "call " ++ f
  | .cond .. => "if"
  | .cases .. => "match"
  | .each x .. => "traverse " ++ x
  | .retry .. => "retry"
  | .loop .. => "forever"
  | .locks .. => "locks"
  | .trim .. | .trimReq .. => "narrow"
  | .ret _ => "return"
  | .alloc _ x .. => "alloc " ++ x
  | _ => "statement"

/-- The first statement of a function body at which an elaboration error arises: the smallest number
    of leading statements whose elaboration already answers `reason`. Statements elaborate in order,
    so every longer prefix answers the same; the search halves the range. `none` when no prefix
    answers it (the error belongs to the closing `return`). -/
def firstFailing (attempt : List SAnw → Option String) (reason : String) (statements : List SAnw) :
    Option (Nat × SAnw) :=
  let fails := fun (k : Nat) => attempt (statements.take k) == some reason
  if !fails statements.length then none else
  let rec search (fuel lo hi : Nat) : Nat :=
    match fuel with
    | 0 => hi
    | fuel + 1 =>
      if hi ≤ lo + 1 then hi else
      let mid := (lo + hi) / 2
      if fails mid then search fuel lo mid else search fuel mid hi
  let k := search 64 0 statements.length
  (statements[k - 1]?).map fun s => (k, s)

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
        | .error _ =>
          -- The expansion refused: name the calls of functions the unit does not declare.
          match Gabbro.Grammatik.Parser.Modules.prepareDetailedRaw declarations with
          | .error _ => []
          | .ok result =>
            let known := Instantiation.functionNames result.items
            ((Instantiation.directReferences result.items).filter fun name => !known.contains name).eraseDups.map
              fun name => "call of an undeclared function: " ++ name
        | .ok (expanded, requirements) =>
          match elabExpandedWithScopes (expanded.map OldSource.normalizeItem) derived.scope.values
              derived.scope.types derived.scope.functions
              (Frontend.tableWithEmpty derived.scope.values derived.scope.types) requirements (ort := true) with
          | .error reason =>
            -- The statement: the shortest prefix of the function's body that answers the same error.
            let run := fun (items : List SItemTief) =>
              match elabExpandedWithScopes items derived.scope.values derived.scope.types
                  derived.scope.functions
                  (Frontend.tableWithEmpty derived.scope.values derived.scope.types) requirements (ort := true) with
              | .error e => some e
              | .ok _ => none
            let normal := expanded.map OldSource.normalizeItem
            let place := normal.findSome? fun
              | .fnT sig (.block statements _) =>
                if reason.startsWith ("function " ++ sig.name ++ ": ") then
                  (firstFailing (fun leading => run (normal.map fun
                      | .fnT other body => if other.name == sig.name then .fnT other (.block leading none) else .fnT other body
                      | item => item)) reason statements).map fun (k, s) =>
                    " (statement " ++ toString k ++ " of " ++ toString statements.length ++ ": " ++
                      statementKind s ++ ")"
                else none
              | _ => none
            ["elaboration: " ++ reason ++ place.getD ""]
          | .ok _ => []
      return gate ++ place
    | .ok unit => pure unit
  let functions := (List.finRange unit.fns.length).filterMap fun f =>
    match lowerFnAt unit f with
    | .ok _ => none
    | .error reason => some ("function " ++ (fnAt unit f).name ++ ": " ++ reason)
  return gate ++ functions

end Gabbro.Stage0.Diagnose
