import Stage0.Frontend.Environments
import Stage0.Frontend.Guard

namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Source provenance and the complete declaration normalization derivation consumed by Stage0.
    Lexing/parsing are the canonical functions; pre108 retains its visibility and name checks. -/
structure Source (text : String) where
  tokens : List Token
  items : List SItemTief
  members : List SItemTief
  lexed : lex text = .ok tokens
  parsed : parseTopTief tokens = .ok items
  visibility : Oeffentlich.huelleZu items = true
  compileTime : compileTimeSafe (uMembers (pre108 items)) = true
  normalized : Normalization (uMembers (pre108 items)) members
  environments : EnvironmentFacts (uMembers (pre108 items)) members

/-- The actual whole-source frontend, producing a proof of provenance and normalization. -/
def source (text : String) : Except String (Source text) :=
  match hl : lex text with
  | .error _ => .error "lex"
  | .ok tokens =>
    match hp : parseTopTief tokens with
    | .error e => .error e
    | .ok items =>
      if hv : Oeffentlich.huelleZu items then
        if hc : compileTimeSafe (uMembers (pre108 items)) then
          let result := normalize (uMembers (pre108 items))
          if he : EnvironmentCompatible (uMembers (pre108 items)) result.val then
            .ok ⟨tokens, items, result.val, hl, hp, hv, hc, result.property,
              normalize_environments _ he⟩
          else .error "compile-time constant or alias environment cannot be preserved by canonical elaboration"
        else .error "compile-time call requires unsupported function contracts, effects or body"
      else .error "public interface is not closed"

/-- Successful frontend extraction carries canonical lexer/parser provenance, the original
    compile-time call guard and local declaration rewrite facts. Whole-program denotational
    preservation is a separate obligation, not implied by projecting this certificate. -/
theorem source_sound (text : String) (result : Source text) :
    lex text = .ok result.tokens ∧ parseTopTief result.tokens = .ok result.items ∧
    Oeffentlich.huelleZu result.items = true ∧
    compileTimeSafe (uMembers (pre108 result.items)) = true ∧
    Normalization (uMembers (pre108 result.items)) result.members ∧
    EnvironmentFacts (uMembers (pre108 result.items)) result.members :=
  ⟨result.lexed, result.parsed, result.visibility, result.compileTime, result.normalized, result.environments⟩

/-- A successful frontend uses exactly canonical name resolution and width normalization;
    visibility failures cannot be hidden by flattening the item list. -/
theorem source_names (text : String) (result : Source text) :
    pre108 result.items = normTopU32 (Aufloesung.loese result.items) := by
  simp only [pre108, result.visibility, ↓reduceIte]

/-- A scalar compile-time call from the original source has a complete safe call-hull derivation
    before normalization, so a later baseline evaluator is never the first contract check. -/
theorem source_constant_hull (text : String) (result : Source text)
    (name : String) (ty : STyp) (expr : SExpr)
    (hm : SItemTief.constT name ty (.one expr) ∈ uMembers (pre108 result.items))
    (callee : String) (hc : callee ∈ calls expr) :
    SafeHull (uMembers (pre108 result.items)) [] callee := by
  have h := compileTimeSafe_constants result.compileTime hm
  exact safeConstantName_sound _ _ _ _ ((List.all_eq_true.mp h) callee hc)

end Gabbro.Stage0.Frontend
