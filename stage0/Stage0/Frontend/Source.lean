import Stage0.Frontend.Correctness

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
  normalized : Normalization (uMembers (pre108 items)) members

/-- The actual whole-source frontend, producing a proof of provenance and normalization. -/
def source (text : String) : Except String (Source text) :=
  match hl : lex text with
  | .error _ => .error "lex"
  | .ok tokens =>
    match hp : parseTopTief tokens with
    | .error e => .error e
    | .ok items =>
      if hv : Oeffentlich.huelleZu items then
        let result := normalize (uMembers (pre108 items))
        .ok ⟨tokens, items, result.val, hl, hp, hv, result.property⟩
      else .error "public interface is not closed"

/-- Successful source compilation carries canonical lexer/parser provenance and the semantic
    derivation for every declaration rewrite; no emitter-success premise stands in for this proof. -/
theorem source_sound (text : String) (result : Source text) :
    lex text = .ok result.tokens ∧ parseTopTief result.tokens = .ok result.items ∧
    Oeffentlich.huelleZu result.items = true ∧
    Normalization (uMembers (pre108 result.items)) result.members :=
  ⟨result.lexed, result.parsed, result.visibility, result.normalized⟩

/-- A successful frontend uses exactly canonical name resolution and width normalization;
    visibility failures cannot be hidden by flattening the item list. -/
theorem source_names (text : String) (result : Source text) :
    pre108 result.items = normTopU32 (Aufloesung.loese result.items) := by
  simp only [pre108, result.visibility, ↓reduceIte]

end Gabbro.Stage0.Frontend
