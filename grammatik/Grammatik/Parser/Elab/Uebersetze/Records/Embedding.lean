module

public import Grammatik.Parser.Item.ElementTief.Defs1
public import Grammatik.Parser.Lex.Lexer

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Surface record members; embeddings disappear before type elaboration. -/
inductive SRecordMember where
  | field (value : SFeld)
  | embed (name : String)

/-- Read record members using the canonical field reader for ordinary fields. -/
def recordMembers : Nat → List Token → Except String (List SRecordMember × List Token)
  | 0, _ => .error "record embedding: parser fuel exhausted"
  | fuel + 1, tokens => do
    if let .zeichen "}" :: rest := tokens then return ([], rest)
    let (member, rest) ← match tokens with
      | .zeichen ".." :: rest => do
        let (name, tail) ← nimmName rest
        pure (.embed name, tail)
      | _ => do
        let (field, tail) ← parseFeld fuel tokens
        pure (.field field, tail)
    match rest with
    | .zeichen "," :: tail =>
      let (members, tail) ← recordMembers fuel tail
      pure (member :: members, tail)
    | .zeichen "}" :: tail => pure ([member], tail)
    | _ => throw "record embedding: comma or closing brace expected"

def recordSurface (text : String) : Except String (List SRecordMember) := do
  let tokens ← lex text
  let tokens ← fordereZeichen "{" tokens
  let (members, rest) ← recordMembers (tokens.length + 1) tokens
  if rest.all (fun | .ende => true | _ => false) then pure members
  else throw "record embedding: trailing tokens"

/-- Expand against the complete declaration list, retaining all field metadata. Fuel bounds
    dependency depth; revisiting a name gives a specific recursive-embedding refusal. -/
def expandRecord : Nat → List SItemTief → List String → String →
    Except String (List SFeld)
  | 0, _, _, _ => .error "record embedding: recursive embedding"
  | fuel + 1, items, active, name => do
    if active.contains name then throw "record embedding: recursive embedding"
    let some item := items.find? (fun item => match item with
      | .typeT _ candidate .. => candidate == name
      | _ => false) | throw "record embedding: non-record target"
    let .typeT _ _ _ _ (some (.raw text)) := item
      | throw "record embedding: non-record target"
    let members ← recordSurface text
    let embedded ← members.foldlM (fun fields member => do
      match member with
      | .field _ => pure fields
      | .embed target =>
        let more ← expandRecord fuel items (name :: active) target
        pure (fields ++ more)) []
    let fields := embedded ++ members.filterMap (fun
      | .field field => some field
      | .embed _ => none)
    if (fields.map (·.fname)).eraseDups.length != fields.length then
      throw "record embedding: duplicate field"
    pure fields

end Gabbro.Grammatik.Parser.Uebersetze
