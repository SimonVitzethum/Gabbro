module
public import Grammatik.Parser.Item.ElementTief.Kopf
@[expose] public section
namespace Gabbro.Grammatik.Parser

/-- A type parameter may carry a nonempty list of spec names. -/
def parseGenericBounds : Nat → List Token → Except String (List String × List Token)
  | 0, _ => .error "out of fuel"
  | fuel + 1, tokens => do
    let (name, rest) ← nimmName tokens
    match rest with
    | .zeichen "+" :: tail => do
      let (bounds, remaining) ← parseGenericBounds fuel tail
      pure (name :: bounds, remaining)
    | _ => pure ([name], rest)

/-- `N: u64` is the owner's shorthand for `N: const u64`. Other explicit constant types
    retain `const`; an identifier after `:` denotes a spec bound. -/
def parseGenericParam (fuel : Nat) (tokens : List Token) :
    Except String (SGenericParam × List Token) := do
  let (name, rest) ← nimmName tokens
  match rest with
  | .zeichen ":" :: .wort "const" :: tail => do
    let (ty, remaining) ← parseTyp fuel tail
    pure (.constant name ty, remaining)
  | .zeichen ":" :: .wort "fn" :: tail => do
    let (ty, remaining) ← parseTyp fuel (.wort "fn" :: tail)
    pure (.function name ty, remaining)
  | .zeichen ":" :: head :: tail =>
    if (nameText head).any istIntWort then do
      let (ty, remaining) ← parseTyp fuel (head :: tail)
      pure (.constant name ty, remaining)
    else do
      let (bounds, remaining) ← parseGenericBounds fuel (head :: tail)
      pure (.type name bounds, remaining)
  | _ => pure (.type name [], rest)

def parseGenericParamList : Nat → List Token →
    Except String (List SGenericParam × List Token)
  | 0, _ => .error "out of fuel"
  | fuel + 1, tokens => do
    let (param, rest) ← parseGenericParam fuel tokens
    match rest with
    | .zeichen "," :: tail => do
      let (params, remaining) ← parseGenericParamList fuel tail
      if params.any (fun p => strEq p.name param.name) then
        throw "duplicate generic parameter"
      pure (param :: params, remaining)
    | .zeichen "]" :: tail => pure ([param], tail)
    | _ => throw "generic parameters without ]"

def parseGenericParams (fuel : Nat) : List Token →
    Except String (List SGenericParam × List Token)
  | .zeichen "[" :: rest => parseGenericParamList fuel rest
  | tokens => .ok ([], tokens)

end Gabbro.Grammatik.Parser
