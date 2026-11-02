module
public import Grammatik.Parser.Expr.Ausdruck.Teil1
@[expose] public section
namespace Gabbro.Grammatik.Parser

/-- Split explicit arguments at outer commas. Nested types, expressions and literal bodies stay
    intact; the declared parameter kind determines which reader interprets each group later. -/
def genericArguments : List Token → List String → List Token → List String →
    Except String (List String × List Token)
  | [], _, _, _ => .error "generic arguments without ]"
  | .zeichen "]" :: rest, [], current, done =>
    if current.isEmpty then .error "empty generic argument"
    else .ok (done ++ [String.intercalate " " (current.reverse.map zeigeTok)], rest)
  | .zeichen "," :: rest, [], current, done =>
    if current.isEmpty then .error "empty generic argument"
    else genericArguments rest [] []
      (done ++ [String.intercalate " " (current.reverse.map zeigeTok)])
  | .zeichen s :: rest, stack, current, done =>
    let closer := if s == "[" then some "]" else if s == "(" then some ")"
      else if s == "{" then some "}" else if s == "<" then some ">" else none
    match closer with
    | some close => genericArguments rest (close :: stack) (.zeichen s :: current) done
    | none =>
      if s == "]" || s == ")" || s == "}" || s == ">" then
        match stack with
        | close :: tail =>
          if s == close then genericArguments rest tail (.zeichen s :: current) done
          else .error "mismatched generic argument delimiter"
        | [] => .error "unexpected generic argument delimiter"
      else genericArguments rest stack (.zeichen s :: current) done
  | .ende :: _, _, _, _ => .error "generic arguments without ]"
  | token :: rest, stack, current, done =>
    genericArguments rest stack (token :: current) done

end Gabbro.Grammatik.Parser
