module

public import Grammatik.Parser.Expr.GenericArguments

namespace Gabbro.Grammatik.Parser

/-- The source parser previously stopped immediately after a direct call.
    Recognise the modelled await suffix there, without enabling arbitrary
    unmodelled result projections or changing the ordinary call AST. Its
    suspension meaning is resolved only by the outer async elaborator. -/
@[expose] public def awaitSuffix (value : SExpr) (tokens : List Token) : Except String (SExpr × List Token) :=
  match tokens with
  | .zeichen mark :: name :: rest =>
    if strEq mark "." && (nameText name).any (fun word => strEq word "await") then
      .ok (.field value "await", rest)
    else .ok (value, tokens)
  | _ => .ok (value, tokens)

end Gabbro.Grammatik.Parser
