module

public import Grammatik.Parser.Stmt.Anweisung.Defs1

@[expose] public section
namespace Gabbro.Grammatik.Parser

/-- Expression callees share the ordinary handler reader and require an explicit
    handler. Keep the expression in the tree instead of printing it into a name. -/
def parseIndRufMitElse (block : List Token → Except String (SAnw × List Token))
    (pointer : SExpr) (args : List SExpr) (toks : List Token) :
    Except String (SAnw × List Token) := do
  let (statement, rest) ← parseRufMitElse block "" args toks
  match statement with
  | .callElse _ args reason body => pure (.callIndElse pointer args reason body, rest)
  | _ => .error "indirect expression statement needs else"

/-- Behind the opening parenthesis of `(pointer)(args) else [(reason)] { ... };`. -/
def parseIndRuf (fuel : Nat) (block : List Token → Except String (SAnw × List Token))
    (toks : List Token) : Except String (SAnw × List Token) := do
  let (pointer, rest) ← parseOr fuel toks
  let rest ← fordereZeichen ")" rest
  let rest ← fordereZeichen "(" rest
  let (args, rest) ← parseArgs fuel rest
  parseIndRufMitElse block pointer args rest

end Gabbro.Grammatik.Parser
