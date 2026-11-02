module
public import Grammatik.Parser.Stmt.Anweisung.Defs2a

public import Grammatik.Parser.Expr.Typ
public import Grammatik.Parser.Stmt.Anweisung.Defs1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

/-- One statement: the token list must end here. -/
def parseTopStmt (toks : List Token) : Except String SAnw :=
  match parseStmt (toks.length * 8 + 32) toks with
  | .ok (s, [.ende]) => .ok s
  | .ok (_, _) => .error "trailing tokens"
  | .error e => .error e

/-- One block: the token list must end here. -/
def parseTopBlock (toks : List Token) : Except String SAnw :=
  match parseBlock (toks.length * 8 + 32) toks with
  | .ok (b, [.ende]) => .ok b
  | .ok (_, _) => .error "trailing tokens"
  | .error e => .error e

/-- Shape equality on statement outcomes, as a `Bool`. -/
def beqTopStmt : Except String SAnw → Except String SAnw → Bool
  | .ok a, .ok b => beqSAnw a b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false

/-- Shape equality on block outcomes, as a `Bool`. -/
def beqTopBlock : Except String SAnw → Except String SAnw → Bool
  | .ok a, .ok b => beqSAnw a b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false
