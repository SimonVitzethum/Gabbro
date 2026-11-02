module

public import Grammatik.Parser.Expr.Typ

@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- A lossless library call. The region is the balanced token sequence inside the outer braces;
    its nested braces and token kinds are retained, without rendering and re-lexing the input.
    Resolution rewrites paths and ordinary arguments, never the translator's input tokens. -/
structure SLibraryCall where
  library : String
  function : String
  args : List SExpr
  region : List Token
  deriving Repr

def beqSLibraryCall (a b : SLibraryCall) : Bool :=
  strEq a.library b.library && strEq a.function b.function &&
    beqSExprList a.args b.args && decide (a.region = b.region)

/-- Collect a brace-balanced region, excluding its outer delimiters. Unlike `nimmBereich`,
    this preserves every input token. Exhaustion refuses an incomplete region. -/
def libraryRegion : List Token → Nat → Except String (List Token × List Token)
  | [], _ => .error "wanted }"
  | .zeichen "}" :: rest, 1 => .ok ([], rest)
  | .zeichen "{" :: rest, depth => do
      let (body, tail) ← libraryRegion rest (depth + 1)
      pure (.zeichen "{" :: body, tail)
  | .zeichen "}" :: rest, depth + 2 => do
      let (body, tail) ← libraryRegion rest (depth + 1)
      pure (.zeichen "}" :: body, tail)
  | t :: rest, depth => do
      let (body, tail) ← libraryRegion rest depth
      pure (t :: body, tail)

end Gabbro.Grammatik.Parser
