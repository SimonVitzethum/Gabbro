module

import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

public import Grammatik.Parser.Expr.Typ

@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- A lossless library call. The library and function names are `::` paths (one segment for
    an unqualified spelling); resolution rewrites each into its item key, never the translator's
    input tokens. The region is the balanced token sequence inside the outer braces; its nested
    braces and token kinds are retained, without rendering and re-lexing the input. -/
structure SLibraryCall where
  library : List String
  function : List String
  args : List SExpr
  region : List Token
  deriving Repr

def beqSLibraryCall (a b : SLibraryCall) : Bool :=
  beqWorte a.library b.library && beqWorte a.function b.function &&
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
