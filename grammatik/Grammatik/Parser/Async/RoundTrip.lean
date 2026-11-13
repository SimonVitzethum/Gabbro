module

public import Grammatik.Parser.Async.Surface
public import Grammatik.Parser.Round.RundlaufItem.Teil3a

namespace Gabbro.Grammatik.Parser.AsyncSource

/-- The new call-result suffix rule is generic in the call AST and follow.
    It consumes exactly `.await` and preserves all following source tokens. -/
public theorem awaitSuffix_consumes (value : SExpr) (rest : List Token) :
    awaitSuffix value (.zeichen "." :: .ident "await" :: rest) =
      .ok (.field value "await", rest) := rfl

/-- Generic token-level round trip, with exactly the ordinary signature,
    block printability and fuel premises. No program-specific parser rule. -/
public theorem function_roundTrip (function : Function)
    (signature : SigGut function.signature) (body : BlockBein function.body)
    (head : BlockKopf function.body) (rest : List Token) (fuel : Nat)
    (enough : fbI (.fnT function.signature function.body) ≤ fuel) :
    parseFunction fuel (printFunction function ++ rest) = .ok (function, rest) := by
  have parsed := item_fn function.signature function.body signature body head rest fuel enough
  cases function
  simp only [printFunction, List.cons_append, parseFunction, parsed,
    String.reduceEq, ↓reduceIte, bind, Except.bind, pure, Except.pure]

end Gabbro.Grammatik.Parser.AsyncSource
