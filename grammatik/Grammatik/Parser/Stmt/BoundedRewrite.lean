module

public import Grammatik.Parser.Stmt.Anweisung.BoundedHeaders
public import Grammatik.Parser.Round.Rundlauf.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- Render a checked header after rewriting its references. -/
def renderBoundedHeader (header : SBoundedHeader) : String :=
  let render := fun e => String.intercalate " " ((druckToks e).map zeigeTok)
  match header with
  | .whileLoop condition bound handler =>
    "while " ++ render condition ++ " bounded " ++ render bound ++
      " ops on_exceeded " ++ handler ++ " "
  | .forRange binder lo hi handler =>
    "for " ++ binder ++ " in " ++ render lo ++ " ..< " ++ render hi ++
      (handler.map (fun h => " on_exceeded " ++ h)).getD "" ++ " "

/-- Rewrite header references with the same visitor as ordinary expressions and calls. -/
def mapBoundedHeaderM {m : Type → Type} [Monad m] (expr : SExpr → m SExpr)
    (callee : String → m String) (raw : String) : m String := do
  match readBoundedHeader raw with
  | .ok (.whileLoop condition bound handler) =>
    return renderBoundedHeader (.whileLoop (← expr condition) (← expr bound) (← callee handler))
  | .ok (.forRange binder lo hi handler) =>
    return renderBoundedHeader (.forRange binder (← expr lo) (← expr hi) (← handler.mapM callee))
  | .error _ => return raw

def mapBoundedHeader (expr : SExpr → SExpr) (callee : String → String) (raw : String) : String :=
  Id.run (mapBoundedHeaderM (m := Id) (fun e => pure (expr e)) (fun h => pure (callee h)) raw)

end Gabbro.Grammatik.Parser
