module

public import Grammatik.Parser.Stmt.Anweisung.Kopf

@[expose] public section
namespace Gabbro.Grammatik.Parser

/-- A resolved case implementation; payload layout remains that of the tagged schema. -/
structure TaggedDispatchCase where
  name : String
  implementation : Option String
  deriving Repr

/-- Expand a resolved dispatchable function into the existing match tree.
    The continuation receives the statically resolved call. Non-dispatchable functions
    are excluded by signature resolution and remain available for static calls.
    Arguments before and after the unique receiver retain their declared order. -/
def expandTaggedDispatch (receiver : SExpr) (before after : List SExpr)
    (cases : List TaggedDispatchCase) (continuation : SExpr → SAnw) :
    Except String SAnw := do
  let arms ← cases.mapM fun c => do
    let target ← match c.implementation with
      | some target => pure target
      | none => throw ("tagged-dispatch-missing-implementation: " ++ c.name)
    pure (SAnw.arm c.name (some "#dispatch")
      (continuation (.call target (before ++ [.variable "#dispatch"] ++ after))))
  pure (.cases receiver arms)

end Gabbro.Grammatik.Parser
