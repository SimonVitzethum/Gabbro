module

public import Grammatik.Parser.TaggedDispatch.Statements
public import Grammatik.Parser.Stmt.LibrarySource

@[expose] public section
namespace Gabbro.Grammatik.Parser

/-- Declaration expansion used by the actual elaborator. Parse-time `by` metadata
    is consumed only after complete signature resolution and match generation. -/
def exportTaggedUnit (items : List SItemTief) : Except String (List SItemTief) := do
  let declarations := items.filterMap fun | .taggedByT decl spec => some (decl, spec) | _ => none
  if declarations.isEmpty then return items
  Spec.check items
  let mut generated := []
  let mut bindings := []
  for (decl, spec) in declarations do
    let (output, resolved) ← resolveTaggedDeclaration items decl spec
    generated := generated ++ output
    bindings := bindings ++ resolved
  if ¬ (bindings.map (fun b => b.signature.name)).Nodup then
    throw "tagged-dispatch-duplicate-dispatcher"
  let ordinary := items.filter (fun | .taggedByT .. => false | _ => true) ++ generated
  let sources := items.flatMap fun
    | .specGroupT spec _ _ fs => fs.map (fun sig => spec ++ "::" ++ sig.name)
    | _ => []
  let globals := ordinary.filterMap fun
    | .globT _ name ty _ _ _ _ | .constT name ty _ => some (name, ty)
    | _ => none
  ordinary.mapM fun
    | .fnT sig body => do
      let scope := sig.params ++ globals
      let rewrite := taggedRewriteExpr ordinary bindings sources scope 100000
      let clauses ← sig.klauseln.mapM fun
        | .needs e => return .needs (← rewrite e)
        | .gives e => return .gives (← rewrite e)
        | .drops e => return .drops (← rewrite e)
        | .cost e => return .cost (← rewrite e)
        | clause => pure clause
      pure (.fnT { sig with klauseln := clauses }
        (← taggedRewriteStmt ordinary bindings sources scope 100000 body))
    | item => pure item

/-- Shared declaration-expansion entry point, before ordinary item admission. -/
def exportDeclarationUnit (items : List SItemTief) : Except String (List SItemTief) := do
  exportLibraryUnit (← Spec.prepare (← exportTaggedUnit items))

end Gabbro.Grammatik.Parser
