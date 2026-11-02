module

public import Grammatik.Parser.TaggedDispatch.Expressions
public import Grammatik.Parser.Dyn.Frontend
public import Grammatik.Parser.Stmt.LibrarySource
public import Grammatik.Parser.SourceFolds.Range

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
  let rewrite : Spec.Walk := { source := ordinary, instantiate := false, resolveSpecs := false,
    exprRewrite := fun locals _ e => do
      match e with
      | .call name args =>
        return .call (← taggedResolveCall ordinary bindings sources locals name args) args
      | _ => return e }
  ordinary.mapM (rewrite.item 100000)

/-- Shared declaration-expansion entry point, before ordinary item admission. -/
def exportDeclarationUnit (items : List SItemTief) : Except String (List SItemTief) := do
  let items ← SourceFolds.prepare items
  let (closed, items) ← Dyn.prepare items
  let items ← exportTaggedUnit items
  let output ← Spec.prepare (Dyn.finish closed items)
  exportLibraryUnit (← Dyn.checkedOutput items output)

end Gabbro.Grammatik.Parser
