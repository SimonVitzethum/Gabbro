module

public import Grammatik.Parser.Dyn.Rewrite

@[expose] public section
namespace Gabbro.Grammatik.Parser.Dyn

/-- Resolve statically known spec calls before dyn closure. Calls whose receiver is
    dynamic (or whose type depends on a later binding) stay for the mandatory final
    resolver. This pass never admits a program: every remaining call must resolve there. -/
def resolveKnownBodies (source : List SItemTief) : SItemTief → Except String SItemTief
  | .fnT sig body => do
    let rewrite : Spec.Walk := { source, instantiate := false, resolveSpecs := false,
      exprRewrite := fun locals _ e => do
        let resolve := fun name types args =>
          match Spec.resolveCall source locals name types args with
          | .ok target => pure (SExpr.call target args)
          | .error _ => pure e
        match e with
        | .call name args => resolve name none args
        | .ext .inst [name, raw] args =>
          match Spec.explicitTypes raw with
          | .ok types => resolve name (some types) args
          | .error _ => pure e
        | _ => pure e }
    return .fnT sig (← { rewrite with result := sig.res }.statement sig.params 100000 body)
  | .implGroupT n ts es fs => do return .implGroupT n ts es (← fs.mapM (resolveKnownBodies source))
  | .modT n fs => do return .modT n (← fs.mapM (resolveKnownBodies source))
  | .pubT it => do return .pubT (← resolveKnownBodies source it)
  | .gateT it => do return .gateT (← resolveKnownBodies source it)
  | it => pure it

/-- Close only after the canonical conformance gate has resolved all linked spec instances.
    The first traversal rewrites types; the second has a complete concrete field/signature
    environment for producer inference and the no-reflection checks. -/
def prepare (items : List SItemTief) : Except String (List Closed × List SItemTief) := do
  Spec.check items
  let items ← items.mapM (resolveKnownBodies items)
  let uses := uniqueTypes (itemsUses items)
  let closed ← catalog items uses
  if closed.isEmpty then return ([], items)
  let declarations := closed.map declaration
  let existing ← Uebersetze.uSumSchemas (items.filterMap fun
    | .taggedByT decl _ => some decl
    | item => some item)
  let generatedCases := closed.flatMap fun c => c.cases.map (·.name)
  if existing.any (fun s => s.cases.any (fun c => generatedCases.any (strEq c.1))) ||
      (Spec.functionHeads (Spec.materialize items)).any (fun s => generatedCases.any (strEq s.name)) ||
      items.any (fun | .typeT _ n _ _ _ => closed.any (fun c => strEq c.name n) | _ => false) then
    throw "dyn.generated-name-collision"
  let types : Spec.Walk := { source := items, instantiate := false, resolveSpecs := false,
    typeRewrite := lowerType closed }
  let typed ← items.mapM (types.item 100000)
  let rewrite : Spec.Walk := { source := typed ++ declarations, instantiate := false,
    resolveSpecs := false, typeRewrite := lowerType closed,
    exprRewrite := rewriteExpr typed closed, statementCheck := checkStatement typed closed, rawCheck := checkRaw typed closed }
  let output ← typed.mapM (rewrite.item 100000)
  return (closed, output ++ declarations)

/-- Call effects remain the written bound, even if linked cases use a smaller subset.
    One case branch is charged in addition to the abstract function's cost. -/
def finish (closed : List Closed) (items : List SItemTief) : List SItemTief :=
  items.map fun
    | .fnT sig body =>
      match closed.find? (fun c => sig.name.startsWith ("#tagged-" ++ c.name ++ "::" ++ c.spec ++ "::")) with
      | none => .fnT sig body
      | some c =>
        .fnT { sig with klauseln := sig.klauseln.filterMap (fun
          | .effs _ => none
          | .cost e => some (.cost (.bin "+" e (.lit 1)))
          | k => some k) ++ [.effs c.effects] } body
    | item => item

/-- The output gate is shared with spec instantiation and rejects every unexpanded dyn node. -/
def checkedOutput (source output : List SItemTief) : Except String (List SItemTief) :=
  if Spec.ordinary source output then .ok output else .error "dyn.output"

/-- Generic output-form guarantee, independent of any fixture or linked implementation list. -/
theorem checkedOutput_ordinary {source output result : List SItemTief}
    (h : checkedOutput source output = .ok result) : Spec.ordinary source result = true := by
  unfold checkedOutput at h
  split at h
  · cases h
    assumption
  · cases h

end Gabbro.Grammatik.Parser.Dyn
