module
public import Grammatik.Parser.Elab.Generic.Body
@[expose] public section
namespace Gabbro.Grammatik.Parser.Generic

/-- Every declaration namespace is checked before generated names are inserted. -/
def sourceName : SItemTief → Option String
  | .fnT sig _ | .protoT sig | .specT sig _ | .asmT sig _ | .transT _ sig _ => some sig.name
  | .typeT _ n _ _ _ | .constT n _ _ | .globT _ n _ _ _ _ _ | .formatT n _ _ _ |
    .tableT n _ _ _ _ _ _ | .arenaT n _ _ _ _ _ | .whyT n _ _ | .stateT n _ |
    .devT n _ _ _ | .assumT n _ _ _ | .axiomT n _ _ _ _ _ | .atomT n _ _ _ _ |
    .lockT n _ _ _ _ _ _ | .rcuT n _ _ | .groupT n _ _ | .accT n _ _ _ |
    .trustT n _ _ _ _ _ | .bootT n _ _ _ | .varT n | .goalT n _ => some n
  | .checkT check => some check.cname
  | .walkT walk => some walk.name
  | .entryT entry => some entry.name
  | .callT call => some call.name
  | _ => none

/-- All ordinary declarations participate in explicit-call lookup and duplicate checking. -/
def environment (source : List SItemTief) : Environment :=
  let declarations := source.filterMap fun
    | .fnT sig body => some (sig, body)
    | _ => none
  let ordinary := source.filter fun
    | .fnT sig _ => sig.generics.isEmpty
    | _ => true
  let fns := Uebersetze.uKonstFns ordinary
  let constants := Uebersetze.uConstsRech fns ordinary []
  { declarations, constants, constantFunctions := fns,
    aliases := Uebersetze.uAliase constants ordinary ++ Uebersetze.uAliasBreiten ordinary,
    globals := source.filterMap sourceName }

mutual
def rewriteConstant (env : Environment) : SKonstWert → RewriteM SKonstWert
  | .one value => return .one (← rewriteExpression env {} value)
  | .rows rows => return .rows (← rewriteConstants env rows)
def rewriteConstants (env : Environment) : List SKonstWert → RewriteM (List SKonstWert)
  | [] => pure []
  | row :: rest => return (← rewriteConstant env row) :: (← rewriteConstants env rest)
end

/-- Templates are removed. Generic prototypes, predicates and assembly bodies have no instance
    body rule here and are refused, including unreachable ones. Other items retain their existing gates. -/
def rewriteItem (env : Environment) : SItemTief → RewriteM (List SItemTief)
  | .fnT sig body => do
    if !sig.generics.isEmpty then pure []
    else return [.fnT (← rewriteSignature env {} sig) (← rewriteBody env {} body)]
  | .protoT sig =>
    if sig.generics.isEmpty then return [.protoT (← rewriteSignature env {} sig)]
    else liftResult (.error "generic prototype requires a function body")
  | .specT sig predicate =>
    if sig.generics.isEmpty then return [.specT (← rewriteSignature env {} sig)
      (← rewriteExpression env {} predicate)]
    else liftResult (.error "generic spec function requires a function body")
  | .asmT sig raw =>
    if sig.generics.isEmpty then pure [.asmT sig raw]
    else liftResult (.error "generic assembly body has no instantiation rule")
  | .transT target sig body =>
    if sig.generics.isEmpty then return [.transT target (← rewriteSignature env {} sig)
      (← rewriteBody env {} body)]
    else liftResult (.error "generic library translator has no instantiation rule")
  | .constT name ty value => return [.constT name (← rewriteType env {} ty) (← rewriteConstant env value)]
  | .globT mu name ty value aligned section shared => return [.globT mu name
      (← rewriteType env {} ty) (← rewriteConstant env value)
      (← aligned.mapM (rewriteExpression env {})) section shared]
  | .concT roots => do
    let roots ← roots.mapM fun (path, args) => do
      if env.declarations.any (fun p => strEq p.1.name (String.intercalate "::" path) &&
          !p.1.generics.isEmpty) then
        liftResult (.error "generic concurrent root requires an ordinary wrapper")
      else pure (path, ← args.mapM (rewriteExpression env {}))
    pure [.concT roots]
  | item => pure [item]

/-- Reject changing type/constant arguments along a recursive cycle, even for finite cycles. -/
def checkRecursion (env : Environment) : Nat → List Instance → Instance → Except String Unit
  | 0, _, _ => .error "generic recursion check exceeded the closed instance set"
  | fuel + 1, ancestors, key => do
    match ancestors.find? (fun ancestor => strEq ancestor.function key.function) with
    | some ancestor =>
      if ancestor == key then pure () else throw "polymorphic generic recursion is refused"
    | none =>
      let (_, children) ← instantiate env key
      for child in children do
        checkRecursion env fuel (key :: ancestors) child

/-- Reuse the canonical specification-call expansion after monomorphisation and before literal
    materialization. Only the spec table and parameter names are read by uSpecKlauseln. -/
def expandSpecificationContracts (specs : List (String × List String × SExpr))
    (sig : FnSig) : Except String FnSig := do
  if specs.isEmpty then pure sig else
    let ctx : Uebersetze.UCtx :=
      { names := sig.params.map Prod.fst, kinds := [], types := [], tabs := [], locks := [],
        held := [], res := none, fname := sig.name, alias := [], lits := [], specs }
    let clauses ← Uebersetze.uSpecKlauseln ctx (sig.params.map Prod.fst) sig.klauseln
    pure { sig with klauseln := clauses }

/-- The output retains every ordinary item and appends exactly the closed, deterministically named
    body instances. The structural source size bounds work, and exhaustion always refuses. -/
def expandTemplatesWithRequirements (source : List SItemTief) :
    Except String (List SItemTief × List (STyp × String)) := do
  let env := environment source
  let names := source.filterMap sourceName
  for (sig, _) in env.declarations do
    if !sig.generics.isEmpty && (names.filter (strEq sig.name)).length != 1 then
      throw ("duplicate generic function: " ++ sig.name)
    for param in sig.generics do
      match param with
      | .type _ [] | .constant _ _ => pure ()
      | .type _ (_ :: _) => throw "generic spec bounds: conformance rule unavailable"
      | .function _ ty => do
        let _ ← staticParameterType {} ty
        pure ()
  let (ordinary, roots) ← (do
    let groups ← source.mapM (rewriteItem env)
    pure groups.flatten).run []
  for root in roots do
    checkRecursion env (env.declarations.length + 1) [] root
  let instances ← boundedInstanceClosure (sizeOf source)
    (fun key => do pure (← instantiate env key).2) roots
  checkInstanceNames names instances
  let results ← instances.mapM (instantiate env)
  let generated := results.map (fun result =>
    let ((sig, body), _, _) := result.1
    SItemTief.fnT sig body)
  let literals := results.flatMap (fun result => result.1.2.1)
  let requirements := results.flatMap (fun result => result.1.2.2)
  let specs := ordinary.filterMap fun
    | .specT sig predicate => some (sig.name, sig.params.map Prod.fst, predicate)
    | _ => none
  let ordinary ← (ordinary ++ generated).mapM fun
    | .fnT sig body => return .fnT (← expandSpecificationContracts specs sig) body
    | item => pure item
  let literals ← literals.mapM fun (sig, body) => do
    pure (← expandSpecificationContracts specs sig, body)
  let target ← appendLiterals (names ++ instances.map instanceName) ordinary literals
  pure (target, requirements)

/-- Generic syntax belongs to ordinary function bodies in this implementation. -/
def genericHeader : SItemTief → Bool
  | .fnT sig _ | .protoT sig | .specT sig _ | .asmT sig _ | .transT _ sig _ => !sig.generics.isEmpty
  | _ => false

/-- Successful expansion removes all generic declarations. The check is a refusal gate, never
    an unchecked fallback; ordinary units retain their exact original frontend path. -/
def expandWithRequirements (source : List SItemTief) :
    Except String (List SItemTief × List (STyp × String)) := do
  if source.any genericHeader then
    let (target, requirements) ← expandTemplatesWithRequirements source
    if target.any genericHeader then throw "generic expansion left a template declaration"
    pure (target, requirements)
  else pure (source, [])

def expand (source : List SItemTief) : Except String (List SItemTief) :=
  (expandWithRequirements source).map Prod.fst

/-- Model A's generic syntactic guarantee: the actual exporter receives ordinary declarations.
    Their safety and contracts are checked by the unchanged G elaboration and checker. -/
theorem expand_ordinary (source target : List SItemTief) (h : expand source = .ok target) :
    target.any genericHeader = false := by
  cases hs : source.any genericHeader with
  | false =>
    simp [expand, expandWithRequirements, hs] at h
    cases h
    exact hs
  | true =>
    cases he : expandTemplatesWithRequirements source with
    | error error => simp [expand, expandWithRequirements, hs, he] at h
    | ok result =>
      rcases result with ⟨result, requirements⟩
      cases hg : result.any genericHeader with
      | false =>
        simp [expand, expandWithRequirements, hs, he, hg] at h
        cases h
        exact hg
      | true => simp [expand, expandWithRequirements, hs, he, hg] at h

end Gabbro.Grammatik.Parser.Generic
