module

public import Grammatik.Parser.Spec.Items

@[expose] public section

namespace Gabbro.Grammatik.Parser.Spec

/-- The visitor of `resolveKnownBodies`: one per source, shared by all its items. -/
def knownWalk (source : List SItemTief) : Walk := {
  source
  instantiate := false
  resolveSpecs := false
  exprRewrite := fun locals _ e => do
    let resolve := fun name types args =>
      match resolveCall source locals name types args with
      | .ok target => pure (SExpr.call target args)
      | .error _ => pure e
    match e with
    | .call name args => resolve name none args
    | .ext .instantiate (name :: words) args =>
      match explicitTypes (String.intercalate ", " words) with
      | .ok types => resolve name (some types) args
      | .error _ => pure e
    | _ => pure e }

/-- One item under a visitor built once. -/
def resolveKnownWith (rewrite : Walk) : SItemTief → Except String SItemTief
  | .fnT sig body => do
    return .fnT sig (← { rewrite with result := sig.res }.statement sig.params 100000 body)
  | .implGroupT n ts es fs => do return .implGroupT n ts es (← fs.mapM (resolveKnownWith rewrite))
  | .modT n fs => do return .modT n (← fs.mapM (resolveKnownWith rewrite))
  | .pubT it => do return .pubT (← resolveKnownWith rewrite it)
  | .gateT it => do return .gateT (← resolveKnownWith rewrite it)
  | it => pure it
termination_by item => sizeOf item

/-- Resolve statically known spec calls before dyn closure. Calls whose receiver is
    dynamic (or whose type depends on a later binding) stay for the mandatory final
    resolver. This pass never admits a program: every remaining call must resolve there. -/
def resolveKnownBodies (source : List SItemTief) (item : SItemTief) : Except String SItemTief :=
  resolveKnownWith (knownWalk source) item

/-- All items of a source under one visitor: the visitor is built before the items are walked. -/
def resolveKnownAll (source items : List SItemTief) : Except String (List SItemTief) :=
  let rewrite := knownWalk source
  items.mapM (resolveKnownWith rewrite)

theorem resolveKnownAll_eq (source items : List SItemTief) :
    resolveKnownAll source items = items.mapM (resolveKnownBodies source) := rfl



/-- Check model A: check interfaces, materialize concrete bodies, resolve every abstract call,
    and validate that only existing forms remain. Real contracts travel with the concrete calls. -/
def expand (items : List SItemTief) : Except String (List SItemTief) := do
  check items
  let concrete := materialize items
  if !uniqueNames ((functionHeads concrete).map (·.name)) then throw "spec.function.collision"
  let output ← concrete.mapM (({ source := items, instantiate := true } : Walk).item 100000)
  if ordinary items output then return output else throw "spec.output"

/-- Every successful instantiation passes the ordinary-form gate, for arbitrary input programs.
    The existing elaborator subsequently checks types and the implementations' actual contracts. -/
theorem expand_ordinary {items output : List SItemTief} (h : expand items = .ok output) :
    ordinary items output = true := by
  unfold expand at h
  cases hc : check items with
  | error e => simp [hc, bind, Except.bind] at h
  | ok u =>
    simp only [hc, bind, Except.bind] at h
    split at h
    · simp at h
    · cases hw : (materialize items).mapM (({ source := items, instantiate := true } : Walk).item 100000) with
      | error e => simp [hw] at h
      | ok result =>
        simp only [hw, bind, Except.bind] at h
        split at h
        · have he : result = output := by simpa only [pure, Except.pure, Except.ok.injEq] using h
          subst output
          assumption
        · simp at h

/-- Preserve the existing front-end path for units with no spec-group items. -/
def prepare (items : List SItemTief) : Except String (List SItemTief) :=
  if items.any (fun | .specGroupT .. | .implGroupT .. => true | _ => false) then expand items
  else .ok items

end Gabbro.Grammatik.Parser.Spec
