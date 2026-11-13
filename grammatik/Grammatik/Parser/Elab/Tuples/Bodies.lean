module
public import Grammatik.Parser.Elab.Tuples.Expressions
public import Grammatik.Parser.Stmt.BoundedRewrite
@[expose] public section

namespace Gabbro.Grammatik.Parser.Tuples

/-- Flatten a pattern into one evaluation followed by ordinary, typed record projections.
    Wildcards omit projections, never the evaluation of the tuple-producing expression. -/
def destructure (k : Context) (locals : Spec.Locals) (fuel : Nat)
    (names : List String) (annotation : Option STyp) (value : SExpr) : ExpandM (List SAnw) := do
  let value ← expandExpr k locals annotation fuel value
  let state ← get
  let some ty := annotation.orElse (fun _ => infer k state locals fuel value)
    | lift (.error "tuple pattern: value type cannot be inferred")
  let some elements := tupleElements k state ty
    | lift (.error "tuple pattern: value must have a tuple type")
  if elements.length != names.length then lift (.error "tuple pattern: arity mismatch")
  let ty ← expandType k fuel ty
  let elements ← elements.mapM (expandType k fuel)
  let state ← get
  let fresh := "#tuple-local:" ++ toString state.nextLocal
  set { state with nextLocal := state.nextLocal + 1 }
  let fields := (names.zip elements).zipIdx.filterMap fun ((name, ty), index) =>
    if strEq name "_" then none
    else some (SAnw.bind false name (some ty) (.field (.variable fresh) ("_" ++ toString index)))
  pure (.bind false fresh (some ty) value :: fields)

def localBindings (k : Context) (state : State) (locals : Spec.Locals) (statement : SAnw) : Spec.Locals :=
  Spec.bindings k.environment locals (infer k state · 128) statement ++
    locals.filter (fun entry => !(Aufloesung.gebunden statement).contains entry.1)

mutual
def expandStatement (k : Context) (locals : Spec.Locals) (result : Option STyp) :
    Nat → SAnw → ExpandM (List SAnw)
  | 0, _ => lift (.error "tuple expansion: statement fuel exhausted")
  | fuel + 1, statement => do
    let ex := expandExpr k locals none fuel
    let ty := expandType k fuel
    let body := fun extra s => do
      let ss ← expandStatement k (extra ++ locals) result fuel s
      pure (match ss with | [s] => s | ss => SAnw.block ss none)
    match statement with
    | .bind mu name annotation value =>
      let annotation ← annotation.mapM ty
      match tuplePatternNames name with
      | some names => destructure k locals fuel names annotation value
      | none => return [.bind mu name annotation (← expandExpr k locals annotation fuel value)]
    | .bindQ mu name annotation value =>
      let annotation ← annotation.mapM ty
      return [.bindQ mu name annotation (← expandExpr k locals annotation fuel value)]
    | .bindElse name annotation value reason failure =>
      let annotation ← annotation.mapM ty
      return [.bindElse name annotation (← expandExpr k locals annotation fuel value) reason
        (← body [] failure)]
    | .bindAxiomOpt name annotation value =>
      let annotation ← annotation.mapM ty
      return [.bindAxiomOpt name annotation (← expandExpr k locals annotation fuel value)]
    | .bindAxiomOptElse name annotation value reason failure =>
      let annotation ← annotation.mapM ty
      return [.bindAxiomOptElse name annotation (← expandExpr k locals annotation fuel value) reason
        (← body [] failure)]
    | .bindLib mu name annotation call =>
      return [.bindLib mu name (← annotation.mapM ty) { call with args := ← call.args.mapM ex }]
    | .lcall call => return [.lcall { call with args := ← call.args.mapM ex }]
    | .call name args =>
      let .call name args ← ex (.call name args) | lift (.error "tuple expansion: direct call expected")
      return [.call name args]
    | .callQ name args =>
      let .call name args ← ex (.call name args) | lift (.error "tuple expansion: direct call expected")
      return [.callQ name args]
    | .callElse name args reason failure =>
      let .call name args ← ex (.call name args) | lift (.error "tuple expansion: direct call expected")
      return [.callElse name args reason (← body [] failure)]
    | .callIndElse pointer args reason failure =>
      return [.callIndElse (← ex pointer) (← args.mapM ex) reason (← body [] failure)]
    | .set place op value =>
      let place ← ex place
      let state ← get
      return [.set place op (← expandExpr k locals (infer k state locals fuel place) fuel value)]
    | .shift place a b => return [.shift (← ex place) a b]
    | .cond condition yes branches no =>
      return [.cond (← ex condition) (← body [] yes) (← branches.mapM (body []))
        (← no.mapM (body []))]
    | .elsif condition branch => return [.elsif (← ex condition) (← body [] branch)]
    | .cases value arms =>
      let arms ← arms.mapM fun arm =>
        body (Spec.matchBindings k.items locals value arm) arm
      return [.cases (← ex value) arms]
    | .arm tag binder branch => return [.arm tag binder (← body [] branch)]
    | .each binder start domain subject mode raw invariant branch =>
      let inner := match subject with
        | .variable table => [(binder, STyp.index false table)]
        | _ => []
      return [.each binder (← start.mapM ex) domain (← ex subject) mode raw
        (← invariant.mapM (expandExpr k (inner ++ locals) none fuel)) (← body inner branch)]
    | .boundedLoop raw branch =>
      return [.boundedLoop (← mapBoundedHeaderM ex (fun name => pure name) raw)
        (← body (boundedLoopLocals raw) branch)]
    | .retry raw branch => return [.retry raw (← body [] branch)]
    | .loop raw branch => return [.loop raw (← body [] branch)]
    | .waive names branch => return [.waive names (← body [] branch)]
    | .trim value raw branch => return [.trim (← ex value) raw (← body [] branch)]
    | .trimReq value raw => return [.trimReq (← ex value) raw]
    | .locks shared lock branch => return [.locks shared (← ex lock) (← body [] branch)]
    | .watch name branch => return [.watch name (← body [] branch)]
    | .emit place value raw => return [.emit (← ex place) (← ex value) raw]
    | .await name annotation value raw => return [.await name (← annotation.mapM ty) (← ex value) raw]
    | .swap name annotation value raw => return [.swap name (← annotation.mapM ty) (← ex value) raw]
    | .ret value => return [.ret (← value.mapM (expandExpr k locals result fuel))]
    | .alloc mu name annotation arena count failure =>
      return [.alloc mu name (← annotation.mapM ty) arena (← ex count) (← failure.mapM (body []))]
    | .allocVon mu name annotation arena => return [.allocVon mu name (← annotation.mapM ty) arena]
    | .reset arena span =>
      return [.reset arena (← span.mapM fun (a, b) => return (← ex a, ← ex b))]
    | .grow arena count branch => return [.grow arena (← ex count) (← body [] branch)]
    | .free value => return [.free (← ex value)]
    | .child branch => return [.child (← body [] branch)]
    | .block statements ending =>
      let (statements, inner) ← expandStatements k locals result fuel statements
      let ending ← ending.mapM fun
        | .ret value => return .ret (← value.mapM (expandExpr k inner result fuel))
        | ending => pure ending
      return [.block statements ending]
    | statement => pure [statement]

def expandStatements (k : Context) (locals : Spec.Locals) (result : Option STyp) :
    Nat → List SAnw → ExpandM (List SAnw × Spec.Locals)
  | 0, _ => lift (.error "tuple expansion: block fuel exhausted")
  | _ + 1, [] => pure ([], locals)
  | fuel + 1, statement :: rest => do
    let statements ← expandStatement k locals result fuel statement
    let state ← get
    let inner := statements.foldl (localBindings k state) locals
    let (tail, final) ← expandStatements k inner result fuel rest
    pure (statements ++ tail, final)
end

end Gabbro.Grammatik.Parser.Tuples
