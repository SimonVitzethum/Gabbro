module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
public import Grammatik.Parser.Elab.Konst.Scopes.ConstantScopes

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst
open Uebersetze

/-- Const option types need only the declared finite domain, not its mutable
    fields. This descriptor grants no runtime memory access or capability. -/
def constDomains (values : List (String × Int)) : List SItemTief → Except String (List UTab)
  | [] => .ok []
  | .tableT name _ (some count) _ _ _ _ _ :: rest => do
    let count ← uAnzahl values count
    if count < 0 then throw ("const domain has a negative extent: " ++ name)
    return { name, count, cols := [] } :: (← constDomains values rest)
  | _ :: rest => constDomains values rest

/-- One descriptor collector at the supplied canonical value/type environment.
    Original source bodies, parameters and predicates remain unchanged. -/
def collectFunctionsWith (items : List SItemTief) (values : List (String × Int))
    (types : List (String × (Int × Int))) : Except String (List UKonstFn) := do
  let domains ← constDomains values items
  let schemas ← uSums types items domains (spaces := []) (eigner := [])
  let reasons ← uWhys items types
  let reasonSchemas : List (USum Ty) := reasons.map (fun reason =>
    { name := reason.name, cases := reason.cases.map (fun name => (name, none)) })
  let named := schemas.map (fun schema => (schema.name, Ty.sum schema.spec)) ++
    reasons.map (fun reason => (reason.name, Ty.why reason.cases.length))
  let schemas := schemas ++ reasonSchemas
  items.reverse.foldlM (fun (rest : List UKonstFn) item =>
    match item with
    | .fnT signature body => do
      if !strEq signature.art "const" then return rest
      if signature.fehler.isSome then
        throw ("const reason channel is outside the admitted fragment: " ++ signature.name)
      let some result := signature.res
        | throw ("const function has no result type: " ++ signature.name)
      let resultType ← uTypIn types domains named (spaces := []) (eigner := []) result
      let params ← signature.params.mapM fun (name, type) => do
        return (name, ← uTypIn types domains named (spaces := []) (eigner := []) type)
      -- Prefer the nominal result schema when several schemas have equal shapes.
      let resultSchemas : List (USum Ty) := match result with
        | .atom name => schemas.filter (fun schema => strEq schema.name name) ++
            schemas.filter (fun schema => !strEq schema.name name)
        | _ => schemas
      return ({
          name := signature.name
          params := params
          erg := resultType
          rumpf := body
          signature := signature
          constants := values
          sums := resultSchemas } : UKonstFn) :: rest
    | _ => pure rest) []

/-- Resolve signatures and close call arguments only after the existing checked
    alias/scalar schedule has established their complete original-source scope. -/
def collectFunctions (items : List SItemTief) : Except String (List UKonstFn) := do
  if !items.any (fun | .fnT signature _ => strEq signature.art "const" | _ => false) then
    return []
  let checkedScope ← Gabbro.Stage0.Frontend.elaborateConstantScopes items
  collectFunctionsWith items checkedScope.scope.values checkedScope.scope.types

/-- The actual substitution entry consumes exactly the certified scope, not a
    second discovery environment or a caller-supplied range approximation. -/
theorem collectFunctions_from_scopes (items : List SItemTief)
    (checkedScope : Gabbro.Stage0.Frontend.DerivedScopes items)
    (present : items.any (fun | .fnT signature _ => strEq signature.art "const" | _ => false) = true)
    (selected : Gabbro.Stage0.Frontend.elaborateConstantScopes items = .ok checkedScope) :
    collectFunctions items = collectFunctionsWith items checkedScope.scope.values checkedScope.scope.types := by
  simp [collectFunctions, present, selected]
  rfl

end Gabbro.Grammatik.Parser.Konst
