module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil12

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst
open Uebersetze

/-- Const option types need only the declared finite domain, not its mutable
    fields. This descriptor grants no runtime memory access or capability. -/
def constDomains (values : List (String × Int)) : List SItemTief → Except String (List UTab)
  | [] => .ok []
  | .tableT name _ (some count) _ _ _ _ :: rest => do
    let count ← uAnzahl values count
    if count < 0 then throw ("const domain has a negative extent: " ++ name)
    return { name, count, cols := [] } :: (← constDomains values rest)
  | _ :: rest => constDomains values rest

/-- Resolve every const signature in the same canonical value/type environment.
    Original source bodies and predicates remain available to their certificates. -/
def collectFunctions (items : List SItemTief) : Except String (List UKonstFn) := do
  let initial := uConstsRech (uKonstFns items) items []
  let aliases := uAliase initial items
  let values := uConstsRech (uKonstFnsWith aliases items) items []
  let types := uAliase values items ++ values.map (fun (name, value) => (name, (value, value)))
  let domains ← constDomains values items
  let schemas ← uSums types items domains
  let reasons ← uWhys items types
  let reasonSchemas : List USum := reasons.map (fun reason =>
    { name := reason.name, cases := reason.cases.map (fun name => (name, none)) })
  let named := schemas.map (fun schema => (schema.name, Ty.sum schema.spec)) ++
    reasons.map (fun reason => (reason.name, Ty.why reason.cases.length))
  let schemas := schemas ++ reasonSchemas
  items.foldrM (fun item rest =>
    match item with
    | .fnT signature body => do
      if !strEq signature.art "const" then return rest
      if signature.fehler.isSome then
        throw ("const reason channel is outside the admitted fragment: " ++ signature.name)
      let some result := signature.res
        | throw ("const function has no result type: " ++ signature.name)
      let resultType ← uTypIn types domains named result
      let params ← signature.params.mapM fun (name, type) => do
        return (name, ← uTypIn types domains named type)
      -- Prefer the nominal result schema when several schemas have equal shapes.
      let resultSchemas := match result with
        | .atom name => schemas.filter (fun schema => strEq schema.name name) ++
            schemas.filter (fun schema => !strEq schema.name name)
        | _ => schemas
      return { name := signature.name, params, erg := resultType, rumpf := body,
        signature, constants := values, sums := resultSchemas } :: rest
    | _ => pure rest) []

end Gabbro.Grammatik.Parser.Konst
