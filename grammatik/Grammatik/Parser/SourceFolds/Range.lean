module

public import Grammatik.Parser.Spec.Items

@[expose] public section
namespace Gabbro.Grammatik.Parser.SourceFolds

/-- A range fold obtains its finite domain from an indexed array, never from a
    generated table or an unchecked numeric bound. -/
private def indexedArrays (binder : String) : Nat → SExpr → Except String (List String)
  | 0, _ => .error "fold range: operand nesting limit"
  | n + 1, .index (.variable array) (.variable index) =>
    pure (if strEq index binder then [array] else [])
  | n + 1, .field e _ | n + 1, .arrow e _ | n + 1, .un _ e | n + 1, .old e =>
    indexedArrays binder n e
  | n + 1, .index a b | n + 1, .bin _ a b => do
    return (← indexedArrays binder n a) ++ (← indexedArrays binder n b)
  | n + 1, .call _ args | n + 1, .built _ args | n + 1, .ext _ _ args => do
    return (← args.mapM (indexedArrays binder n)).flatten
  | _ + 1, _ => pure []

/-- Fresh internal names cannot capture a body reference, local, function or the
    range binder. Supplied ASTs with internal spellings are checked too. -/
private def freshName (used : List String) (role : String) : Except String String := do
  let candidates := (List.range (used.length + 1)).map fun n =>
    "$rangeFold$" ++ role ++ "$" ++ toString n
  let some name := candidates.find? (fun name => !used.contains name)
    | throw "fold: generated binding collision"
  pure name

/-- `return add i in 0 ..< N : e` for an indexed `[T; N]` array is
    ordinary array traversal. Calls in `e` are evaluated once inside the loop;
    their effects, contracts and the non-wrapping sum retain the ordinary checks.
    The result type is explicit; no accumulator range or overflow fact is guessed. -/
def returnFold (source : List SItemTief) (locals : Spec.Locals)
    (result : Option STyp) : SAnw → Except String SAnw
  | .ret (some (.ext .foldAdd [binder, "range"] [lo, hi, filter, value])) => do
    if !beqSExpr lo (.lit 0) then throw "fold range: lower bound must be zero"
    let arrays ← indexedArrays binder 1000 value
    let some array := arrays.head? | throw "fold range: indexed array required"
    if !(arrays.all (strEq array)) then throw "fold range: exactly one indexed array required"
    if strEq array binder then throw "fold range: binder shadows its array"
    let some (.array _ count) := Spec.inferType source locals 128 (.variable array)
      | throw "fold range: array type required"
    if !beqSExpr hi count then throw "fold range: upper bound must equal the array length"
    let some ty := result | throw "fold range: explicit integer result required"
    let .atom word := ty | throw "fold range: explicit integer result required"
    if !(istIntWort word || istZuckerBreite word) then
      throw "fold range: explicit integer result required"
    let used := binder :: locals.map Prod.fst ++
      Oeffentlich.namenA [] value ++ Oeffentlich.namenA [] filter ++
      (Spec.functionHeads source).map (·.name)
    let acc ← freshName used "acc"
    let element ← freshName (acc :: used) "value"
    let body := SAnw.block
      [.bind false element none value, .set (.variable acc) "+=" (.variable element)] none
    let body := if beqSExpr filter .tru then body else
      SAnw.block [.cond filter body [] none] none
    pure (.block [.bind true acc (some ty) (.lit 0),
      .each binder none "elems" (.variable array) "unvisited" "" none body]
      (some (.ret (some (.variable acc)))))
  | statement => pure statement

/-- Range sugar has a deliberately checked domain. Unsupported contexts (such as
    a nested expression or min/max range) refuse instead of reaching another fold path. -/
private def expression (expr : SExpr) : Except String SExpr :=
  match expr with
  | .ext .foldAdd (_ :: "range" :: _) _ |
    .ext .foldMin (_ :: "range" :: _) _ | .ext .foldMax (_ :: "range" :: _) _ =>
    .error "fold range: only a direct integer add-fold return is supported"
  | expr => .ok expr

/-- Reuse the shared lexical visitor before generic checks and before spec resolution.
    Symbolic N is compared to the symbolic array length; instantiation substitutes
    both through the existing constant-parameter machinery. -/
def prepare (source : List SItemTief) : Except String (List SItemTief) :=
  let walk : Spec.Walk := { source, instantiate := false, resolveSpecs := false,
    statementRewrite := returnFold source,
    exprRewrite := fun _ _ e => expression e }
  source.mapM (walk.item 100000)

end Gabbro.Grammatik.Parser.SourceFolds
