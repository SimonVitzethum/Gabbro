module

public import Grammatik.Parser.Elab.Uebersetze.Teil11

public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Labels retain first-occurrence numbering. Numeric and dynamic endpoints
    do not acquire invented labels, and declared values are never labels. -/
@[expose] def uStufenNamen (steps : List (SExpr × SExpr × SExpr)) (acc : List String)
    (values : List String := []) : Except String (List String) :=
  match steps with
  | [] => .ok acc
  | (_, a, b) :: rest =>
    let add := fun (names : List String) (e : SExpr) => match e with
      | .variable n =>
        if values.any (strEq · n) || names.any (strEq · n) then names else names ++ [n]
      | _ => names
    uStufenNamen rest (add (add acc a) b) values

/-- Resolve a label exactly, or reuse ordinary arithmetic elaboration.
    There is no fallback to stage zero. -/
@[expose] def uTransitionEndpoint (ctx : UCtx) (labels : List String) (e : SExpr) : Except String USide :=
  match e with
  | .variable n =>
    match labels.findIdx? (strEq · n) with
    | some k => .ok (.lit (Int.ofNat k))
    | none => uWertBody ctx e
  | _ => uWertBody ctx e

/-- Conjunctive lock requirements become the ordinary held-resource list.
    Disjunctive or negated Held expressions acquire no lock. -/
@[expose] def uTransitionRequirements : SExpr → List SKlausel
  | .bin "&&" a b => uTransitionRequirements a ++ uTransitionRequirements b
  | e => [.needs e]

/-- Resolve real places in the declaration's scope, retaining relative field
    identity for the later use-site specialization. -/
@[expose] def uTransitionPlace (ctx : UCtx) : SExpr → Except String UTransitionPlace
  | .variable n =>
    if ctx.globs.any (fun g => strEq g.name n) then .ok (.glob n)
    else if ctx.tabs.any (fun t => t.cols.any (fun f => strEq f.1 n)) then .ok (.relative n)
    else .error ("transition place unknown: " ++ n)
  | e =>
    match uZugriff ctx e with
    | .ok (.tabelle _, table, field, index) => .ok (.slot table field index)
    | .ok (.thru ..) => .error "transition through a pointer without G form"
    | .error message => .error message

/-- A clause-bearing declaration must explicitly grant every store.
    A relative field is checked against the use-site table, never against an
    arbitrary table with the same field name. -/
@[expose] def uTransitionPermission (puts gputs : List String) : UTransitionPlace → Bool
  | .slot table .. => puts.any (strEq · table)
  | .glob name => gputs.any (strEq · name)
  | .relative _ => false

/-- A fail-closed source check, in addition to the ordinary atomic contract
    footprint check. Transition declarations have no captured caller names. -/
@[expose] def uTransitionAtomicFree (ctx : UCtx) : Nat → SExpr → Bool
  | 0, _ => false
  | _ + 1, .lit _ | _ + 1, .float _ | _ + 1, .tru | _ + 1, .fls |
    _ + 1, .res | _ + 1, .why .. | _ + 1, .fnref _ => true
  | _ + 1, .variable name =>
    !ctx.globs.any (fun g => strEq g.name name && g.atomic && g.shared)
  | n + 1, .field e _ | n + 1, .arrow e _ | n + 1, .un _ e | n + 1, .old e =>
    uTransitionAtomicFree ctx n e
  | n + 1, .index a b | n + 1, .bin _ a b =>
    uTransitionAtomicFree ctx n a && uTransitionAtomicFree ctx n b
  | n + 1, .call _ args | n + 1, .built _ args | n + 1, .ext _ _ args =>
    args.all (uTransitionAtomicFree ctx n)

/-- Lower all clauses using the ordinary predicate, value and effect readers.
    Unsupported mark/service flows retain the ordinary effect refusal. -/
@[expose] def uTransition (base : UCtx) (labels : List String) (tr : STrans) : Except String UTransition := do
  if !tr.voraus.all (uTransitionAtomicFree base 10000) ||
      !tr.schritte.all (fun (p, a, b) => uTransitionAtomicFree base 10000 p &&
        uTransitionAtomicFree base 10000 a && uTransitionAtomicFree base 10000 b) then
    throw "shared atomic in a transition contract"
  let requirements := tr.voraus.map uTransitionRequirements |>.getD []
  let held ← uGehalten base.locks requirements
  let ctx := { base with held := uEindeutig held, fname := tr.tname }
  let head : UFnKopf :=
    { name := tr.tname, names := [], kinds := [], types := [], res := none, held := ctx.held }
  let effects ← uEffekte head ctx.tabs ctx.locks ctx.globs [.effs tr.wirkung]
  if !effects.locks.isEmpty then
    throw "transition lock effect has no corresponding lock action"
  let clauses ← uSeq (requirements.filterMap fun
    | .needs (.call "Held" _) => none
    | .needs p => some (uBool ctx p)
    | _ => none)
  let primitiveSource := tr.voraus.isNone && tr.wirkung.isEmpty
  let writes ← uSeq (tr.schritte.map fun (place, source, target) => do
    let place ← uTransitionPlace ctx place
    let place ← match place with
      | .relative field =>
        if primitiveSource then pure place else
        match ctx.tabs.filter (fun t => effects.puts.any (strEq · t.name) &&
            t.cols.any (fun f => strEq f.1 field)) with
        | [table] => pure (.slot table.name field (.param "#transitionIndex"))
        | [] => throw "transition store omitted from declared effects"
        | _ => throw "relative transition field has ambiguous target scope"
      | place => pure place
    let source ← uTransitionEndpoint ctx labels source
    let target ← uTransitionEndpoint ctx labels target
    pure ({ place, source, target } : UTransitionWrite))
  let primitive := tr.voraus.isNone && tr.wirkung.isEmpty &&
    writes.length == 1 &&
    writes.all (fun w => match w.place, w.source, w.target with
      | .relative _, .lit _, .lit _ => true
      | _, _, _ => false)
  if !primitive && !writes.all (fun w => uTransitionPermission effects.puts effects.gputs w.place) then
    throw "transition store omitted from declared effects"
  if !writes.isEmpty && tr.wirkung.any (fun | .pure => true | _ => false) then
    throw "pure transition declares a store"
  pure { name := tr.tname, writes, clause := clauses.foldr UEns.and .tru,
    held := ctx.held, puts := uEindeutig effects.puts, gputs := uEindeutig effects.gputs, primitive }

/-- Preserve every named declaration. Only clause-free constant symbolic
    edges enter the primitive projection; clauses never become raw shifts. -/
@[expose] def uZustand (n : String) (ts : List STrans) (ctx : UCtx) : Except String UZustand := do
  if (uEindeutig (ts.map (·.tname))).length != ts.length then
    throw "duplicate transition name in a state"
  let labels ← uStufenNamen (ts.flatMap (·.schritte)) []
    (ctx.globs.map (·.name) ++ ctx.lits.map (·.1))
  let transitions ← uSeq (ts.map (uTransition ctx labels))
  let pairs := transitions.flatMap fun tr =>
    if tr.primitive then tr.writes.filterMap fun w =>
      match w.source, w.target with
      | .lit a, .lit b => some (a, b)
      | _, _ => none
    else []
  pure { name := n, stufen := labels, paare := pairs, transitions }

end Gabbro.Grammatik.Parser.Uebersetze
