module

public import Grammatik.Parser.SourceFolds.Range

@[expose] public section
namespace Gabbro.Grammatik.Parser.SourceFolds

/-- Range folds in positions the statement hoist does not cover (contract and
    cost clauses, constant initializers, type bounds and lengths, traverse and
    lock headers) refuse instead of reaching another fold path. Value positions
    of statements are hoisted by `hoistAnw` before this visitor runs. -/
private def expression (expr : SExpr) : Except String SExpr :=
  match expr with
  | .ext .foldAdd (_ :: "range" :: _) _ | .ext .foldMin (_ :: "range" :: _) _ |
    .ext .foldMax (_ :: "range" :: _) _ | .ext .foldAnd (_ :: "range" :: _) _ |
    .ext .foldOr (_ :: "range" :: _) _ =>
    .error "fold range: range folds are not supported in this position"
  | expr => .ok expr

/-- Every fold binder tagged in the expression, for the freshness gate. Tags
    only ever cover range nodes, so the match always succeeds here. -/
def tagBinders (tags : List (SExpr × Nat)) : List String :=
  tags.filterMap fun p => match matchFoldNode p.1 with
    | some (_, binder, _) => some binder
    | none => none

/-- Hoist every range fold in the given expressions (left to right) into prefix
    accumulator loops. The tags cover the whole list, so generated bindings are
    distinct across the list; the freshness gate rejects any collision with the
    surrounding names before anything is emitted. -/
def hoistList (source : List SItemTief) (locals : Spec.Locals)
    (es : List SExpr) : Except String (List SExpr × List SAnw) := do
  let tags := (tagFoldNodesList es 0).1
  if hasRangeFoldList es then do
    if hasDuplicateTags tags then throw "fold range: duplicate nested fold"
    let used := locals.map Prod.fst ++ es.flatMap (Oeffentlich.namenA []) ++
      tagBinders tags ++ (Spec.functionHeads source).map (·.name)
    if (reservedNames tags.length).any (used.contains ·) then
      throw "fold: generated binding collision"
    let pairs ← es.mapM (expandNested 32 source locals [] tags)
    pure (pairs.map Prod.fst, (pairs.map Prod.snd).flatten)
  else pure (es, [])

/-- Hoist the single expression, for statement positions with one operand. -/
def hoistOne (source : List SItemTief) (locals : Spec.Locals)
    (e : SExpr) : Except String (SExpr × List SAnw) := do
  let (es, prefix) ← hoistList source locals [e]
  match es with
  | [e'] => pure (e', prefix)
  | _ => throw "fold range: hoist shape"

/-- Hoist the two operands in order, for places assigned from values. -/
def hoistPair (source : List SItemTief) (locals : Spec.Locals)
    (a b : SExpr) : Except String (SExpr × SExpr × List SAnw) := do
  let (es, prefix) ← hoistList source locals [a, b]
  match es with
  | [a', b'] => pure (a', b', prefix)
  | _ => throw "fold range: hoist shape"

/-- Wrap the rewritten statement after its prefix. With an empty prefix the
    statement is returned unchanged, so fold-free sources keep their exact
    shape; otherwise the prefix runs first, in order, and the rewritten
    statement reads only the fresh result variables. -/
def afterPrefix (s : SAnw) (prefix : List SAnw) : SAnw :=
  match prefix with
  | [] => s
  | _ => .block (prefix ++ [s]) none

/-- Expand a range fold outside a direct return to a fresh local accumulator
    loop before the statement. The prefix evaluates the folds' loops in
    left-to-right source order; the rewritten statement only reads the fresh
    result variables, which the lexical gate keeps distinct from every
    surrounding name (`$` is not a surface name character, so no written read
    can observe them). Direct returns keep the existing `returnFold` shape;
    traverse and lock headers stay refused. Sub-statements are left for the
    recursive walker pass. -/
def hoistAnw (source : List SItemTief) (locals : Spec.Locals)
    (result : Option STyp) : SAnw → Except String SAnw
  | .ret (some e) =>
    match matchFoldNode e with
    | some _ => returnFold source locals result (.ret (some e))
    | none => do
      let (e', prefix) ← hoistOne source locals e
      pure (afterPrefix (.ret (some e')) prefix)
  | .bind b n t e => do
    let (e', prefix) ← hoistOne source locals e
    pure (afterPrefix (.bind b n t e') prefix)
  | .bindQ b n t e => do
    let (e', prefix) ← hoistOne source locals e
    pure (afterPrefix (.bindQ b n t e') prefix)
  | .bindElse n t e why body => do
    let (e', prefix) ← hoistOne source locals e
    pure (afterPrefix (.bindElse n t e' why body) prefix)
  | .bindAxiomOpt n t e => do
    let (e', prefix) ← hoistOne source locals e
    pure (afterPrefix (.bindAxiomOpt n t e') prefix)
  | .bindAxiomOptElse n t e why body => do
    let (e', prefix) ← hoistOne source locals e
    pure (afterPrefix (.bindAxiomOptElse n t e' why body) prefix)
  | .await n t e p => do
    let (e', prefix) ← hoistOne source locals e
    pure (afterPrefix (.await n t e' p) prefix)
  | .swap n t e p => do
    let (e', prefix) ← hoistOne source locals e
    pure (afterPrefix (.swap n t e' p) prefix)
  | .set a op b => do
    let (a', b', prefix) ← hoistPair source locals a b
    pure (afterPrefix (.set a' op b') prefix)
  | .shift e a b => do
    let (e', prefix) ← hoistOne source locals e
    pure (afterPrefix (.shift e' a b) prefix)
  | .trim e n body => do
    let (e', prefix) ← hoistOne source locals e
    pure (afterPrefix (.trim e' n body) prefix)
  | .trimReq e n => do
    let (e', prefix) ← hoistOne source locals e
    pure (afterPrefix (.trimReq e' n) prefix)
  | .free e => do
    let (e', prefix) ← hoistOne source locals e
    pure (afterPrefix (.free e') prefix)
  | .call name args => do
    let (args', prefix) ← hoistList source locals args
    pure (afterPrefix (.call name args') prefix)
  | .callQ name args => do
    let (args', prefix) ← hoistList source locals args
    pure (afterPrefix (.callQ name args') prefix)
  | .callIndElse pointer args reason body => do
    let (operands, prefix) ← hoistList source locals (pointer :: args)
    match operands with
    | pointer' :: args' => pure (afterPrefix (.callIndElse pointer' args' reason body) prefix)
    | [] => throw "fold range: hoist shape"
  | .callElse name args reason body => do
    let (args', prefix) ← hoistList source locals args
    pure (afterPrefix (.callElse name args' reason body) prefix)
  | .genericCall name words args => do
    let (args', prefix) ← hoistList source locals args
    pure (afterPrefix (.genericCall name words args') prefix)
  | .cond c body arms other => do
    let (c', prefix) ← hoistOne source locals c
    pure (afterPrefix (.cond c' body arms other) prefix)
  | .elsif c body => do
    let (c', prefix) ← hoistOne source locals c
    pure (afterPrefix (.elsif c' body) prefix)
  | .cases g arms => do
    let (g', prefix) ← hoistOne source locals g
    pure (afterPrefix (.cases g' arms) prefix)
  | .alloc b n t a e body => do
    let (e', prefix) ← hoistOne source locals e
    pure (afterPrefix (.alloc b n t a e' body) prefix)
  | .reset n r => do
    let (es, prefix) ← hoistList source locals (r.toList.flatMap fun p => [p.1, p.2])
    match es with
    | [] => pure (afterPrefix (.reset n r) prefix)
    | [a', b'] => pure (afterPrefix (.reset n (some (a', b'))) prefix)
    | _ => throw "fold range: hoist shape"
  | .grow n e body => do
    let (e', prefix) ← hoistOne source locals e
    pure (afterPrefix (.grow n e' body) prefix)
  | .emit a b p => do
    let (a', b', prefix) ← hoistPair source locals a b
    pure (afterPrefix (.emit a' b' p) prefix)
  | .bindLib b n t c => do
    let (args', prefix) ← hoistList source locals c.args
    pure (afterPrefix (.bindLib b n t { c with args := args' }) prefix)
  | .lcall c => do
    let (args', prefix) ← hoistList source locals c.args
    pure (afterPrefix (.lcall { c with args := args' }) prefix)
  | s => pure s

/-- Reuse the shared lexical visitor before generic checks and before spec resolution.
    Symbolic N is compared to the symbolic array length; instantiation substitutes
    both through the existing constant-parameter machinery. Range folds in value
    positions expand where they stand; every other position still refuses. -/
def prepare (source : List SItemTief) : Except String (List SItemTief) :=
  let walk : Spec.Walk := { source, instantiate := false, resolveSpecs := false,
    statementRewrite := hoistAnw source,
    exprRewrite := fun _ _ e => expression e }
  source.mapM (walk.item 100000)

end Gabbro.Grammatik.Parser.SourceFolds
