module

public import Grammatik.Parser.Spec.Resolve

@[expose] public section

namespace Gabbro.Grammatik.Parser.Spec

/-- One traversal serves instantiation and the output-form validator. In validation mode,
    abstract calls, explicit arguments, effect parameters and group items are refused. -/
structure Walk where
  source : List SItemTief
  instantiate : Bool

def Walk.call (w : Walk) (locals : Locals) (name : String)
    (types : Option (List STyp)) (args : List SExpr) : Except String String := do
  let (name, types) ← match name.splitOn "::[" with
    | [n, raw] =>
      if raw.endsWith "]" && types.isNone then do
        let ts ← explicitTypes (String.ofList raw.toList.dropLast)
        pure (n, some ts)
      else throw "spec.call.arguments"
    | [_] => pure (name, types)
    | _ => throw "spec.call.arguments"
  if w.instantiate then resolveCall w.source locals name types args
  else if types.isSome || (groups w.source).any (fun g => name.startsWith (g.name ++ "::")) then
    .error "spec.output.call"
  else .ok name
mutual
def Walk.expr (w : Walk) (locals : Locals) : Nat → SExpr → Except String SExpr
  | 0, _ => .error "spec.expansion.fuel"
  | f + 1, e => do
    let recur := w.expr locals f
    match e with
    | .call name args =>
      let args ← args.mapM recur
      return .call (← w.call locals name none args) args
    | .ext .inst [name, raw] args =>
      let types ← explicitTypes raw
      let args ← args.mapM recur
      return .call (← w.call locals name (some types) args) args
    | .ext .inst _ _ => throw "spec.call.arguments"
    | .field x n => return .field (← recur x) n
    | .index x i => return .index (← recur x) (← recur i)
    | .arrow x n => return .arrow (← recur x) n
    | .un op x => return .un op (← recur x)
    | .bin op a b => return .bin op (← recur a) (← recur b)
    | .built n args => return .built n (← args.mapM recur)
    | .old x => return .old (← recur x)
    | .ext k (x :: "slots" :: ns) args =>
      let locals := match args.head? with
        | some (.variable t) => (x, STyp.index false t) :: locals
        | _ => locals
      return .ext k (x :: "slots" :: ns) (← args.mapM (w.expr locals f))
    | .ext k ns args => return .ext k ns (← args.mapM recur)
    | e => return e
end

def Walk.type (w : Walk) (locals : Locals) : Nat → STyp → Except String STyp
  | 0, _ => .error "spec.expansion.fuel"
  | f + 1, t => do
    match t with
    | .ptr s r t => return .ptr s r (← w.type locals f t)
    | .range t lo hi b => return .range (← w.type locals f t) (← w.expr locals f lo) (← w.expr locals f hi) b
    | .array t n => return .array (← w.type locals f t) (← w.expr locals f n)
    | .wrap t => return .wrap (← w.type locals f t)
    | .embed t p s => return .embed (← w.type locals f t) p (← s.mapM (w.expr locals f))
    | .str n => return .str (← w.expr locals f n)
    | .entry ps r => return .entry ps (← r.mapM (w.type locals f))
    | t => return t

def Walk.effects (w : Walk) (locals : Locals) (es : List SEffekt) : Except String (List SEffekt) := do
  let es ← if w.instantiate then expandEffects w.source (groups w.source) (instances w.source) [] [] 1000 es
    else if es.any (fun | .param _ | .instanceEffects _ _ => true | _ => false) then throw "spec.output.effects"
    else pure es
  es.mapM fun e => match e with
    | .reads p => return .reads (← w.expr locals 1000 p)
    | .writes p => return .writes (← w.expr locals 1000 p)
    | .locks b p => return .locks b (← w.expr locals 1000 p)
    | .takes p => return .takes (← w.expr locals 1000 p)
    | .posts p => return .posts (← w.expr locals 1000 p)
    | e => pure e

def Walk.clause (w : Walk) (locals : Locals) : SKlausel → Except String SKlausel
  | .needs p => return .needs (← w.expr locals 1000 p)
  | .gives p => return .gives (← w.expr locals 1000 p)
  | .cost p => return .cost (← w.expr locals 1000 p)
  | .drops p => return .drops (← w.expr locals 1000 p)
  | .effs es => return .effs (← w.effects locals es)
  | k => pure k

def Walk.signature (w : Walk) (s : FnSig) : Except String FnSig := do
  let params ← s.params.mapM fun (n, t) => return (n, ← w.type [] 1000 t)
  return { s with params, res := ← s.res.mapM (w.type params 1000),
                  klauseln := ← s.klauseln.mapM (w.clause params) }

/-- New bindings affect the remainder of their block, including inferred let types. -/
def bindings (items : List SItemTief) (locals : Locals) : SAnw → Locals
  | .bind _ n t e | .bindElse n t e _ _ =>
    match t.orElse (fun _ => inferType items locals 128 e) with
    | some ty => [(n, ty)]
    | none => []
  | .await n t _ _ | .swap n t _ _ => (t.map fun ty => [(n, ty)]).getD []
  | .alloc _ n t _ _ _ | .allocVon _ n t _ => (t.map fun ty => [(n, ty)]).getD []
  | _ => []

/-- Raw headers have their own ordinary elaborators. Refuse an abstract call hidden there. -/
def Walk.raw (w : Walk) (s : String) : Except String String :=
  if (groups w.source).any (fun g => (s.splitOn (g.name ++ "::")).length > 1) then
    .error "spec.call.raw.header"
  else .ok s

mutual
def Walk.statement (w : Walk) (locals : Locals) : Nat → SAnw → Except String SAnw
  | 0, _ => .error "spec.expansion.fuel"
  | f + 1, s => do
    let ex := w.expr locals f
    let ty := w.type locals f
    let st := w.statement locals f
    match s with
    | .bind b n t e => return .bind b n (← t.mapM ty) (← ex e)
    | .bindElse n t e why body => return .bindElse n (← t.mapM ty) (← ex e) why (← st body)
    | .set a op b => return .set (← ex a) op (← ex b)
    | .shift e a b => return .shift (← ex e) a b
    | .call name args =>
      let args ← args.mapM ex
      return .call (← w.call locals name none args) args
    | .cond e body arms other => return .cond (← ex e) (← st body) (← arms.mapM st) (← other.mapM st)
    | .elsif e body => return .elsif (← ex e) (← st body)
    | .cases e arms => return .cases (← ex e) (← arms.mapM st)
    | .arm c n body => return .arm c n (← st body)
    | .each n start kind subject mode raw inv body =>
      let inner := match subject with
        | .variable t => (n, STyp.index false t) :: locals
        | _ => locals
      return .each n (← start.mapM ex) kind (← ex subject) mode (← w.raw raw)
        (← inv.mapM (w.expr inner f)) (← w.statement inner f body)
    | .retry raw body => return .retry (← w.raw raw) (← st body)
    | .loop raw body => return .loop (← w.raw raw) (← st body)
    | .waive ns body => return .waive ns (← st body)
    | .trim e n body => return .trim (← ex e) n (← st body)
    | .locks b e body => return .locks b (← ex e) (← st body)
    | .watch n body => return .watch n (← st body)
    | .emit a b p => return .emit (← ex a) (← ex b) p
    | .await n t e p => return .await n (← t.mapM ty) (← ex e) p
    | .swap n t e p => return .swap n (← t.mapM ty) (← ex e) p
    | .ret e => return .ret (← e.mapM ex)
    | .alloc b n t a e body => return .alloc b n (← t.mapM ty) a (← ex e) (← body.mapM st)
    | .allocVon b n t a => return .allocVon b n (← t.mapM ty) a
    | .reset n es => return .reset n (← es.mapM fun (a, b) => return (← ex a, ← ex b))
    | .grow n e body => return .grow n (← ex e) (← st body)
    | .free e => return .free (← ex e)
    | .child body => return .child (← st body)
    | .block ss ending =>
      let (ss, env) ← w.statements locals f ss
      let ending ← ending.mapM fun
        | .ret e => return .ret (← e.mapM (w.expr env f))
        | e => pure e
      return .block ss ending
    | s => return s

def Walk.statements (w : Walk) (locals : Locals) : Nat → List SAnw → Except String (List SAnw × Locals)
  | 0, _ => .error "spec.expansion.fuel"
  | _ + 1, [] => .ok ([], locals)
  | f + 1, s :: ss => do
    let s ← w.statement locals f s
    let locals := bindings (materialize w.source) locals s ++ locals
    let (ss, env) ← w.statements locals f ss
    return (s :: ss, env)
end

end Gabbro.Grammatik.Parser.Spec
