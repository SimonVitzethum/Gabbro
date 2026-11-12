module

public import Grammatik.Parser.Spec.Resolve
public import Grammatik.Parser.Namen.References
public import Grammatik.Parser.Lex.Tafel

@[expose] public section

namespace Gabbro.Grammatik.Parser.Spec

/-- One traversal serves instantiation and the output-form validator. In validation mode,
    abstract calls, explicit arguments, effect parameters and group items are refused. -/
structure Walk where
  source : List SItemTief
  instantiate : Bool
  /-- Earlier front-end passes share the traversal and defer spec-call resolution. -/
  resolveSpecs : Bool := true
  typeRewrite : STyp → Except String STyp := Except.ok
  exprRewrite : Locals → Option STyp → SExpr → Except String SExpr := fun _ _ e => .ok e
  statementCheck : Locals → SAnw → Except String Unit := fun _ _ => .ok ()
  /-- Source sugar is expanded before the same visitor checks its ordinary statements. -/
  statementRewrite : Locals → Option STyp → SAnw → Except String SAnw := fun _ _ s => .ok s
  rawCheck : Locals → String → Except String Unit := fun _ _ => .ok ()
  /-- Earlier checks may infer symbolic template results before concrete spec resolution. -/
  infer : Locals → SExpr → Option STyp := fun _ _ => none
  expected : Option STyp := none
  result : Option STyp := none
  /-- What type inference reads from the materialized source, built once per walk (default only). -/
  umfeld : Umfeld := Umfeld.von (materialize source)
  /-- The spec groups of the source, computed once per walk (default only). -/
  specGroups : List Group := groups source

def Walk.call (w : Walk) (locals : Locals) (name : String)
    (types : Option (List STyp)) (args : List SExpr) : Except String String := do
  if !w.resolveSpecs then return name
  if w.instantiate then resolveCallWith w.specGroups w.source locals name types args
  else if types.isSome || w.specGroups.any (fun g => name.startsWith (g.name ++ "::")) then
    .error "spec.output.call"
  else .ok name

mutual
def Walk.expr (w : Walk) (locals : Locals) : Nat → SExpr → Except String SExpr
  | 0, _ => .error "spec.expansion.fuel"
  | f + 1, e => do
    let recur := { w with expected := none }.expr locals f
    let e ← (do
      match e with
      | .call name args => do
        let signature := w.umfeld.heads.finde name
        let args ← args.zipIdx.mapM fun (arg, index) => do
          let expected := signature.bind fun s => (s.params[index]?).map Prod.snd
          { w with expected }.expr locals f arg
        return .call (← w.call locals name none args) args
      | .ext .dyn ns args => do
        if w.resolveSpecs then throw "dyn.unexpanded-producer"
        return .ext .dyn ns (← args.mapM recur)
      | .ext .instantiate (name :: words) args => do
        if !w.resolveSpecs then return .ext .instantiate (name :: words) (← args.mapM recur)
        let types ← explicitTypes (String.intercalate ", " words)
        let args ← args.mapM recur
        return .call (← w.call locals name (some types) args) args
      | .ext .instantiate [] _ => do throw "spec.call.arguments"
      | .field x n => do
        let x ← recur x
        match x with
        | .index (.variable table) i =>
          if w.resolveSpecs && !(locals.any fun p => strEq p.1 table) && w.source.any (fun
              | .tableT t _ _ _ _ _ _ _ => strEq t table
              | _ => false) then
            return .field (.index (.field (.variable table) "slots") i) n
          else return .field x n
        | _ => return .field x n
      | .index x i => do return .index (← recur x) (← recur i)
      | .arrow x n => do return .arrow (← recur x) n
      | .un op x => do return .un op (← recur x)
      | .bin op a b => do return .bin op (← recur a) (← recur b)
      | .built n args => do return .built n (← args.mapM recur)
      | .old x => do return .old (← recur x)
      | .ext k (x :: "slots" :: ns) args => do
        let locals := match args.head? with
          | some (.variable t) => (x, STyp.index false t) :: locals
          | _ => locals
        return .ext k (x :: "slots" :: ns) (← args.mapM (w.expr locals f))
      | .ext k ns args => do return .ext k ns (← args.mapM recur)
      | e => do return e)
    w.exprRewrite locals w.expected e
end

/-- Even a leaf reaches the configured expression rewrite or refusal. -/
theorem Walk.expr_literal (w : Walk) (locals : Locals) (fuel n : Nat) :
    w.expr locals (fuel + 1) (.lit n) = w.exprRewrite locals w.expected (.lit n) := rfl

def Walk.type (w : Walk) (locals : Locals) : Nat → STyp → Except String STyp
  | 0, _ => .error "spec.expansion.fuel"
  | f + 1, t => do
    let t ← (do
      match t with
      | .dyn n raw => do
        if w.resolveSpecs then throw "dyn.unexpanded-type"
        return .dyn n raw
      | .ptr s r t => do return .ptr s r (← w.type locals f t)
      | .range t lo hi b => do return .range (← w.type locals f t) (← w.expr locals f lo) (← w.expr locals f hi) b
      | .array t n => do return .array (← w.type locals f t) (← w.expr locals f n)
      | .wrap t => do return .wrap (← w.type locals f t)
      | .embed t p s => do return .embed (← w.type locals f t) p (← s.mapM (w.expr locals f))
      | .str n => do return .str (← w.expr locals f n)
      | .entry ps r => do return .entry ps (← r.mapM (w.type locals f))
      | t => do return t)
    w.typeRewrite t

/-- Even a named type reaches the configured type rewrite or refusal. -/
theorem Walk.type_atom (w : Walk) (locals : Locals) (fuel : Nat) (name : String) :
    w.type locals (fuel + 1) (.atom name) = w.typeRewrite (.atom name) := rfl

def Walk.effects (w : Walk) (locals : Locals) (es : List SEffekt) : Except String (List SEffekt) := do
  let es ← if !w.resolveSpecs then pure es
    else if w.instantiate then expandEffects w.source (groups w.source) (instances w.source) [] [] 1000 es
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
def bindings (U : Umfeld) (locals : Locals)
    (infer : Locals → SExpr → Option STyp) : SAnw → Locals
  | .bind _ n t e | .bindQ _ n t e | .bindElse n t e _ _ | .bindAxiomOpt n t e | .bindAxiomOptElse n t e _ _ =>
    match t.orElse (fun _ => (infer locals e).orElse (fun _ => inferTypeMit U locals 128 e)) with
    | some ty => [(n, ty)]
    | none => []
  | .await n t _ _ | .swap n t _ _ => (t.map fun ty => [(n, ty)]).getD []
  | .alloc _ n t _ _ _ | .allocVon _ n t _ => (t.map fun ty => [(n, ty)]).getD []
  | _ => []

/-- Whether the characters `needle` occur in `text`. Structural over the characters, so the kernel
    reduces it (`String.splitOn` does not). -/
def zeichenInfix (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | c :: rest => needle.isPrefixOf (c :: rest) || zeichenInfix needle rest

/-- Raw headers have their own ordinary elaborators. Refuse an abstract call hidden there. -/
def Walk.raw (w : Walk) (s : String) (locals : Locals := []) : Except String String := do
  w.rawCheck locals s
  let compact := s.toList.filter fun c => c != ' ' && c != '\t' && c != '\n' && c != '\r'
  if w.resolveSpecs && w.specGroups.any (fun g => zeichenInfix (g.name ++ "::").toList compact) then
    .error "spec.call.raw.header"
  else .ok s

/-- A match payload binder receives the existing case's concrete type. This serves static
    spec inference and tagged dispatch alike, without a separate statement walker. -/
def matchBindings (items : List SItemTief) (locals : Locals) (value : SExpr) : SAnw → Locals
  | .arm caseName (some binder) _ =>
    let payload : Option STyp := do
      let .atom sumName ← inferType (materialize items) locals 128 value | none
      let schemas ← (Uebersetze.uSumSchemas (items.map fun
        | .taggedByT decl _ => decl | it => it)).toOption
      let schema ← schemas.find? (fun s => strEq s.name sumName)
      let variant ← schema.cases.find? (fun c => strEq c.1 caseName)
      variant.2
    payload.toList.map (fun ty => (binder, ty))
  | _ => []

mutual
def Walk.statement (w : Walk) (locals : Locals) : Nat → SAnw → Except String SAnw
  | 0, _ => .error "spec.expansion.fuel"
  | f + 1, s => do
    let s ← w.statementRewrite locals w.result s
    w.statementCheck locals s
    let ex := { w with expected := none }.expr locals f
    let ty := w.type locals f
    let st := w.statement locals f
    match s with
    | .bind b n t e =>
      let t ← t.mapM ty
      return .bind b n t (← { w with expected := t }.expr locals f e)
    | .bindQ b n t e =>
      let t ← t.mapM ty
      return .bindQ b n t (← { w with expected := t }.expr locals f e)
    | .callIndElse pointer args reason body =>
      return .callIndElse (← ex pointer) (← args.mapM ex) reason
        (← w.statement (locals.filter (fun p => !strEq p.1 reason)) f body)
    | .callElse name args reason body =>
      let .call name args ← ex (.call name args) | throw "spec.statement.call"
      return .callElse name args reason (← w.statement (locals.filter (fun p => !strEq p.1 reason)) f body)
    | .callQ name args =>
      let .call name args ← ex (.call name args) | throw "spec.statement.call"
      return .callQ name args
    | .bindElse n t e why body =>
      let t ← t.mapM ty
      return .bindElse n t (← { w with expected := t }.expr locals f e) why (← st body)
    | .bindLib b n t c =>
      let t ← t.mapM ty
      return .bindLib b n t { c with args := ← c.args.mapM ex }
    | .lcall c => return .lcall { c with args := ← c.args.mapM ex }
    | .bindAxiomOpt n t e =>
      let t ← t.mapM ty
      return .bindAxiomOpt n t (← { w with expected := t }.expr locals f e)
    | .bindAxiomOptElse n t e why body =>
      let t ← t.mapM ty
      return .bindAxiomOptElse n t (← { w with expected := t }.expr locals f e) why (← st body)
    | .set a op b =>
      let a ← ex a
      let expected ← (inferTypeMit w.umfeld locals 128 a).mapM ty
      return .set a op (← { w with expected }.expr locals f b)
    | .shift e a b => return .shift (← ex e) a b
    | .call name args =>
      let .call name args ← ex (.call name args) | throw "spec.statement.call"
      return .call name args
    | .genericCall name words args =>
      let e ← ex (.ext .instantiate (name :: words) args)
      match e with
      | .call target values => return .call target values
      | .ext .instantiate (target :: arguments) values => return .genericCall target arguments values
      | _ => throw "spec.statement.call"
    | .cond e body arms other => return .cond (← ex e) (← st body) (← arms.mapM st) (← other.mapM st)
    | .elsif e body => return .elsif (← ex e) (← st body)
    | .cases e arms =>
      let e ← ex e
      w.statementCheck locals (.cases e arms)
      let arms ← arms.mapM fun arm =>
        w.statement (matchBindings w.source locals e arm ++ locals) f arm
      return .cases e arms
    | .arm c n body => return .arm c n (← st body)
    | .each n start kind subject mode raw inv body =>
      let inner := match subject with
        | .variable t => (n, STyp.index false t) :: locals
        | _ => locals
      return .each n (← start.mapM ex) kind (← ex subject) mode (← w.raw raw locals)
        (← inv.mapM (w.expr inner f)) (← w.statement inner f body)
    | .retry raw body => return .retry (← w.raw raw locals) (← st body)
    | .loop raw body => return .loop (← w.raw raw locals) (← st body)
    | .waive ns body => return .waive ns (← st body)
    | .trimReq e n => return .trimReq (← ex e) n
    | .trim e n body => return .trim (← ex e) n (← st body)
    | .locks b e body => return .locks b (← ex e) (← st body)
    | .watch n body => return .watch n (← st body)
    | .emit a b p => return .emit (← ex a) (← ex b) p
    | .await n t e p => return .await n (← t.mapM ty) (← ex e) p
    | .swap n t e p => return .swap n (← t.mapM ty) (← ex e) p
    | .ret e => return .ret (← e.mapM ({ w with expected := w.result }.expr locals f))
    | .alloc b n t a e body => return .alloc b n (← t.mapM ty) a (← ex e) (← body.mapM st)
    | .allocVon b n t a => return .allocVon b n (← t.mapM ty) a
    | .reset n es => return .reset n (← es.mapM fun (a, b) => return (← ex a, ← ex b))
    | .grow n e body => return .grow n (← ex e) (← st body)
    | .free e => return .free (← ex e)
    | .child body => return .child (← st body)
    | .block ss ending =>
      let (ss, env) ← w.statements locals f ss
      match ending with
      | some (.ret e) =>
        match ← w.statement env f (.ret e) with
        | .ret e => return .block ss (some (.ret e))
        | .block beforeReturn ending => return .block (ss ++ beforeReturn) ending
        | tail => return .block (ss ++ [tail]) none
      | ending => return .block ss ending
    | .other raw => return .other (← w.raw raw locals)
    | s => return s

def Walk.statements (w : Walk) (locals : Locals) : Nat → List SAnw → Except String (List SAnw × Locals)
  | 0, _ => .error "spec.expansion.fuel"
  | _ + 1, [] => .ok ([], locals)
  | f + 1, s :: ss => do
    let s ← w.statement locals f s
    let names := Aufloesung.gebunden s
    let locals := bindings w.umfeld locals w.infer s ++
      locals.filter (fun p => !(names.any (strEq p.1)))
    let (ss, env) ← w.statements locals f ss
    return (s :: ss, env)
end

end Gabbro.Grammatik.Parser.Spec
