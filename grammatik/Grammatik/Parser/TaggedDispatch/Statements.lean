module

public import Grammatik.Parser.TaggedDispatch.Expressions

@[expose] public section
namespace Gabbro.Grammatik.Parser

def taggedBindLocal (locals : TaggedLocals) (name : String) (ty : Option STyp) : TaggedLocals :=
  ty.toList.map (fun t => (name, t)) ++ locals.filter (fun p => !strEq p.1 name)

def taggedStatementLocals (items : List SItemTief) (locals : TaggedLocals) : SAnw → TaggedLocals
  | .bind _ n ty e | .bindElse n ty e _ _ =>
    taggedBindLocal locals n (ty.orElse (fun _ => taggedExprType items locals e))
  | .bindLib _ n ty _ | .await n ty _ _ | .swap n ty _ _ => taggedBindLocal locals n ty
  | .alloc _ n ty _ _ _ | .allocVon _ n ty _ => taggedBindLocal locals n ty
  | _ => locals

/-- The payload binder of a written match has its case's declared type. -/
def taggedArmLocals (items : List SItemTief) (locals : TaggedLocals)
    (scrut : SExpr) (arm : SAnw) : TaggedLocals :=
  match arm with
  | .arm name (some binder) _ =>
    let payload := do
      let .atom sumName ← taggedExprType items locals scrut | none
      let schemas ← (Uebersetze.uSumSchemas items).toOption
      let schema ← schemas.find? (fun s => strEq s.name sumName)
      let c ← schema.cases.find? (fun c => strEq c.1 name)
      c.2
    taggedBindLocal locals binder payload
  | _ => locals

mutual
/-- Rewrite every structured expression position, retaining block-local type scope.
    Generated calls go through ordinary typing and lowering afterwards. -/
def taggedRewriteStmt (items : List SItemTief) (bindings : List TaggedBinding)
    (sources : List String) (locals : TaggedLocals) : Nat → SAnw → Except String SAnw
  | 0, _ => .error "tagged-dispatch-statement-too-deep"
  | f + 1, statement => do
    let expr := taggedRewriteExpr items bindings sources locals f
    let exprs := taggedRewriteExprs items bindings sources locals f
    let stmt := taggedRewriteStmt items bindings sources locals f
    let stmts := taggedRewriteStmts items bindings sources locals f
    match statement with
    | .block ss ender =>
      let (ss, scope) ← stmts ss
      let ender ← match ender with
        | some (.ret value) => do
          pure (some (.ret (← value.mapM (taggedRewriteExpr items bindings sources scope f))))
        | e => pure e
      pure (.block ss ender)
    | .bind m n t e => pure (.bind m n t (← expr e))
    | .bindElse n t e err body => pure (.bindElse n t (← expr e) err
        (← taggedRewriteStmt items bindings sources (taggedBindLocal locals err none) f body))
    | .bindLib m n t c => pure (.bindLib m n t { c with args := ← exprs c.args })
    | .lcall c => pure (.lcall { c with args := ← exprs c.args })
    | .call n args =>
      let args ← exprs args
      pure (.call (← taggedResolveCall items bindings sources locals n args) args)
    | .set a op b => pure (.set (← expr a) op (← expr b))
    | .shift a b c => pure (.shift (← expr a) b c)
    | .cond e yes branches no =>
      let branches ← branches.mapM stmt
      pure (.cond (← expr e) (← stmt yes) branches (← no.mapM stmt))
    | .elsif e body => pure (.elsif (← expr e) (← stmt body))
    | .cases e arms =>
      let arms ← arms.mapM fun arm =>
        taggedRewriteStmt items bindings sources (taggedArmLocals items locals e arm) f arm
      pure (.cases (← expr e) arms)
    | .arm n binder body => pure (.arm n binder (← stmt body))
    | .each n start kind domain mode raw inv body =>
      let scope := taggedBindLocal locals n none
      pure (.each n (← start.mapM expr) kind (← expr domain) mode raw
        (← inv.mapM (taggedRewriteExpr items bindings sources scope f))
        (← taggedRewriteStmt items bindings sources scope f body))
    | .retry n body => pure (.retry n (← stmt body))
    | .loop n body => pure (.loop n (← stmt body))
    | .waive ns body => pure (.waive ns (← stmt body))
    | .trim e n body => pure (.trim (← expr e) n (← stmt body))
    | .locks shared e body => pure (.locks shared (← expr e) (← stmt body))
    | .watch n body => pure (.watch n (← stmt body))
    | .emit a b order => pure (.emit (← expr a) (← expr b) order)
    | .await n t e order => pure (.await n t (← expr e) order)
    | .swap n t e order => pure (.swap n t (← expr e) order)
    | .ret value => pure (.ret (← value.mapM expr))
    | .alloc m n t arena count no =>
      pure (.alloc m n t arena (← expr count) (← no.mapM stmt))
    | .reset arena range =>
      let range ← range.mapM fun (a, b) => do pure (← expr a, ← expr b)
      pure (.reset arena range)
    | .grow arena count no => pure (.grow arena (← expr count) (← stmt no))
    | .free e => pure (.free (← expr e))
    | .child body => pure (.child (← stmt body))
    | s => pure s
def taggedRewriteStmts (items : List SItemTief) (bindings : List TaggedBinding)
    (sources : List String) (locals : TaggedLocals) : Nat → List SAnw →
    Except String (List SAnw × TaggedLocals)
  | 0, _ => .error "tagged-dispatch-statement-too-deep"
  | _ + 1, [] => .ok ([], locals)
  | f + 1, s :: ss => do
    let s ← taggedRewriteStmt items bindings sources locals f s
    let (ss, scope) ← taggedRewriteStmts items bindings sources
      (taggedStatementLocals items locals s) f ss
    pure (s :: ss, scope)
end

end Gabbro.Grammatik.Parser
