module
public import Grammatik.Parser.Elab.Generic.Arguments
@[expose] public section
namespace Gabbro.Grammatik.Parser.Generic

/-- Requests are collected while the same traversal rewrites calls. -/
abbrev RewriteM := StateT (List Instance) (Except String)

def liftResult {α : Type} (result : Except String α) : RewriteM α :=
  fun state => do pure (← result, state)

mutual
/-- The shared expression traversal substitutes constants and eliminates explicit applications. -/
def rewriteExpression (env : Environment) (bindings : Bindings) : SExpr → RewriteM SExpr
  | .variable n => match bindings.functions.find? (fun p => strEq p.1 n) with
    | some (_, target) => pure (.fnref target)
    | none => pure (expression bindings.values (.variable n))
  | .field e n => return .field (← rewriteExpression env bindings e) n
  | .index e i => return .index (← rewriteExpression env bindings e) (← rewriteExpression env bindings i)
  | .arrow e n => return .arrow (← rewriteExpression env bindings e) n
  | .un op e => return .un op (← rewriteExpression env bindings e)
  | .bin op a b => return .bin op (← rewriteExpression env bindings a) (← rewriteExpression env bindings b)
  | .call n args => do
    let n := ((bindings.functions.find? (fun p => strEq p.1 n)).map Prod.snd).getD n
    if env.declarations.any (fun p => strEq p.1.name n && !p.1.generics.isEmpty) then
      liftResult (.error ("generic call requires explicit ::[arguments]: " ++ n))
    else return .call n (← rewriteExpressions env bindings args)
  | .fnref n => do
    let n := ((bindings.functions.find? (fun p => strEq p.1 n)).map Prod.snd).getD n
    if env.declarations.any (fun p => strEq p.1.name n && !p.1.generics.isEmpty) then
      liftResult (.error "generic function reference requires an ordinary named instance")
    else pure (.fnref n)
  | .built n args => return .built n (← rewriteExpressions env bindings args)
  | .old e => return .old (← rewriteExpression env bindings e)
  | .ext .instantiate (n :: words) args => do
    -- Module applications and spec calls remain pending until their own expansion phase.
    if env.deferApplications || !env.declarations.any (fun p => strEq p.1.name n) then
      return .ext .instantiate (n :: (← liftResult (words.mapM (substituteArgument bindings))))
        (← rewriteExpressions env bindings args)
    let key ← liftResult (normalize env bindings n words)
    modify (fun requests => requests ++ [key])
    return .call (instanceName key) (← rewriteExpressions env bindings args)
  | .ext .instantiate [] _ => liftResult (.error "generic call without a function name")
  | .ext kind (binder :: domain :: names) args => do
    let args ← if kind == .all || kind == .any || kind == .count then
      rewriteQuantifierOperands env bindings binder args
      else rewriteExpressions env bindings args
    pure (.ext kind (binder :: domain :: names) args)
  | .ext k ns args => return .ext k ns (← rewriteExpressions env bindings args)
  | e => pure e
termination_by structural e => e

/-- Rewrite each operand left to right, retaining request and error order. -/
def rewriteExpressions (env : Environment) (bindings : Bindings) : List SExpr → RewriteM (List SExpr)
  | [] => pure []
  | e :: rest => return (← rewriteExpression env bindings e) :: (← rewriteExpressions env bindings rest)
termination_by structural es => es

/-- Only the last operand is under a quantifier's binder; domain operands use the outer scope. -/
def rewriteQuantifierOperands (env : Environment) (bindings : Bindings) (binder : String) :
    List SExpr → RewriteM (List SExpr)
  | [] => pure []
  | [body] => return [← rewriteExpression env (bindings.without [binder]) body]
  | operand :: rest => return (← rewriteExpression env bindings operand) ::
      (← rewriteQuantifierOperands env bindings binder rest)
termination_by structural es => es
end

/-- The structural traversal agrees with the original mapM traversal. -/
theorem rewriteExpressions_eq_mapM (env : Environment) (bindings : Bindings) (es : List SExpr) :
    rewriteExpressions env bindings es = es.mapM (rewriteExpression env bindings) := by
  induction es with
  | nil => rfl
  | cons head rest ih => simp only [rewriteExpressions, List.mapM_cons, ih]

mutual
/-- Type bounds may themselves contain constants or calls; use the same expression traversal. -/
def rewriteType (env : Environment) (bindings : Bindings) : STyp → RewriteM STyp
  | .atom n => pure (surfaceType bindings.types bindings.values (.atom n))
  | .tuple types => return .tuple (← rewriteTypes env bindings types)
  | .ptr space rights ty => return .ptr space rights (← rewriteType env bindings ty)
  | .range ty lo hi ex => do
    return .range (← rewriteType env bindings ty)
      (← rewriteExpression env bindings lo) (← rewriteExpression env bindings hi) ex
  | .array ty count => return .array (← rewriteType env bindings ty) (← rewriteExpression env bindings count)
  | .wrap ty => return .wrap (← rewriteType env bindings ty)
  | .embed ty bits scale => do
    return .embed (← rewriteType env bindings ty) bits
      (← scale.mapM (rewriteExpression env bindings))
  | .str count => return .str (← rewriteExpression env bindings count)
  | .entry args none => pure (.entry args none)
  | .entry args (some result) => return .entry args (some (← rewriteType env bindings result))
  | .raw text => return .raw (← liftResult (substituteRaw bindings text))
  | ty => pure ty
termination_by structural ty => ty

/-- Rewrite tuple components in the same state and error order as ordinary operands. -/
def rewriteTypes (env : Environment) (bindings : Bindings) : List STyp → RewriteM (List STyp)
  | [] => pure []
  | ty :: rest => return (← rewriteType env bindings ty) :: (← rewriteTypes env bindings rest)
termination_by structural ts => ts
end

/-- The structural traversal agrees with the original mapM traversal. -/
theorem rewriteTypes_eq_mapM (env : Environment) (bindings : Bindings) (ts : List STyp) :
    rewriteTypes env bindings ts = ts.mapM (rewriteType env bindings) := by
  induction ts with
  | nil => rfl
  | cons head rest ih => simp only [rewriteTypes, List.mapM_cons, ih]

def rewriteEffect (env : Environment) (bindings : Bindings) : SEffekt → RewriteM SEffekt
  | .reads e => return .reads (← rewriteExpression env bindings e)
  | .writes e => return .writes (← rewriteExpression env bindings e)
  | .locks sh e => return .locks sh (← rewriteExpression env bindings e)
  | .takes e => return .takes (← rewriteExpression env bindings e)
  | .posts e => return .posts (← rewriteExpression env bindings e)
  | .instanceEffects name types => return .instanceEffects name (← types.mapM (rewriteType env bindings))
  | effect => pure effect

def rewriteClause (env : Environment) (bindings : Bindings) : SKlausel → RewriteM SKlausel
  | .needs e => return .needs (← rewriteExpression env bindings e)
  | .gives e => return .gives (← rewriteExpression env bindings e)
  | .cost e => return .cost (← rewriteExpression env bindings e)
  | .drops e => return .drops (← rewriteExpression env bindings e)
  | .effs es => return .effs (← es.mapM (rewriteEffect env bindings))
  | .induc text => return .induc (← liftResult (substituteRaw bindings text))
  | .quits text => return .quits (← liftResult (substituteRaw bindings text))
  | .limit text => return .limit (← liftResult (substituteRaw bindings text))
  | clause => pure clause

def rewriteSignature (env : Environment) (bindings : Bindings) (sig : FnSig) : RewriteM FnSig := do
  let params ← sig.params.mapM fun (name, ty) => do pure (name, ← rewriteType env bindings ty)
  let result ← sig.res.mapM (rewriteType env bindings)
  let clauses ← sig.klauseln.mapM (rewriteClause env (bindings.without (sig.params.map Prod.fst)))
  pure { sig with params, res := result, klauseln := clauses, generics := [] }

end Gabbro.Grammatik.Parser.Generic
