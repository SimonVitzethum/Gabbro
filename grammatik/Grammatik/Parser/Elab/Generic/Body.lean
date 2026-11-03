module
public import Grammatik.Parser.Elab.Generic.Rewrite
@[expose] public section
namespace Gabbro.Grammatik.Parser.Generic

/-- Every statement retains its shape; only types, expressions and pending direct calls change. -/
mutual
def rewriteBody (env : Environment) (bindings : Bindings) : SAnw → RewriteM SAnw
  | .bind mu n ty value => return .bind mu n (← ty.mapM (rewriteType env bindings))
      (← rewriteExpression env bindings value)
  | .bindQ mu n ty value => return .bindQ mu n (← ty.mapM (rewriteType env bindings))
      (← rewriteExpression env bindings value)
  | .callElse name args reason body => do
    let .call target values ← rewriteExpression env bindings (.call name args) |
      liftResult (.error "foreign statement did not produce a direct call")
    return .callElse target values reason (← rewriteBody env (bindings.filter (fun p => !strEq p.1 reason)) body)
  | .callQ name args => do
    match ← rewriteExpression env bindings (.call name args) with
    | .call target values => pure (.callQ target values)
    | _ => liftResult (.error "reason statement did not produce a direct call")
  | .bindElse n ty value reason body => return .bindElse n (← ty.mapM (rewriteType env bindings))
      (← rewriteExpression env bindings value) reason (← rewriteBody env bindings body)
  | .bindAxiomOpt n ty value => return .bindAxiomOpt n (← ty.mapM (rewriteType env bindings))
      (← rewriteExpression env bindings value)
  | .bindAxiomOptElse n ty value reason body => return .bindAxiomOptElse n
      (← ty.mapM (rewriteType env bindings)) (← rewriteExpression env bindings value) reason
      (← rewriteBody env bindings body)
  | .bindLib mu n ty call => return .bindLib mu n (← ty.mapM (rewriteType env bindings))
      { call with args := ← call.args.mapM (rewriteExpression env bindings) }
  | .set place op value => return .set (← rewriteExpression env bindings place) op
      (← rewriteExpression env bindings value)
  | .shift place before after => return .shift (← rewriteExpression env bindings place) before after
  | .genericCall name words args => do
    if env.deferApplications then
      return .genericCall name (← liftResult (words.mapM (substituteArgument bindings)))
        (← args.mapM (rewriteExpression env bindings))
    match ← rewriteExpression env bindings (.ext .instantiate (name :: words) args) with
    | .call n values => pure (.call n values)
    | .ext .instantiate (n :: words) args => pure (.genericCall n words args)
    | _ => liftResult (.error "generic statement did not produce a direct call")
  | .call name args => do
    match ← rewriteExpression env bindings (.call name args) with
    | .call n values => pure (.call n values)
    | _ => liftResult (.error "ordinary statement did not produce a direct call")
  | .lcall call => return .lcall { call with args := ← call.args.mapM (rewriteExpression env bindings) }
  | .cond c yes branches no => return .cond (← rewriteExpression env bindings c)
      (← rewriteBody env bindings yes) (← branches.mapM (rewriteBody env bindings))
      (← no.mapM (rewriteBody env bindings))
  | .elsif c body => return .elsif (← rewriteExpression env bindings c) (← rewriteBody env bindings body)
  | .cases value arms => return .cases (← rewriteExpression env bindings value)
      (← arms.mapM (rewriteBody env bindings))
  | .arm tag binder body => return .arm tag binder
      (← rewriteBody env (bindings.without binder.toList) body)
  | .each binder start domain subject mode raw invariant body =>
    return .each binder (← start.mapM (rewriteExpression env bindings)) domain
      (← rewriteExpression env bindings subject) mode
      (← liftResult (substituteRaw (bindings.without [binder]) raw))
      (← invariant.mapM (rewriteExpression env (bindings.without [binder])))
      (← rewriteBody env (bindings.without [binder]) body)
  | .retry label body => return .retry label (← rewriteBody env bindings body)
  | .loop label body => return .loop label (← rewriteBody env bindings body)
  | .waive reasons body => return .waive reasons (← rewriteBody env bindings body)
  | .trimReq e tag => return .trimReq (← rewriteExpression env bindings e) tag
  | .trim e tag body => return .trim (← rewriteExpression env bindings e) tag (← rewriteBody env bindings body)
  | .locks shared lock body => return .locks shared (← rewriteExpression env bindings lock)
      (← rewriteBody env bindings body)
  | .watch duty body => return .watch duty (← rewriteBody env bindings body)
  | .emit place value payload => return .emit (← rewriteExpression env bindings place)
      (← rewriteExpression env bindings value) payload
  | .await n ty e payload => return .await n (← ty.mapM (rewriteType env bindings))
      (← rewriteExpression env bindings e) payload
  | .swap n ty e mode => return .swap n (← ty.mapM (rewriteType env bindings))
      (← rewriteExpression env bindings e) mode
  | .ret value => return .ret (← value.mapM (rewriteExpression env bindings))
  | .alloc mu n ty arena count no => return .alloc mu n (← ty.mapM (rewriteType env bindings)) arena
      (← rewriteExpression env bindings count) (← no.mapM (rewriteBody env bindings))
  | .reset arena span => do
    let span ← span.mapM fun (start, count) => do
      pure (← rewriteExpression env bindings start, ← rewriteExpression env bindings count)
    pure (.reset arena span)
  | .grow arena count body => return .grow arena (← rewriteExpression env bindings count)
      (← rewriteBody env bindings body)
  | .free place => return .free (← rewriteExpression env bindings place)
  | .child body => return .child (← rewriteBody env bindings body)
  | .start names =>
    if names.any (fun name => env.declarations.any (fun p => strEq p.1.name name && !p.1.generics.isEmpty))
    then liftResult (.error "generic start requires an ordinary wrapper") else pure (.start names)
  | .block statements ending => do
    let (statements, final) ← rewriteStatements env bindings statements
    let ending ← ending.mapM fun
      | .ret value => return .ret (← value.mapM (rewriteExpression env final))
      | ending => pure ending
    pure (.block statements ending)
  | .allocVon mu n ty arena => return .allocVon mu n (← ty.mapM (rewriteType env bindings)) arena
  | statement => pure statement

def rewriteStatements (env : Environment) (bindings : Bindings) :
    List SAnw → RewriteM (List SAnw × Bindings)
  | [] => pure ([], bindings)
  | statement :: rest => do
    let rewritten ← rewriteBody env bindings statement
    let names := match statement with
      | .bind _ n _ _ | .bindQ _ n _ _ | .bindElse n _ _ _ _ | .bindAxiomOpt n _ _ | .bindAxiomOptElse n _ _ _ _ |
        .bindLib _ n _ _ | .alloc _ n _ _ _ _ |
        .allocVon _ n _ _ | .await n _ _ _ | .swap n _ _ _ => [n]
      | _ => []
    let (tail, final) ← rewriteStatements env (bindings.without names) rest
    pure (rewritten :: tail, final)
end

/-- Instantiate the complete declaration and collect its rewritten dependencies in the same pass. -/
def instantiate (env : Environment) (key : Instance) :
    Except String (((FnSig × SAnw) × List (FnSig × SAnw) × List (STyp × String)) ×
      List Instance) := do
  let (sig, body) ← declaration env key.function
  let (_, bindings) ← normalizeArguments env {} sig.generics key.arguments {}
  (do
    let sig' ← rewriteSignature env bindings sig
    let body' ← rewriteBody env (bindings.without (sig.params.map Prod.fst)) body
    -- Literal bodies have no access to the instance's runtime or translation-time binders.
    -- Their own generic calls still contribute to the same closed instance dependency graph.
    let literals ← bindings.literals.mapM fun (literalSig, literalBody) => do
      pure (← rewriteSignature env {} literalSig, ← rewriteBody env {} literalBody)
    pure (({ sig' with name := instanceName key }, body'), literals, bindings.requirements)).run []

end Gabbro.Grammatik.Parser.Generic
