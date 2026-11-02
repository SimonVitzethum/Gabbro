module

public import Grammatik.Parser.TaggedDispatch.Resolve

@[expose] public section
namespace Gabbro.Grammatik.Parser

abbrev TaggedLocals := List (String × STyp)

/-- Type information used solely to select a generated overload. Ordinary typing
    remains with the elaborator; an unresolved receiver refuses rather than guesses. -/
def taggedExprType (items : List SItemTief) (locals : TaggedLocals) : SExpr → Option STyp
  | .variable name => (locals.find? (fun p => strEq p.1 name)).map (·.2)
  | .call name _ =>
    let result := items.filterMap fun
      | .fnT sig _ | .protoT sig => if strEq sig.name name then sig.res else none
      | _ => none
    match result with
    | [ty] => some ty
    | _ =>
      let sums := items.filterMap fun
        | decl@(.typeT ["tagged"] sumName [] [] (some (.raw _))) =>
          match Uebersetze.uSumSchemas [decl] with
          | .ok [schema] => if schema.cases.any (fun c => strEq c.1 name)
              then some (STyp.atom sumName) else none
          | _ => none
        | _ => none
      match sums with | [ty] => some ty | _ => none
  | _ => none

def taggedResolveCall (items : List SItemTief) (bindings : List TaggedBinding)
    (sources : List String) (locals : TaggedLocals) (name : String) (args : List SExpr) :
    Except String String := do
  let candidates := bindings.filter (fun b => strEq b.source name)
  if candidates.isEmpty then
    if sources.any (strEq · name) then
      throw ("tagged-dispatch-non-dispatchable-call: " ++ name)
    pure name
  else
    let selected := candidates.filter fun b =>
      args.length == b.signature.params.length &&
        ((args[b.receiver]?).bind (taggedExprType items locals)).any
          (fun ty => beqSTyp ty (.atom b.sumName))
    match selected with
    | [b] => pure b.signature.name
    | [] => throw ("tagged-dispatch-unresolved-receiver: " ++ name)
    | _ => throw ("tagged-dispatch-ambiguous-call: " ++ name)

mutual
def taggedRewriteExpr (items : List SItemTief) (bindings : List TaggedBinding)
    (sources : List String) (locals : TaggedLocals) : Nat → SExpr → Except String SExpr
  | 0, _ => .error "tagged-dispatch-expression-too-deep"
  | f + 1, e => do
    match e with
    | .call name args =>
      let args ← taggedRewriteExprs items bindings sources locals f args
      pure (.call (← taggedResolveCall items bindings sources locals name args) args)
    | .field a n => pure (.field (← taggedRewriteExpr items bindings sources locals f a) n)
    | .arrow a n => pure (.arrow (← taggedRewriteExpr items bindings sources locals f a) n)
    | .un op a => pure (.un op (← taggedRewriteExpr items bindings sources locals f a))
    | .old a => pure (.old (← taggedRewriteExpr items bindings sources locals f a))
    | .index a b => pure (.index (← taggedRewriteExpr items bindings sources locals f a)
        (← taggedRewriteExpr items bindings sources locals f b))
    | .bin op a b => pure (.bin op (← taggedRewriteExpr items bindings sources locals f a)
        (← taggedRewriteExpr items bindings sources locals f b))
    | .built n es => pure (.built n (← taggedRewriteExprs items bindings sources locals f es))
    | .ext k ns es => pure (.ext k ns (← taggedRewriteExprs items bindings sources locals f es))
    | _ => pure e
def taggedRewriteExprs (items : List SItemTief) (bindings : List TaggedBinding)
    (sources : List String) (locals : TaggedLocals) : Nat → List SExpr → Except String (List SExpr)
  | 0, _ => .error "tagged-dispatch-expression-too-deep"
  | _ + 1, [] => .ok []
  | f + 1, e :: es => do
    pure ((← taggedRewriteExpr items bindings sources locals f e) ::
      (← taggedRewriteExprs items bindings sources locals f es))
end

end Gabbro.Grammatik.Parser
