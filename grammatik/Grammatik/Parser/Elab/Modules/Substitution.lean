module
public import Grammatik.Parser.Elab.Generic.Expansion
public import Grammatik.Parser.Namen.Oeffentlich
public import Grammatik.Parser.Print.Stmt
@[expose] public section
namespace Gabbro.Grammatik.Parser.Modules
open Generic

/-- Inner generic binders shadow module parameters in both namespaces. -/
def underGenerics (bindings : Bindings) (params : List SGenericParam) : Bindings :=
  let names := params.map SGenericParam.name
  { bindings.without names with types := bindings.types.filter (fun p => !names.contains p.1) }

def parameter (env : Environment) (bindings : Bindings) : SGenericParam → RewriteM SGenericParam
  | .type n bounds => pure (.type n bounds)
  | .constant n ty => return .constant n (← rewriteType env bindings ty)
  | .function n ty => return .function n (← rewriteType env bindings ty)

/-- Preserve a function's own generics for the next frontend phase. -/
def signature (env : Environment) (bindings : Bindings) (sig : FnSig) : RewriteM FnSig := do
  let bindings := underGenerics bindings sig.generics
  let result ← rewriteSignature env bindings sig
  let params ← sig.generics.mapM (parameter env bindings)
  pure { result with generics := params }

/-- Forward a static argument by its canonical source, and respect a literal's own binders when
    substituting an enclosing module's parameters. Literal materialization remains a later phase. -/
def argument (env : Environment) (bindings : Bindings) (word : String) : Except String String := do
  match bindings.functionArguments.find? (fun entry => strEq entry.1 word) with
  | some (_, canonical) => pure canonical
  | none =>
    let ts ← tokens word
    match parseFunctionArgument (ts.length * 4 + 32) ts with
    | .ok (.literal sig body) =>
      let env := { env with declarations := [], deferApplications := true }
      let ((sig, body), requests) ← (do
        pure (← signature env bindings sig,
          ← rewriteBody env (bindings.without (sig.params.map Prod.fst)) body)).run []
      if !requests.isEmpty then throw "parametric-module-order: literal requested a function instance"
      let printed := [.wort "fn"] ++ (druckFnSig sig).drop 2 ++ druckAnw body
      pure (String.intercalate " " (printed.map zeigeTok))
    | _ => substituteRaw bindings word

mutual
def constant (env : Environment) (bindings : Bindings) : SKonstWert → RewriteM SKonstWert
  | .one value => return .one (← rewriteExpression env bindings value)
  | .rows rows => return .rows (← constants env bindings rows)
def constants (env : Environment) (bindings : Bindings) : List SKonstWert → RewriteM (List SKonstWert)
  | [] => pure []
  | value :: rest => return (← constant env bindings value) :: (← constants env bindings rest)
end

def field (env : Environment) (bindings : Bindings) (f : SFeld) : RewriteM SFeld := do
  pure { f with
    ftyp := ← rewriteType env bindings f.ftyp
    wo := ← f.wo.mapM (rewriteExpression env (bindings.without [f.fname]))
    pos := ← f.pos.mapM (fun text => liftResult (substituteRaw bindings text))
  }

def invariant (env : Environment) (bindings : Bindings) (iv : SGruppenInv) : RewriteM SGruppenInv := do
  pure { iv with
    pred := ← rewriteExpression env bindings iv.pred
  }

def tablePart (env : Environment) (bindings : Bindings) : STabTeil → RewriteM STabTeil
  | .tConst n ty value => return .tConst n (← rewriteType env bindings ty) (← constant env bindings value)
  | .tSlot fields => return .tSlot (← fields.mapM (field env bindings))
  | .tInv iv => return .tInv (← invariant env bindings iv)
  | part => pure part

/-- Module substitution uses the ordinary function traversal with applications deferred. Every
    storage declaration is copied; names and place references have already been hygienically bound.
    Unsupported item forms refuse explicitly rather than retaining unsubstituted parameters. -/
def substituteItem (env : Environment) (bindings : Bindings) : SItemTief → RewriteM SItemTief
  | .fnT sig body => do
    return .fnT (← signature env bindings sig)
      (← rewriteBody env ((underGenerics bindings sig.generics).without (sig.params.map Prod.fst)) body)
  | .protoT sig => return .protoT (← signature env bindings sig)
  | .specT sig pred => do
    return .specT (← signature env bindings sig)
      (← rewriteExpression env ((underGenerics bindings sig.generics).without (sig.params.map Prod.fst)) pred)
  | .asmT _ _ => liftResult (.error "parametric-module-assembly: raw bodies have no substitution rule")
  | .transT target sig body => do
    return .transT target (← signature env bindings sig)
      (← rewriteBody env ((underGenerics bindings sig.generics).without (sig.params.map Prod.fst)) body)
  | .typeT flags n args order ty => do
    return .typeT flags n
      (← args.mapM (rewriteType env bindings)) order (← ty.mapM (rewriteType env bindings))
  | .constT n ty value => return .constT n (← rewriteType env bindings ty) (← constant env bindings value)
  | .globT mu n ty value aligned sectionName shared => do
    return .globT mu n
      (← rewriteType env bindings ty) (← constant env bindings value)
      (← aligned.mapM (rewriteExpression env bindings)) sectionName shared
  | .tableT n sourceName count backed owner shared parts space => do
    return .tableT n sourceName
      (← count.mapM (rewriteExpression env bindings)) backed owner shared
      (← parts.mapM (tablePart env bindings)) space
  | .formatT n version endian fields => do
    return .formatT n
      (← version.mapM (rewriteExpression env bindings)) endian (← fields.mapM (field env bindings))
  | .arenaT n lo hi max ty provider => do
    let provider ← provider.mapM fun (path, amount) => do
      pure (path, ← rewriteExpression env bindings amount)
    pure (.arenaT n (← rewriteExpression env bindings lo) (← rewriteExpression env bindings hi)
      (← max.mapM (rewriteExpression env bindings)) (← rewriteType env bindings ty) provider)
  | .whyT n cases exhaustive => do
    let cases ← cases.mapM fun (tag, code, text) => do
      pure (tag, ← rewriteExpression env bindings code, text)
    pure (.whyT n cases exhaustive)
  | .atomT n ty publishes order observer => do
    return .atomT n (← rewriteType env bindings ty)
      (← publishes.mapM (fun es => es.mapM (rewriteExpression env bindings))) order observer
  | .lockT n places rank held shared masks iv => do
    return .lockT n
      (← places.mapM (rewriteExpression env bindings)) (← rewriteExpression env bindings rank)
      (← held.mapM (rewriteExpression env bindings)) (← shared.mapM (rewriteExpression env bindings))
      masks (← iv.mapM (rewriteExpression env bindings))
  | .rcuT n places reclaim => do
    return .rcuT n (← places.mapM (rewriteExpression env bindings))
      (← reclaim.mapM (rewriteExpression env bindings))
  | .groupT n members ivs => return .groupT n members (← ivs.mapM (invariant env bindings))
  | .accT n ty mode cpu q => do
    return .accT n (← rewriteType env bindings ty) mode
      (← cpu.mapM (rewriteExpression env bindings)) q
  | .concT starts => do
    let starts ← starts.mapM fun (path, args) => do
      pure (path, ← args.mapM (rewriteExpression env bindings))
    pure (.concT starts)
  | .assumT n arch text kind => pure (.assumT n arch text kind)
  | .varT n => pure (.varT n)
  | .useT path => pure (.useT path)
  | _ => liftResult (.error "parametric-module-item: declaration has no substitution rule")

/-- No generic-function instance may be requested while substituting a module. -/
def substitute (env : Environment) (bindings : Bindings) (item : SItemTief) : Except String SItemTief := do
  let (result, requests) ← (substituteItem { env with declarations := [], deferApplications := true }
    bindings item).run []
  if !requests.isEmpty then throw "parametric-module-order: function expansion ran before modules"
  pure result

end Gabbro.Grammatik.Parser.Modules
