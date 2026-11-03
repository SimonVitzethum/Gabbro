module
public import Grammatik.Parser.Elab.Generic.Arguments
@[expose] public section
namespace Gabbro.Grammatik.Parser.Generic

/-- Substitute a symbolic call's type arguments without making a concrete instance. -/
def symbolicHead (types : List (String × STyp)) (sig : FnSig) : FnSig :=
  { sig with params := sig.params.map (fun (n, ty) => (n, Spec.substituteType types ty)),
    res := sig.res.map (Spec.substituteType types) }

mutual
/-- Inference during the parametricity check keeps T abstract, including inferred lets,
    array elements, spec results and forwarded generic results. It never examines an impl body. -/
def symbolicType (source : List SItemTief) (template : FnSig) (locals : Spec.Locals) :
    Nat → SExpr → Option STyp
  | 0, _ => none
  | fuel + 1, expr =>
    match expr with
    | .res => template.res
    | .variable name =>
      match locals.find? (fun p => strEq p.1 name) with
      | some (_, ty) => some ty
      | none => (Spec.inferType source [] fuel expr).map (Spec.canonicalType source 128)
    | .call name args =>
      ((symbolicCall source template locals fuel name none args).toOption.bind (·.res))
        .orElse (fun _ => Spec.inferType source locals fuel expr)
    | .ext .instantiate (name :: words) args =>
      (symbolicCall source template locals fuel name (some words) args).toOption.bind (·.res)
    | .index array _ => do
      let .array element _ ← symbolicType source template locals fuel array | none
      pure element
    | .old value | .un _ value | .ext .label [_] [value] =>
      symbolicType source template locals fuel value
    | .bin op left right =>
      if ["==", "!=", "<", ">", "<=", ">=", "&&", "||"].any (strEq op) then
        some (.atom "bool")
      else (symbolicType source template locals fuel left).orElse
        (fun _ => symbolicType source template locals fuel right)
    | _ => (Spec.inferType source locals fuel expr).map (Spec.canonicalType source 128)

/-- A spec call consumes exactly a written bound. Forwarding to another generic must
    entail that function's bounds before any concrete type substitution can hide the omission. -/
def symbolicCall (source : List SItemTief) (template : FnSig) (locals : Spec.Locals) :
    Nat → String → Option (List String) → List SExpr → Except String FnSig
  | 0, _, _, _ => .error "generic.parametricity.fuel"
  | fuel + 1, name, explicit, args => do
    let parameters := typeParameters template
    let specs := (Spec.groups source).flatMap fun group => group.functions.filterMap fun sig =>
      if strEq (group.name ++ "::" ++ sig.name) name then some (group, sig) else none
    match specs with
    | [(group, sig)] =>
      if sig.params.length != args.length then throw "spec.call.arity"
      let types ← match explicit with
        | some words => Spec.explicitTypes (String.intercalate ", " words)
        | none => do
          let types ← (sig.params.zip args).foldlM (fun types (param, arg) =>
            match symbolicType source template locals fuel arg with
            | some ty => Spec.bindType group.types types param.2 ty
            | none => pure types) []
          group.types.mapM fun name => match types.find? (fun p => strEq p.1 name) with
            | some (_, ty) => pure ty
            | none => throw ("spec.call.type.required: " ++ name)
      if types.length != group.types.length then throw "spec.call.arguments"
      for ty in types do checkAbstractBound parameters ty group.name
      pure (symbolicHead (group.types.zip types) sig)
    | _ :: _ => throw "spec.call.ambiguous"
    | [] =>
      match (Spec.functionHeads source).find? (fun sig => strEq sig.name name) with
      | some sig =>
        match explicit with
        | none =>
          -- These names belong to the callee's scope. A global alias called T is
          -- not the caller's abstract T, even when their surface spellings coincide.
          if sig.generics.isEmpty then
            pure { sig with params := sig.params.map (fun (n, ty) =>
                (n, Spec.canonicalType source 128 ty)),
              res := sig.res.map (Spec.canonicalType source 128) }
          else pure sig
        | some words =>
          if sig.generics.length != words.length then throw "generic argument count does not match declaration"
          let types ← (sig.generics.zip words).foldlM (fun types (param, word) => do
            match param with
            | .type name bounds =>
              let ty ← readType word
              for bound in bounds do checkAbstractBound parameters ty bound
              pure (types ++ [(name, ty)])
            | _ => pure types) []
          pure (symbolicHead types sig)
      | none =>
        match template.generics.find? (fun p => strEq p.name name) with
        | some (.function _ (.raw raw)) => Uebersetze.uZeigerSig raw
        | _ => throw ("generic.parametricity.call: " ++ name)
end

/-- An abstract value may cross a call only through the same symbolic parameter type. -/
def checkSymbolicArguments (source : List SItemTief) (template : FnSig) (locals : Spec.Locals)
    (name : String) (words : Option (List String)) (args : List SExpr) : Except String Unit := do
  let parameters := typeParameters template
  let abstract := fun arg => (symbolicType source template locals 128 arg).any (mentionsParameter parameters)
  let known := (Spec.groups source).any (fun group => name.startsWith (group.name ++ "::")) ||
    (Spec.functionHeads source).any (fun sig => strEq sig.name name) ||
    template.generics.any (fun p => strEq p.name name)
  if !known && !(args.any abstract) then return ()
  let sig ← symbolicCall source template locals 128 name words args
  if sig.params.length != args.length then throw "generic.parametricity.call.arity"
  for (param, arg) in sig.params.zip args do
    let actual := symbolicType source template locals 128 arg
    if actual.any (mentionsParameter parameters) || mentionsParameter parameters param.2 then
      if !(actual.any (fun ty => beqSTyp ty param.2)) then
        throw ("generic.parametricity.argument: " ++ name)

/-- These checks run over symbolic templates, also unused ones. The ordinary elaborator
    independently checks the specialized program against each implementation's real contracts. -/
def checkParametricExpression (source : List SItemTief) (template : FnSig)
    (locals : Spec.Locals) (expected : Option STyp) (expr : SExpr) : Except String SExpr := do
  let parameters := typeParameters template
  let abstract := fun value =>
    (symbolicType source template locals 128 value).any (mentionsParameter parameters)
  match expr with
  | .bin op left right =>
    if abstract left || abstract right then
      let kind := if ["==", "!=", "<", ">", "<=", ">=", "&&", "||"].any (strEq op)
        then "comparison" else "arithmetic"
      throw ("generic.parametricity." ++ kind ++ ": " ++ op)
  | .un op value =>
    if abstract value then throw ("generic.parametricity.unary: " ++ op)
  | .field value _ | .arrow value _ =>
    if abstract value then throw "generic.parametricity.field"
  | .index array index =>
    if abstract index then throw "generic.parametricity.index"
    if abstract array then
      match symbolicType source template locals 128 array with
      | some (.array _ _) => pure ()
      | _ => throw "generic.parametricity.index"
  | .call name args => checkSymbolicArguments source template locals name none args
  | .ext .instantiate (name :: words) args =>
    checkSymbolicArguments source template locals name (some words) args
  | .built name args =>
    if args.any abstract then throw ("generic.parametricity.builtin: " ++ name)
  | .ext .label [_] [_] => pure ()
  | .ext _ _ args =>
    if args.any abstract then throw "generic.parametricity.expression"
  | _ => pure ()
  let actual := symbolicType source template locals 128 expr
  if expected.any (mentionsParameter parameters) || actual.any (mentionsParameter parameters) then
    if let some expected := expected then
      if !(actual.any (fun actual => beqSTyp actual expected)) then
        throw "generic.parametricity.binding"
  pure expr

def checkParametricStatement (source : List SItemTief) (template : FnSig)
    (locals : Spec.Locals) : SAnw → Except String Unit
  | .cond value _ _ _ | .elsif value _ | .cases value _ | .trim value _ _ |
    .shift value _ _ | .free value =>
    if (symbolicType source template locals 128 value).any (mentionsParameter (typeParameters template))
    then .error "generic.parametricity.statement" else pure ()
  | .set place op value => do
    let ty := symbolicType source template locals 128 place
    if ty.any (mentionsParameter (typeParameters template)) then
      if !strEq op "=" then throw ("generic.parametricity.arithmetic: " ++ op)
    let _ ← checkParametricExpression source template locals ty value
    if ty.isNone && (symbolicType source template locals 128 value).any
        (mentionsParameter (typeParameters template)) then
      throw "generic.parametricity.assignment"
    pure ()
  | .lcall call | .bindLib _ _ _ call =>
    if call.args.any (fun arg => (symbolicType source template locals 128 arg).any
        (mentionsParameter (typeParameters template))) then
      .error "generic.parametricity.library-call" else pure ()
  | _ => pure ()

/-- Raw metadata has no typed expression tree. An abstract value there must not bypass
    the structured check; ordinary concrete loop counters and constant parameters remain usable. -/
def checkParametricRaw (source : List SItemTief) (template : FnSig)
    (locals : Spec.Locals) (raw : String) : Except String Unit := do
  let ts ← tokens raw
  for token in ts do
    if let some name := nameText token then
      if (symbolicType source template locals 128 (.variable name)).any
          (mentionsParameter (typeParameters template)) then
        throw "generic.parametricity.raw"

/-- Reuse the spec/dyn visitor, with symbolic result inference for block-local bindings. -/
def checkParametricBody (source : List SItemTief) (template : FnSig) (body : SAnw) :
    Except String Unit := do
  if (typeParameters template).isEmpty then return ()
  -- Type inference and call checking use the captured source through the hooks below.
  -- Keep the visitor's concrete-call expectation lookup empty: callee type names live
  -- in its own scope and must not be interpreted as this template's binders.
  let walk : Spec.Walk := { source := [], instantiate := false, resolveSpecs := false,
    infer := fun locals value => symbolicType source template locals 128 value,
    exprRewrite := checkParametricExpression source template,
    statementCheck := checkParametricStatement source template,
    rawCheck := checkParametricRaw source template, result := template.res }
  let _ ← walk.signature template
  let _ ← walk.statement template.params 100000 body
  pure ()

end Gabbro.Grammatik.Parser.Generic
