module

public import Grammatik.Parser.Dyn.Closed

@[expose] public section
namespace Gabbro.Grammatik.Parser.Dyn
open Spec

/-- Preserve nominal dyn identity through ordinary type aliases. -/
def lookup (items : List SItemTief) (closed : List Closed) : Nat → STyp → Option Closed
  | 0, _ => none
  | f + 1, .atom n =>
    (closed.find? (fun c => strEq c.name n)).orElse fun _ =>
      match items.find? (fun | .typeT _ name [] [] (some _) => strEq name n | _ => false) with
      | some (.typeT _ _ _ _ (some t)) => lookup items closed f t
      | _ => none
  | _, t@(.dyn ..) => closed.find? (fun c => beqSTyp c.surface t || c.aliases.any (beqSTyp t))
  | _, _ => none

def expressionType (items : List SItemTief) (closed : List Closed)
    (locals : Locals) (e : SExpr) : Option STyp :=
  match e with
  | .call n _ =>
    ((closed.find? fun c => c.cases.any (fun k => strEq k.name n)).map fun c => STyp.atom c.name)
      |>.orElse fun _ => inferType (materialize items) locals 128 e
  | _ => inferType (materialize items) locals 128 e

def dynamicType (items : List SItemTief) (closed : List Closed)
    (locals : Locals) (e : SExpr) : Option Closed :=
  (expressionType items closed locals e).bind (lookup items closed 128)

/-- Equality on a container cannot indirectly compare its dyn elements either. -/
def containsDynamic (items : List SItemTief) (closed : List Closed) : Nat → STyp → Bool
  | 0, _ => false
  | f + 1, t =>
    if (lookup items closed 128 t).isSome then true else
    match t with
    | .array element _ => containsDynamic items closed f element
    | .atom n =>
      match items.find? (fun | .typeT _ name [] [] (some _) => strEq name n | _ => false) with
      | some (.typeT _ _ _ _ (some body)) => containsDynamic items closed f body
      | _ => false
    | _ => false

def checkCall (items : List SItemTief) (closed : List Closed) (locals : Locals)
    (name : String) (args : List SExpr) : Except String Unit := do
  if args.any (fun a => (dynamicType items closed locals a).isSome) then
    for group in groups items do
      for signature in group.functions do
        if strEq name (group.name ++ "::" ++ signature.name) then
          let [parameter] := group.types | throw "dyn.spec-type-arity"
          if !taggedDispatchable (taggedCanonicalSignature parameter signature) then
            throw ("dyn.non-dispatchable-call: " ++ name)

/-- Producers select the contextual bound. Without context, only one bound may match;
    the pass never silently picks a narrower effect set. -/
def rewriteExpr (items : List SItemTief) (closed : List Closed) (locals : Locals)
    (expected : Option STyp) (e : SExpr) : Except String SExpr := do
  match dynamicType items closed locals e, expected with
  | some actual, some target =>
    match lookup items closed 128 target with
    | some target => if !strEq actual.name target.name then throw "dyn.bound-conversion"
    | none => throw "dyn.downcast"
  | _, _ => pure ()
  match e with
  | .ext .dyn [spec] [payload] =>
    let some ty := expressionType items closed locals payload
      | throw ("dyn.payload-type-required: " ++ spec)
    if expected.isSome && (expected.bind (lookup items closed 128)).isNone then
      throw "dyn.producer-target"
    let candidates := closed.filter fun c => strEq c.spec spec &&
      c.cases.any (fun k => beqSTyp (canonicalType items 128 k.payload) (canonicalType items 128 ty))
    let candidates := match expected.bind (lookup items closed 128) with
      | some target => candidates.filter (fun c => strEq c.name target.name)
      | none => candidates
    let target ← match candidates with
      | [target] => pure target
      | [] => throw ("dyn.producer-implementation: " ++ spec)
      | _ => throw ("dyn.producer-bound-required: " ++ spec)
    let some variant := target.cases.find? fun c =>
        beqSTyp (canonicalType items 128 c.payload) (canonicalType items 128 ty)
      | throw ("dyn.producer-implementation: " ++ spec)
    return .call variant.name [payload]
  | .ext .dyn _ _ => throw "dyn.producer.syntax"
  | .bin op a b =>
    if (strEq op "==" || strEq op "!=") &&
        ((expressionType items closed locals a).any (containsDynamic items closed 128) ||
         (expressionType items closed locals b).any (containsDynamic items closed 128)) then
      throw "dyn.equality"
    return e
  | .field value _ | .arrow value _ =>
    if (dynamicType items closed locals value).isSome then throw "dyn.implementation-test"
    return e
  | .ext .inst [name, _] args =>
    checkCall items closed locals name args
    return e
  | .call name args | .built name args =>
    checkCall items closed locals name args
    if ["downcast", "is_impl", "type_of"].any (strEq name) &&
        args.any (fun a => (dynamicType items closed locals a).isSome) then
      throw "dyn.downcast-or-implementation-test"
    return e
  | _ => return e

/-- Written matches would reveal the implementation identity. Generated dispatch matches
    are introduced only after this gate, so they do not need a bypass flag. -/
def checkStatement (items : List SItemTief) (closed : List Closed)
    (locals : Locals) : SAnw → Except String Unit
  | .cases value _ =>
    if (dynamicType items closed locals value).isSome then .error "dyn.implementation-test" else .ok ()
  | .trim value _ _ =>
    if (dynamicType items closed locals value).isSome then .error "dyn.downcast" else .ok ()
  | _ => .ok ()

/-- Raw loop metadata has no typed expression tree. Refuse a dyn name there instead
    of letting an equality or implementation test bypass the structured visitor. -/
def checkRaw (items : List SItemTief) (closed : List Closed)
    (locals : Locals) (raw : String) : Except String Unit := do
  let tokens ← lex raw
  if tokens.any (fun token => match nameText token with
      | some n => strEq n "dyn" ||
          (dynamicType items closed locals (.variable n)).isSome ||
          items.any (fun
            | .tableT table _ _ _ _ _ parts =>
              strEq table n && (parts.flatMap fun | .tSlot fs => fs | _ => []).any
                (fun f => (lookup items closed 128 f.ftyp).isSome)
            | _ => false)
      | none => false) then throw "dyn.raw-header"

end Gabbro.Grammatik.Parser.Dyn
