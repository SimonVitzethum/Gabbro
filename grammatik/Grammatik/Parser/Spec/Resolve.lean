module

public import Grammatik.Parser.Spec.Check
public import Grammatik.Parser.Elab.Uebersetze.Tagged.Schema

@[expose] public section

namespace Gabbro.Grammatik.Parser.Spec

abbrev Locals := List (String × STyp)

/-- Generated names cannot be spelled as source identifiers; collisions in a supplied AST are checked. -/
def implementationName (index : Nat) (name : String) : String :=
  "$spec$" ++ toString index ++ "$" ++ name

/-- Replace group items with the actual implementation bodies, retaining their own contracts. -/
def materialize (items : List SItemTief) : List SItemTief :=
  (items.flatMap fun
    | .specGroupT .. | .implGroupT .. => []
    | it => [it])
  ++ ((instances items).zipIdx.flatMap fun (i, n) => i.functions.map fun
    | .fnT s b => .fnT { s with name := implementationName n s.name, art := "impl" } b
    | it => it)

def functionHeads (items : List SItemTief) : List FnSig := items.filterMap fun
  | .fnT s _ | .protoT s | .specT s _ | .asmT s _ => some s
  | .callT s => some { art := "", name := s.name, params := s.params, res := s.res,
                      fehler := s.fail, klauseln := [] }
  | _ => none

/-- Read the table field type from the existing surface declaration. -/
def tableField (items : List SItemTief) (table field : String) : Option STyp := do
  let .tableT _ _ _ _ _ _ parts ← items.find? (fun
    | .tableT n _ _ _ _ _ _ => strEq n table
    | _ => false) | none
  let fields := parts.flatMap fun | .tSlot fs => fs | _ => []
  return (← fields.find? fun f => strEq f.fname field).ftyp

/-- Only types determined by the ordinary source environment participate in inference.
    An untyped literal alone does not guess an implementation. -/
def inferType (items : List SItemTief) (locals : Locals) : Nat → SExpr → Option STyp
  | 0, _ => none
  | f + 1, e =>
    match e with
    | .variable n =>
      ((locals.find? fun p => strEq p.1 n).map Prod.snd).orElse fun _ =>
        items.findSome? fun
          | .globT _ m t _ _ _ _ | .constT m t _ | .atomT m t _ _ _ =>
            if strEq m n then some t else none
          | _ => none
    | .tru | .fls => some (.atom "bool")
    | .call n _ =>
      (((functionHeads items).find? fun s => strEq s.name n).bind (·.res)).orElse fun _ => do
        let declarations := items.map fun | .taggedByT decl _ => decl | it => it
        let schemas ← (Uebersetze.uSumSchemas declarations).toOption
        let [schema] := schemas.filter (fun s => s.cases.any (fun c => strEq c.1 n)) | none
        return .atom schema.name
    | .field (.index (.variable t) _) fld => tableField items t fld
    | .field (.index (.field (.variable t) "slots") _) fld => tableField items t fld
    | .field x fld => do
      let .index _ t ← inferType items locals f x | none
      tableField items t fld
    | .index a _ => do
      let .array t _ ← inferType items locals f a | none
      return t
    | .old x | .un _ x => inferType items locals f x
    | .bin op a b =>
      if ["==", "!=", "<", ">", "<=", ">=", "&&", "||"].any (strEq op) then
        some (.atom "bool")
      else (inferType items locals f a).orElse fun _ => inferType items locals f b
    | _ => none

/-- Infer occurrences of type parameters structurally, rejecting inconsistent occurrences. -/
def bindType (parameters : List String) (env : List (String × STyp)) :
    STyp → STyp → Except String (List (String × STyp))
  | .atom n, actual =>
    if parameters.any (strEq n) then
      match env.find? (fun p => strEq p.1 n) with
      | none => .ok ((n, actual) :: env)
      | some (_, t) => if beqSTyp t actual then .ok env else .error "spec.call.type.conflict"
    else .ok env
  | .ptr _ _ a, .ptr _ _ b | .array a _, .array b _ | .wrap a, .wrap b |
    .range a _ _ _, .range b _ _ _ | .embed a _ _, .embed b _ _ => bindType parameters env a b
  | _, _ => .ok env

/-- Resolve to precisely one concrete function; the ordinary elaborator checks its real contract. -/
def resolveCall (items : List SItemTief) (locals : Locals) (name : String)
    (explicit : Option (List STyp)) (args : List SExpr) : Except String String := do
  let gs := groups items
  let candidates := gs.flatMap fun g => g.functions.filterMap fun s =>
    if strEq (g.name ++ "::" ++ s.name) name then some (g, s) else none
  match candidates with
  | [] =>
    if explicit.isSome || gs.any (fun g => name.startsWith (g.name ++ "::")) then
      throw ("spec.call.unknown: " ++ name)
    else return name
  | [(g, s)] =>
    if s.params.length != args.length then throw "spec.call.arity"
    let types ← match explicit with
      | some ts => pure ts
      | none => do
        let env ← (s.params.zip args).foldlM (fun env (p, arg) =>
          match inferType (materialize items) locals 128 arg with
          | none => pure env
          | some actual => bindType g.types env p.2 (canonicalType items 128 actual)) []
        g.types.mapM fun n => match env.find? (fun p => strEq p.1 n) with
          | some (_, t) => pure t
          | none => throw ("spec.call.type.required: " ++ n)
    if types.length != g.types.length then throw "spec.call.arguments"
    let matches := ((instances items).zipIdx).filter fun (i, _) =>
      strEq i.group g.name && beqSTypList (i.types.map (canonicalType items 128))
        (types.map (canonicalType items 128))
    match matches with
    | [(_, n)] => return implementationName n s.name
    | [] => throw "spec.call.implementation.missing"
    | _ => throw "spec.call.implementation.ambiguous"
  | _ => throw "spec.call.ambiguous"

/-- Parse only type arguments here; generic-function argument kinds are a preceding pass (§5.4). -/
def explicitTypes (raw : String) : Except String (List STyp) := do
  let tokens ← lex raw
  let (types, r) ← parseSpecTypes (tokens.length * 8 + 32) tokens
  match r with
  | [.ende] => return types
  | _ => throw "spec.call.arguments"

end Gabbro.Grammatik.Parser.Spec
