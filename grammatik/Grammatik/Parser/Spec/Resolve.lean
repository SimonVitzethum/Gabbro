module

public import Grammatik.Parser.Spec.Check
public import Grammatik.Parser.Lex.Tafel
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
  | .callT s => some
    { art := "", name := s.name, params := s.params, res := s.res,
      fehler := s.fail, klauseln := [], generics := [] }
  | _ => none

/-- What type inference reads from a source, by name: the function heads, the typed values (statics,
    constants, atomics), the tables' parts, and the source itself for the tagged sums. A walk builds it
    once; a scan of the items at every expression made a unit of n functions cost n². -/
structure Umfeld where
  items : List SItemTief
  heads : Tafel FnSig (·.name)
  werte : Tafel (String × STyp) (·.1)
  tabellen : Tafel (String × List STabTeil) (·.1)

/-- The environment of a source. -/
def Umfeld.von (items : List SItemTief) : Umfeld where
  items := items
  heads := Tafel.von _ (functionHeads items)
  werte := Tafel.von _ (items.filterMap fun
    | .globT _ m t _ _ _ _ | .constT m t _ | .atomT m t _ _ _ => some (m, t)
    | _ => none)
  tabellen := Tafel.von _ (items.filterMap fun
    | .tableT n _ _ _ _ _ parts _ => some (n, parts)
    | _ => none)

/-- Read the table field type from the existing surface declaration. -/
def tableField (U : Umfeld) (table field : String) : Option STyp := do
  let (_, parts) ← U.tabellen.finde table
  let fields := parts.flatMap fun | .tSlot fs => fs | _ => []
  return (← fields.find? fun f => strEq f.fname field).ftyp

/-- `inferType` over an environment built beforehand. -/
def inferTypeMit (U : Umfeld) (locals : Locals) : Nat → SExpr → Option STyp
  | 0, _ => none
  | f + 1, e =>
    match e with
    | .variable n =>
      ((locals.find? fun p => strEq p.1 n).map Prod.snd).orElse fun _ =>
        (U.werte.finde n).map Prod.snd
    | .tru | .fls => some (.atom "bool")
    | .call n _ =>
      ((U.heads.finde n).bind (·.res)).orElse fun _ => do
        let declarations := U.items.map fun | .taggedByT decl _ => decl | it => it
        let schemas ← (Uebersetze.uSumSchemas declarations).toOption
        let [schema] := schemas.filter (fun s => s.cases.any (fun c => strEq c.1 n)) | none
        return .atom schema.name
    | .field (.index (.variable t) _) fld => tableField U t fld
    | .field (.index (.field (.variable t) "slots") _) fld => tableField U t fld
    | .field x fld => do
      let .index _ t ← inferTypeMit U locals f x | none
      tableField U t fld
    | .index a _ => do
      let .array t _ ← inferTypeMit U locals f a | none
      return t
    | .old x | .un _ x => inferTypeMit U locals f x
    | .bin op a b =>
      if ["==", "!=", "<", ">", "<=", ">=", "&&", "||"].any (strEq op) then
        some (.atom "bool")
      else (inferTypeMit U locals f a).orElse fun _ => inferTypeMit U locals f b
    | _ => none

/-- Only types determined by the ordinary source environment participate in inference.
    An untyped literal alone does not guess an implementation. -/
def inferType (items : List SItemTief) (locals : Locals) (fuel : Nat) (e : SExpr) : Option STyp :=
  inferTypeMit (Umfeld.von items) locals fuel e

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

/-- `resolveCall` over spec groups collected beforehand (`gs = groups items`). -/
def resolveCallWith (gs : List Group) (items : List SItemTief) (locals : Locals) (name : String)
    (explicit : Option (List STyp)) (args : List SExpr) : Except String String := do
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
    let selected := ((instances items).zipIdx).filter fun (i, _) =>
      strEq i.group g.name && beqSTypList (i.types.map (canonicalType items 128))
        (types.map (canonicalType items 128))
    match selected with
    | [(_, n)] => return implementationName n s.name
    | [] => throw "spec.call.implementation.missing"
    | _ => throw "spec.call.implementation.ambiguous"
  | _ => throw "spec.call.ambiguous"

/-- Resolve to precisely one concrete function; the ordinary elaborator checks its real contract. -/
def resolveCall (items : List SItemTief) (locals : Locals) (name : String)
    (explicit : Option (List STyp)) (args : List SExpr) : Except String String :=
  resolveCallWith (groups items) items locals name explicit args

/-- Parse only type arguments here; generic-function argument kinds are a preceding pass (§5.4). -/
def explicitTypes (raw : String) : Except String (List STyp) := do
  let tokens ← match lex raw with
    | .ok tokens => pure tokens
    | .error _ => throw "spec.call.arguments"
  let (types, r) ← parseSpecTypes (tokens.length * 8 + 32) tokens
  match r with
  | [.ende] => return types
  | _ => throw "spec.call.arguments"

end Gabbro.Grammatik.Parser.Spec
