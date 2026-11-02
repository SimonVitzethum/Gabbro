module

public import Grammatik.Kern.Syntax.Typen.Produkt
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Item.ElementTief.Defs1
public import Grammatik.Parser.Lex.Lexer
public import Grammatik.Parser.Elab.Uebersetze.Teil3
public import Grammatik.Parser.Elab.Uebersetze.Records.Schema

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Parse the complete balanced field group with the canonical field/type reader. -/
def uRecordFields (text : String) : Except String (List SFeld) :=
  match lex text with
  | .error _ => .error "source export: record schema unreadable"
  | .ok tokens =>
    match parseFeldListe (tokens.length + 1) tokens with
    | .error e => .error e
    | .ok (fields, rest) =>
      if rest.all (fun | .ende => true | _ => false) then pure fields
      else .error "source export: trailing tokens in record schema"

/-- Placement, state predicates and erased resources cannot disappear from a value schema. -/
def uRecordFieldMetadata (field : SFeld) : Bool :=
  field.pos.isSome || field.bezug.isSome || field.wo.isSome || field.reserviert || field.byOps

/-- One field type: a nominal record reference resolves through the collected schemas, every other
    shape through the canonical type reader (records never weaken a range reading). -/
def uRecordFeldTyp (scope : UTypeScope) (alias : List (String × (Int × Int))) (tabs : List UTab) :
    STyp → Except String Ty
  | .atom name =>
    match scope.types.find? (fun entry => strEq entry.1 name) with
    | some (_, ty) => .ok ty
    | none => uTyp alias tabs (.atom name)
  | other => uTyp alias tabs other

/-- One schema field: no metadata duties, then the resolved type. -/
def uRecordField (scope : UTypeScope) (alias : List (String × (Int × Int))) (tabs : List UTab)
    (field : SFeld) : Except String (String × Ty) := do
  if uRecordFieldMetadata field then
    throw "source export: record field placement/where/resource duties are unsupported"
  let ty ← uRecordFeldTyp scope alias tabs field.ftyp
  pure (field.fname, ty)

/-- One dependency pass. Identity is the original declaration position, independent of resolution
    order. A deferred declaration is retried only after another declaration has resolved. -/
def uTypePass (scope : UTypeScope) (alias : List (String × (Int × Int))) (tabs : List UTab)
    (pending : List (Nat × SItemTief)) :
    Except String (UTypeScope × List (Nat × SItemTief)) :=
  pending.foldlM (fun (scope, deferred) (identity, item) => do
    match item with
    | .typeT flags name args order (some body) =>
      if flags.any (fun flag => flag != "pub" && flag != "export") || !args.isEmpty || !order.isEmpty then
        throw ("source export: record/type modifiers require ownership or nominal proof binding: " ++ name)
      if scope.types.any (fun entry => strEq entry.1 name) then
        throw ("source export: duplicate type declaration: " ++ name)
      match body with
      | .raw text =>
        let fields ← uRecordFields text
        if (fields.map (·.fname)).eraseDups.length != fields.length then
          throw ("source export: duplicate record field: " ++ name)
        if fields.any uRecordFieldMetadata then
          throw ("source export: record field placement/where/resource duties are unsupported: " ++ name)
        match fields.mapM (uRecordField scope alias tabs) with
        | .error _ => pure (scope, deferred ++ [(identity, item)])
        | .ok resolved =>
          let schema : URecord := { name, identity, fields := resolved, modifiers := flags }
          pure ({ types := scope.types ++ [(name, schema.ty)], records := scope.records ++ [schema] }, deferred)
      | _ =>
        match uTyp alias tabs body with
        | .error _ => pure (scope, deferred ++ [(identity, item)])
        | .ok ty => pure ({ scope with types := scope.types ++ [(name, ty)] }, deferred)
    | _ => throw "source export: type declaration has no value schema") (scope, [])

/-- There are at most as many productive passes as declarations. Cycles and missing names fail closed. -/
def uResolveTypes : Nat → UTypeScope → List (String × (Int × Int)) → List UTab →
    List (Nat × SItemTief) → Except String UTypeScope
  | _, scope, _, _, [] => .ok scope
  | 0, _, _, _, _ => .error "source export: cyclic or unresolved by-value record schema"
  | fuel + 1, scope, alias, tabs, pending => do
    let (next, deferred) ← uTypePass scope alias tabs pending
    if deferred.length < pending.length then uResolveTypes fuel next alias tabs deferred
    else throw "source export: cyclic, unsupported or unresolved by-value record schema"

/-- Tagged declarations retain their separate canonical collector. Every other type resolves here. -/
def uTypes (constants : List (String × Int)) (alias : List (String × (Int × Int)))
    (tabs : List UTab) (items : List SItemTief) : Except String UTypeScope :=
  let pending := (List.range items.length).zip items |>.filter fun (_, item) =>
    match item with
    | .typeT flags .. => !flags.any (strEq · "tagged")
    | _ => false
  uResolveTypes pending.length { types := constants.map (fun (name, value) => (name, .int value value)) } alias tabs pending

/-- The nominal schema of a product value, with the proof that the identity matches. Unknown nominal
    identities stay refused; they never default to a structural guess. -/
def uRecordOf : List URecord → (ty : Ty) → Except String { schema : URecord // schema.ty = ty }
  | [], _ => .error "source export: unknown nominal record schema"
  | schema :: rest, ty =>
    if h : schema.ty = ty then .ok ⟨schema, h⟩ else uRecordOf rest ty

/-- A resolved schema is one of the declared schemas. -/
theorem uRecordOf_mem (records : List URecord) (ty : Ty)
    (schema : { schema : URecord // schema.ty = ty })
    (h : uRecordOf records ty = .ok schema) : schema.val ∈ records := by
  induction records with
  | nil => simp only [uRecordOf] at h
  | cons head rest ih =>
    simp only [uRecordOf] at h
    split at h
    · next heq => cases heq; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih _ h)

/-- Arrange already elaborated values in schema order. Source expressions are elaborated before this step. -/
def uRecordValues (schema : URecord) (values : List (String × USide)) : Except String USide := do
  if values.length != schema.fields.length ||
      (values.map (·.1)).eraseDups.length != values.length ||
      values.any (fun value => !schema.fields.any (fun field => strEq field.1 value.1)) then
    throw "source export: missing, duplicate or unknown record constructor field"
  let fields ← schema.fields.mapM fun (name, ty) => do
    let value ← uSuch "record field" values name
    pure (ty, value)
  let reordered := values.map (·.1) != schema.fields.map (·.1)
  pure (.product schema.identity reordered fields)

/-- A typed position is resolved from a schema, never from a run-time string. -/
def uRecordPosition : (fields : List (String × Ty)) → (name : String) →
    Except String (Σ ty, FieldAt (fields.map (·.2)) ty)
  | [], _ => .error "source export: unknown record field"
  | (name, ty) :: rest, selected =>
    if strEq name selected then .ok ⟨ty, .head⟩
    else (uRecordPosition rest selected).map fun ⟨ty, position⟩ => ⟨ty, .tail position⟩

/-- Source-side type information for aggregate binding. The dependent lowering checks it again. -/
def uValueType (ctx : UCtx) : USide → Option Ty
  | .param name => (ctx.names.findIdx? (strEq · name)).bind (ctx.types[·]?)
  | .typed ty _ => some ty
  | .product identity _ _ =>
    (ctx.records.find? (fun schema => schema.identity == identity)).map (·.ty)
  | .field base field => do
    let ty ← uValueType ctx base
    let schema ← ctx.records.find? (fun schema => decide (schema.ty = ty))
    (schema.fields.find? (fun entry => strEq entry.1 field)).map (·.2)
  | .replace base _ _ => uValueType ctx base
  | .idx base _ => match uValueType ctx base with | some (.arr ty _) => some ty | _ => none
  | .truth _ => some .bool
  | .lit value => some (.int value value)
  | .conv lo hi _ | .eng _ lo hi => some (.int lo hi)
  | .glob name => (ctx.globs.find? (fun global => strEq global.name name)).map (fun global => global.ty.toTy)
  | .erg => ctx.resTy
  | _ => none

/-- Entry snapshots retain the containing carrier when projecting a nested record field. -/
def uOldRecord : USide → Except String USide
  | .slot base field index | .tab base field index => pure (.old base field index)
  | .field base name => (uOldRecord base).map (.field · name)
  | _ => .error "source export: old record requires a containing carrier"

/-- Explicit product initializers retain every field. Zero is an integer field, never a missing field. -/
def uConstantValue : USide → Except String UKonst
  | .lit value => pure (.zahl value)
  | .truth value => pure (.wahr value)
  | .text bytes => pure (.text bytes)
  | .product name _ fields => do pure (.product name (← fields.mapM (fun (_, side) => uConstantValue side)))
  | .arrNil => pure .nil
  | .arrCons value rest => do pure (.cons (← uConstantValue value) (← uConstantValue rest))
  | .typed _ value => uConstantValue value
  | .conv lo hi value => do
    match ← uConstantValue value with
    | .zahl number =>
      if lo ≤ number ∧ number ≤ hi then pure (.zahl number)
      else throw "source export: record initializer outside field range"
    | _ => throw "source export: record initializer conversion requires a number"
  | _ => .error "source export: record initializer requires explicit constant fields"

/-- Elaborate labelled record constructor arguments with the given value elaborator: `P(a: v, …)`
    arrives as `.ext .label` applications, one per field, in source order. -/
def uRecordSides (ctx : UCtx) (rechne : SExpr → Except String USide) :
    List SExpr → Except String (List (String × USide))
  | [] => .ok []
  | .ext .label [label] [value] :: rest => do
    let side ← match value with
      | .tru => pure (.truth true)
      | .fls => pure (.truth false)
      | .variable name =>
        match uParamNr ctx name with
        | .ok position =>
          match ctx.kinds[position]? with
          | some .bool => pure (.param name)
          | _ => rechne value
        | .error _ => rechne value
      | _ => rechne value
    let tail ← uRecordSides ctx rechne rest
    pure ((label, side) :: tail)
  | _ => .error "source export: record construction requires labelled fields"

end Gabbro.Grammatik.Parser.Uebersetze
