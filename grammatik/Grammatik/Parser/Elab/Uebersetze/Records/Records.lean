module

public import Grammatik.Kern.Syntax.Typen.Produkt
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Item.ElementTief.Defs1
public import Grammatik.Parser.Lex.Lexer
public import Grammatik.Parser.Elab.Uebersetze.Kontext.LocalLookup
public import Grammatik.Parser.Elab.Uebersetze.Records.Schema
public import Grammatik.Parser.Elab.Uebersetze.Records.Embedding

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Parse the complete balanced field group with the canonical field/type reader. -/
def uRecordFields (text : String) : Except String (List SFeld) :=
  match lex text with
  | .error _ => .error "source export: record schema unreadable"
  | .ok tokens =>
    match parseFeldListe (tokens.length * 4 + 32) tokens with
    | .error e => .error e
    | .ok (fields, rest) =>
      if rest.all (fun | .ende => true | _ => false) then pure fields
      else .error "source export: trailing tokens in record schema"

/-- Placement, state predicates and erased resources cannot disappear from a value schema. -/
def uRecordFieldMetadata (field : SFeld) : Bool :=
  field.pos.isSome || field.bezug.isSome || field.wo.isSome || field.reserviert || field.byOps

/-- One field type: a nominal record reference resolves through the collected schemas, every other
    shape through the canonical type reader (records never weaken a range reading). -/
def uRecordFeldTyp (scope : UTypeScope) (alias : List (String × (Int × Int))) (tabs : List UTab)
    (eigner : List String := []) (spaces : List String := []) : STyp → Except String Ty :=
  uTypIn alias tabs scope.types spaces eigner

/-- One schema field: no metadata duties, then the resolved type. -/
def uRecordField (scope : UTypeScope) (alias : List (String × (Int × Int))) (tabs : List UTab)
    (field : SFeld) (eigner : List String := []) (spaces : List String := []) : Except String (String × Ty) := do
  if uRecordFieldMetadata field then
    throw "source export: record field placement/where/resource duties are unsupported"
  let ty ← uRecordFeldTyp scope alias tabs eigner spaces field.ftyp
  pure (field.fname, ty)

/-- One dependency pass. Identity is the original declaration position, independent of resolution
    order. A deferred declaration is retried only after another declaration has resolved. -/
def uTypePass (scope : UTypeScope) (alias : List (String × (Int × Int))) (tabs : List UTab)
    (items : List SItemTief) (pending : List (Nat × SItemTief)) (eigner : List String := []) (spaces : List String := [])
    (widths : List (String × (Int × Int)) := []) :
    Except String (UTypeScope × List (Nat × SItemTief)) :=
  pending.foldlM (fun (scope, deferred) (identity, item) => do
    match item with
    | .typeT flags name args order (some body) =>
      if flags.any (fun flag => flag != "pub" && flag != "export") || !args.isEmpty || !order.isEmpty then
        throw ("source export: record/type modifiers require ownership or nominal proof binding: " ++ name)
      if scope.types.any (fun entry => strEq entry.1 name) then
        throw ("source export: duplicate type declaration: " ++ name)
      match body with
      | .raw _ =>
        let fields ← expandRecord (items.length + 1) items [] name
        if (fields.map (·.fname)).eraseDups.length != fields.length then
          throw ("source export: duplicate record field: " ++ name)
        if fields.any uRecordFieldMetadata then
          throw ("source export: record field placement/where/resource duties are unsupported: " ++ name)
        match fields.mapM (fun field => uRecordField scope alias tabs field eigner spaces) with
        | .error _ => pure (scope, deferred ++ [(identity, item)])
        | .ok resolved =>
          let schema : URecord :=
            { name := name
              identity := identity
              fields := resolved
              modifiers := flags
              breiten := uFeldBreiten widths fields }
          pure (
            { types := scope.types ++ [(name, schema.ty)]
              records := scope.records ++ [schema] }, deferred)
      | _ =>
        match uTypIn alias tabs scope.types spaces eigner body with
        | .error _ => pure (scope, deferred ++ [(identity, item)])
        | .ok ty => pure ({ scope with types := scope.types ++ [(name, ty)] }, deferred)
    | _ => throw "source export: type declaration has no value schema") (scope, [])

/-- There are at most as many productive passes as declarations. Cycles and missing names fail closed. -/
def uResolveTypes (items : List SItemTief) (eigner : List String := []) (spaces : List String := [])
    (widths : List (String × (Int × Int)) := []) : Nat → UTypeScope → List (String × (Int × Int)) → List UTab →
    List (Nat × SItemTief) → Except String UTypeScope
  | _, scope, _, _, [] => .ok scope
  | 0, _, _, _, _ => .error "source export: cyclic or unresolved by-value record schema"
  | fuel + 1, scope, alias, tabs, pending => do
    let (next, deferred) ← uTypePass scope alias tabs items pending eigner spaces widths
    if deferred.length < pending.length then uResolveTypes items eigner spaces widths fuel next alias tabs deferred
    else throw "source export: cyclic, unsupported or unresolved by-value record schema"

/-- Tagged declarations and linear resources retain their separate canonical collectors.
    Every ordinary value type resolves here. -/
def uTypes (constants : List (String × Int)) (alias : List (String × (Int × Int)))
    (tabs : List UTab) (items : List SItemTief) (eigner : List String := []) (spaces : List String := [])
    (widths : List (String × (Int × Int)) := []) : Except String UTypeScope :=
  let pending := (List.range items.length).zip items |>.filter fun (_, item) =>
    match item with
    | .typeT flags .. => !flags.any (fun flag => strEq flag "tagged" || strEq flag "linear")
    | _ => false
  uResolveTypes items eigner spaces widths pending.length { types := constants.map (fun (name, value) => (name, .int value value)) } alias tabs pending

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
  induction records generalizing schema with
  | nil => cases h
  | cons head rest ih =>
    simp only [uRecordOf] at h
    split at h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih schema h)

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

/-- A common source type for ordered array elements. This only selects the checking
    type: the dependent lowerer still checks every element and every bound. -/
def uArrayElementType : Ty → Ty → Option Ty
  | .int a b, .int c d => some (.int (min a c) (max b d))
  | .arr a n, .arr b m =>
    if n = m then (uArrayElementType a b).map (.arr · n) else none
  | a, b => if a = b then some a else none

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
  | .arrCons value .arrNil => do
    let ty ← uValueType ctx value
    pure (.arr ty 1)
  | .arrCons value rest => do
    let head ← uValueType ctx value
    let .arr tail count ← uValueType ctx rest | none
    let ty ← uArrayElementType head tail
    pure (.arr ty (count + 1))
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

/-- A declared field's source value is smaller than the actual containing field list. -/
theorem recordField_sizeOf_lt (fields : List (Ty × USide)) (field : Ty × USide)
    (member : field ∈ fields) : sizeOf field.2 < sizeOf fields := by
  rcases field with ⟨ty, side⟩
  have component : sizeOf side < sizeOf (ty, side) := by simp +arith
  exact Nat.lt_trans component (List.sizeOf_lt_of_mem member)

/-- Explicit product initializers retain every field. Zero is an integer field, never a missing field. -/
def uConstantValue : USide → Except String UKonst
  | .lit value => pure (.zahl value)
  | .truth value => pure (.wahr value)
  | .text bytes => pure (.text bytes)
  | .product name _ fields => do pure (.product name (← fields.mapM (fun field => uConstantValue field.2)))
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
termination_by source => sizeOf source
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | have smaller := recordField_sizeOf_lt _ _ ‹_ ∈ _›
      omega

/-- One record component, shared by construction and replacement. The callback receives the
    original component with a non-increasing size bound, connecting nested source recursion.
    The dependent lowerer checks the component at the field's declared type. -/
def uRecordSide (ctx : UCtx) : (value : SExpr) →
    ((source : SExpr) → sizeOf source ≤ sizeOf value → Except String USide) → Except String USide
  | .tru, _ => pure (.truth true)
  | .fls, _ => pure (.truth false)
  | .variable name, rechne =>
    match uParamNr ctx name with
    | .ok position =>
      match ctx.kinds[position]? with
      | some .bool => pure (.param name)
      | _ => rechne (.variable name) (Nat.le_refl _)
    | .error _ => rechne (.variable name) (Nat.le_refl _)
  | value, rechne => rechne value (Nat.le_refl _)

/-- Array elements share the canonical component reader. Every recursive callback
    concerns an actual smaller element of the original list, in source order. -/
def uArraySides (ctx : UCtx) : (values : List SExpr) →
    ((source : SExpr) → sizeOf source < sizeOf values → Except String USide) → Except String USide
  | [], _ => .ok .arrNil
  | value :: rest, read => do
    let head ← uRecordSide ctx value fun source smaller => read source (by
      have nested : sizeOf value < sizeOf (value :: rest) := by simp +arith
      exact Nat.lt_of_le_of_lt smaller nested)
    let tail ← uArraySides ctx rest fun source smaller => read source (by
      have nested : sizeOf rest < sizeOf (value :: rest) := by simp +arith
      exact Nat.lt_trans smaller nested)
    pure (.arrCons head tail)
termination_by structural values _ => values

/-- Labelled constructors arrive as `.ext .label` applications in source order. Every callback
    argument is smaller than this actual source list, including across recursive tails. -/
def uRecordSides (ctx : UCtx) : (args : List SExpr) →
    ((source : SExpr) → sizeOf source < sizeOf args → Except String USide) →
    Except String (List (String × USide))
  | [], _ => .ok []
  | .ext .label [label] [value] :: rest, rechne => do
    let side ← uRecordSide ctx value fun source smaller =>
      rechne source (by
        have nested : sizeOf value < sizeOf (SExpr.ext .label [label] [value] :: rest) := by
          simp +arith
        exact Nat.lt_of_le_of_lt smaller nested)
    let tail ← uRecordSides ctx rest fun source smaller =>
      rechne source (by
        have tail : sizeOf rest < sizeOf (SExpr.ext .label [label] [value] :: rest) := by
          simp +arith
        exact Nat.lt_trans smaller tail)
    pure ((label, side) :: tail)
  | _, _ => .error "source export: record construction requires labelled fields"
termination_by structural args _ => args

/-- The tables with their fields of a record type typed (`werte`): a field whose type names a record
    of the unit holds a value of that record. The remaining named fields are those of tagged types
    (`uSumTabs`). A table without such a field is returned as it is. -/
def uRecordTabs (records : List URecord) (tabs : List UTab) : List UTab :=
  tabs.map fun t =>
    let hit := t.sumNamen.filterMap fun (f, a) =>
      (records.find? fun record => strEq record.name a).map fun record => (f, record.ty)
    if hit.isEmpty then t
    else
      { t with
        werte := t.werte ++ hit
        sumNamen := t.sumNamen.filter fun (_, a) => !records.any fun record => strEq record.name a }

end Gabbro.Grammatik.Parser.Uebersetze
