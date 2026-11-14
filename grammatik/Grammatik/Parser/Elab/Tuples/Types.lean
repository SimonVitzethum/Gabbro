module
public import Grammatik.Parser.Spec.Items
public import Grammatik.Parser.Elab.Uebersetze.Records.Records
public import Grammatik.Parser.Print.Stmt
public import Grammatik.Parser.Elab.Konst.Scalar.Names
public import Grammatik.Parser.Elab.Tuples.Natural
@[expose] public section

namespace Gabbro.Grammatik.Parser.Tuples
open Uebersetze

/-- Tuple expansion is unit-local. The ordinary exporter remains the type checker. -/
structure Context where
  items : List SItemTief
  constants : List (String × Int)
  aliases : List (String × (Int × Int))
  sourceTypes : UTypeScope := { types := [] }
  environment : Spec.Umfeld := Spec.Umfeld.von items

structure TypeKey where
  resolved : Option Ty
  surface : STyp
  width : Nat

def sameTypeKey (a b : TypeKey) : Bool :=
  a.width == b.width && match a.resolved, b.resolved with
    | some a, some b => a == b
    | _, _ => beqSTyp a.surface b.surface

def sameKeys (as bs : List TypeKey) : Bool :=
  as.length == bs.length && (as.zip bs).all (fun (a, b) => sameTypeKey a b)

structure Record where
  name : String
  elements : List STyp
  key : List TypeKey

structure State where
  records : List Record := []
  nextLocal : Nat := 0

abbrev ExpandM := StateT State (Except String)

def lift {α : Type} (result : Except String α) : ExpandM α :=
  fun state => do pure (← result, state)

/-- Transparent aliases stop at nominal record declarations. Unresolved names stay distinct. -/
def canonical (k : Context) : Nat → STyp → STyp
  | 0, ty => ty
  | fuel + 1, .atom name =>
    match k.items.find? (fun
        | .typeT flags n [] [] (some _) => strEq n name &&
            flags.all (fun flag => strEq flag "pub" || strEq flag "export")
        | _ => false) with
    | some (.typeT _ _ _ _ (some (.raw _))) => .atom name
    | some (.typeT _ _ _ _ (some ty)) => canonical k fuel ty
    | _ => .atom name
  | fuel + 1, .tuple types => .tuple (types.map (canonical k fuel))
  | fuel + 1, .array ty count => .array (canonical k fuel ty) count
  | fuel + 1, .ptr space rights ty => .ptr space rights (canonical k fuel ty)
  | _, ty => ty
termination_by structural fuel => fuel

/-- Resolved G types identify equal intervals and aliases. The fallback retains nominal names;
    actual schema collection below also interns by resolved element types. -/
def typeKey (k : Context) (ty : STyp) : TypeKey :=
  let ty := canonical k (k.items.length + 1) ty
  { resolved := (uTypIn k.aliases [] k.sourceTypes.types [] [] ty).toOption
    surface := ty
    width := uSpeicherBreite k.aliases ty }

/-- No hash: structural equality decides reuse. Reserved `#tuple:` names cannot be source
    identifiers, and the enclosing module pipeline checks generated-name provenance as well. -/
def intern (k : Context) (elements : List STyp) : ExpandM STyp := do
  if elements.length < 2 then lift (.error "tuple type: at least two elements required")
  let state ← get
  let key := elements.map (typeKey k)
  match state.records.find? (fun record => sameKeys record.key key) with
  | some record => pure (.atom record.name)
  | none =>
    let name := uTuplePrefix k.aliases elements ++ toString state.records.length
    set { state with records := state.records ++ [({ name := name, elements := elements, key := key } : Record)] }
    pure (.atom name)

/-- Generated records are represented structurally in the frontend, avoiding a round trip
    through raw field text (reserved generated names are deliberately not lexer identifiers). -/
def Record.declaration (record : Record) : SItemTief :=
  .typeT [] record.name [] [] (some (.tuple record.elements))

def expandType (k : Context) : Nat → STyp → ExpandM STyp
  | 0, _ => lift (.error "tuple expansion: type fuel exhausted")
  | fuel + 1, .tuple types => do intern k (← types.mapM (expandType k fuel))
  | fuel + 1, .atom name =>
    match canonical k (k.items.length + 1) (.atom name) with
    | .tuple types => expandType k fuel (.tuple types)
    | _ => pure (.atom name)
  | fuel + 1, .ptr space rights ty => return .ptr space rights (← expandType k fuel ty)
  | fuel + 1, .range ty lo hi ex => return .range (← expandType k fuel ty) lo hi ex
  | fuel + 1, .array ty count => return .array (← expandType k fuel ty) count
  | fuel + 1, .wrap ty => return .wrap (← expandType k fuel ty)
  | fuel + 1, .embed ty bits scale => return .embed (← expandType k fuel ty) bits scale
  | fuel + 1, .entry params result => return .entry params (← result.mapM (expandType k fuel))
  | _, ty => pure ty
termination_by structural fuel => fuel

/-- Tuple field order is the generated record's declaration order. -/
def tupleElements (k : Context) (state : State) (ty : STyp) : Option (List STyp) :=
  match canonical k (k.items.length + 1) ty with
  | .tuple elements => some elements
  | .atom name => (state.records.find? (fun record => strEq record.name name)).map (·.elements)
  | _ => none

/-- Ordinary record fields retain their original names, types and metadata. -/
def recordFields (k : Context) (ty : STyp) : Option (List SFeld) := do
  let .atom name := canonical k (k.items.length + 1) ty | none
  (expandRecord (k.items.length + 1) k.items [] name).toOption

def position (field : String) : Option Nat :=
  match field.toList with
  | '_' :: digits => natural? (String.ofList digits)
  | _ => natural? field

def integerType (lo hi : Int) : STyp :=
  .range (.atom (if lo < 0 then "i64" else "u64"))
    (Konst.literalVonInt lo) (Konst.literalVonInt hi) false

def integerBounds (k : Context) (ty : STyp) : Option (Int × Int) := do
  let .int lo hi ← (uTypIn k.aliases [] k.sourceTypes.types [] []
    (canonical k (k.items.length + 1) ty)).toOption | none
  pure (lo, hi)

/-- Inference supplies types only for source sugar. Every constructed value is subsequently
    checked by the existing record and dependent product lowerers. -/
def infer (k : Context) (state : State) (locals : Spec.Locals) : Nat → SExpr → Option STyp
  | 0, _ => none
  | fuel + 1, .built "#tuple" values => do
    return .tuple (← values.mapM (infer k state locals fuel))
  | _, .lit n => some (.range (.atom "u64") (.lit n) (.lit n) false)
  | fuel + 1, .field base field => do
    let ty ← infer k state locals fuel base
    match position field, tupleElements k state ty with
    | some position, some elements => elements[position]?
    | _, _ =>
      match tupleElements k state ty with
      | some _ => none
      | none => ((recordFields k ty).bind fun fields =>
          (fields.find? (fun f => strEq f.fname field)).map (·.ftyp)).orElse fun _ =>
          Spec.inferTypeMit k.environment locals fuel (.field base field)
  | _, .call name args =>
    if state.records.any (fun record => strEq record.name name) ||
        (recordFields k (.atom name)).isSome then some (.atom name)
    else match uTypIn k.aliases [] k.sourceTypes.types [] [] (.atom name) with
      | .ok _ => some (.atom name)
      | .error _ => Spec.inferTypeMit k.environment locals 128 (.call name args)
  | fuel + 1, .un op value =>
    if strEq op "-" || strEq op "-()" then do
      let ty ← infer k state locals fuel value
      let (lo, hi) ← integerBounds k ty
      pure (integerType (-hi) (-lo))
    else if strEq op "!" then some (.atom "bool")
    else Spec.inferTypeMit k.environment locals 128 (.un op value)
  | fuel + 1, .bin op a b =>
    if ["+", "-", "*"].contains op then do
      let a ← infer k state locals fuel a
      let b ← infer k state locals fuel b
      let (al, ah) ← integerBounds k a
      let (bl, bh) ← integerBounds k b
      if strEq op "+" then pure (integerType (al + bl) (ah + bh))
      else if strEq op "-" then pure (integerType (al - bh) (ah - bl))
      else pure (integerType
        (imin (imin (al * bl) (al * bh)) (imin (ah * bl) (ah * bh)))
        (imax (imax (al * bl) (al * bh)) (imax (ah * bl) (ah * bh))))
    else Spec.inferTypeMit k.environment locals 128 (.bin op a b)
  | _, .res => (locals.find? (fun entry => strEq entry.1 "#tuple-result")).map (·.2)
  | _, value => Spec.inferTypeMit k.environment locals 128 value
termination_by structural fuel => fuel

end Gabbro.Grammatik.Parser.Tuples
