module

public import Grammatik.Parser.Elab.Uebersetze.Folds.Substitution
public import Grammatik.Parser.Elab.Uebersetze.Folds.ConstantBytes

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Typed value paths consist of a name and ordinary record projections.
    Their types come from the lexical declaration and its record schema. -/
def uSpecValuePath : SExpr → Bool
  | .variable _ => true
  | .field base _ => uSpecValuePath base
  | _ => false

/-- A literal field is checked against the constructor's declared type
    before substitution, including integer ranges and UTF-8 capacity. -/
def specPrimitiveLiteralFieldFits : Ty → USide → Bool
  | .int lo hi, .lit value => decide (lo ≤ value ∧ value ≤ hi)
  | .bool, .truth _ => true
  | .str capacity, .text bytes =>
    match bytesZahl bytes with
    | some decoded => decide (decoded.length ≤ capacity)
    | none => false
  | _, _ => false

def specLiteralFieldFits (records : List URecord) : USide → Ty → Bool
  | .arrNil, type =>
    match type with
    | .arr _ 0 => true
    | _ => false
  | .arrCons first rest, type =>
    match type with
    | .arr element (length + 1) =>
      specLiteralFieldFits records first element && specLiteralFieldFits records rest (.arr element length)
    | _ => false
  | .product identity _ fields, type =>
    decide (type = .prod identity (fields.map Prod.fst)) &&
      (uRecordOf records type).isOk &&
      fields.attach.all (fun field => specLiteralFieldFits records field.val.2 field.val.1)
  | value, type => specPrimitiveLiteralFieldFits type value
termination_by value _ => sizeOf value
decreasing_by
  all_goals
    simp_wf
    first
    | have smaller := recordField_sizeOf_lt fields field.val field.property
      omega
    | omega

/-- An array constructor can also read immutable or mutable lexical
    values of the declared element type. Each nested array preserves
    its own length and type, including empty tails. -/
def specArrayArgumentFits (ctx : UCtx) : USide → Ty → Bool
  | .arrCons head tail, .arr element (length + 1) =>
    specArrayArgumentFits ctx head element && specArrayArgumentFits ctx tail (.arr element length)
  | .param name, expected =>
    !ctx.unknownRanges.contains name && decide (uValueType ctx (.param name) = some expected)
  | value, expected => specLiteralFieldFits ctx.records value expected

/-- Check the nominal schema and each already ordered field returned
    by the ordinary constructor reader. Unused arguments are checked too. -/
def uSpecLiteralRecordType (ctx : UCtx) (name : String) (identity : Nat)
    (fields : List (Ty × USide)) : Option Ty := do
  let schema ← uRecordConstructor ctx name
  if schema.ty = .prod identity (fields.map Prod.fst) ∧
    fields.all (fun field => specLiteralFieldFits ctx.records field.2 field.1) = true then
    some schema.ty
  else none

/-- Before substitution, read the exact type of each supported value.
    Strings use decoded byte lengths, checked literal slice ranges,
    declared path bounds and the ordinary G rule for concatenation.
    An array slice uses the element type and extent of its checked base. -/
def uSpecValueType (ctx : UCtx) : SExpr → USide → Option Ty
  | .built "#spec-array" [_, _, _], .typed type literal =>
    if specArrayArgumentFits ctx literal type then some type else none
  | .call name _, .product identity _ fields => uSpecLiteralRecordType ctx name identity fields
  | .ext .text [_] [], .text bytes => (bytesZahl bytes).map fun decoded => Ty.str decoded.length
  | .built "#slice" [.ext .text [_] [], _, _], .slice (.text bytes) first last => do
    let decoded ← bytesZahl bytes
    if first ≤ last ∧ last ≤ decoded.length then some (.str (last - first)) else none
  | .built "#slice" [base, _, _], .slice operand first last => do
    let some (.arr element capacity) := uSpecValueType ctx base operand | none
    if first ≤ last ∧ last ≤ capacity then some (.arr element (last - first)) else none
  | .index base _, .idx operand index => do
    let some (.arr element capacity) := uSpecValueType ctx base operand | none
    let (lo, hi) ← foldRangeWithIndexCheck ctx true index
    if 0 ≤ lo ∧ hi < (capacity : Int) then some element else none
  | .field base name, .field operand field => do
    if !strEq name field then none else
      let ty ← uSpecValueType ctx base operand
      let schema ← (uRecordOf ctx.records ty).toOption
      let position ← (uRecordPosition schema.val.fields field).toOption
      pure position.1
  | .bin "+" lhs rhs, .add a b => do
    let some (.str left) := uSpecValueType ctx lhs a | none
    let some (.str right) := uSpecValueType ctx rhs b | none
    pure (.str (left + right))
  | argument, side => if uSpecValuePath argument then uValueType ctx side else none

/-- Compare the full value type, including nominal record identity, array
    shape and string bound, before substituting into the predicate. -/
def uSpecValueArgument (ctx : UCtx) (expected : Ty) (argument : SExpr) : Except String Unit := do
  let side ← uWertBody ctx argument
  if uSpecValueType ctx argument side = some expected then pure ()
  else throw "spec value argument does not have the declared type"

theorem uSpecValueArgument_exact {ctx : UCtx} {expected : Ty} {argument : SExpr}
    (accepted : uSpecValueArgument ctx expected argument = .ok ()) :
    ∃ side, uWertBody ctx argument = .ok side ∧
      uSpecValueType ctx argument side = some expected := by
  cases read : uWertBody ctx argument with
  | error err => simp [uSpecValueArgument, read, bind, Except.bind] at accepted
  | ok side =>
    by_cases typeMatches : uSpecValueType ctx argument side = some expected
    · exact ⟨side, rfl, typeMatches⟩
    · simp [uSpecValueArgument, read, typeMatches, bind, Except.bind] at accepted

theorem specValueArgument_erfuellbar (ctx : UCtx) (name : String) (expected : Ty)
    (read : uWertBody ctx (.variable name) = .ok (.param name))
    (typeMatches : uValueType ctx (.param name) = some expected) :
    uSpecValueArgument ctx expected (.variable name) = .ok () := by
  simp [uSpecValueArgument, uSpecValueType, uSpecValuePath, read, typeMatches,
    bind, Except.bind, pure, Except.pure]

/-- The premises hold for any parsed constructor and every list of
    jointly well-typed literal fields in its nominal schema. -/
theorem specLiteralRecordArgument_erfuellbar (ctx : UCtx) (name : String) (args : List SExpr)
    (schema : URecord) (fields : List (Ty × USide)) (reordered : Bool)
    (selected : uRecordConstructor ctx name = some schema)
    (read : uWertBody ctx (.call name args) = .ok (.product schema.identity reordered fields))
    (shape : schema.ty = .prod schema.identity (fields.map Prod.fst))
    (valid : fields.all (fun field => specLiteralFieldFits ctx.records field.2 field.1) = true) :
    uSpecValueArgument ctx schema.ty (.call name args) = .ok () := by
  simp only [uSpecValueArgument, bind, Except.bind, read, uSpecValueType, uSpecLiteralRecordType,
    selected, Option.bind_eq_bind, Option.bind_some, shape, valid, true_and, ite_true,
    pure, Except.pure]

/-- The literal lane accepts exactly the type of the checked byte list. -/
theorem specTextArgument_erfuellbar (ctx : UCtx) (text : String) :
    uSpecValueArgument ctx (.str text.toUTF8.toList.length) (.ext .text [text] []) = .ok () := by
  obtain ⟨decoded, valid⟩ := bytesZahl_uint8 text.toUTF8.toList
  have length := bytesZahl_laenge _ decoded valid
  rw [List.length_map] at length
  have parsed : uWertBody ctx (.ext .text [text] []) =
      .ok (.text (text.toUTF8.toList.map fun b => Int.ofNat b.toNat)) := by
    simp only [uWertBody, uRechne]
  simp only [uSpecValueArgument, parsed, bind, Except.bind, uSpecValueType, valid,
    Option.map_some, length, ite_true] <;> rfl

/-- A checked literal substring uses the same half-open UTF-8 byte
    interval during argument checking and ordinary source elaboration. -/
theorem specTextSliceArgument_erfuellbar (ctx : UCtx) (text : String) (first last : Nat)
    (bounds : first ≤ last ∧ last ≤ text.toUTF8.toList.length) :
    let argument := SExpr.built "#slice" [.ext .text [text] [], .lit first, .lit last]
    let bytes := text.toUTF8.toList.map (fun byte => Int.ofNat byte.toNat)
    uWertBody ctx argument = .ok (.slice (.text bytes) first last) ∧
      uSpecValueArgument ctx (.str (last - first)) argument = .ok () := by
  intro argument bytes
  have nonnegative : ¬ (first : Int) < 0 := by omega
  have ordered : ¬ (last : Int) < first := by have low := bounds.1; omega
  have read : uWertBody ctx argument = .ok (.slice (.text bytes) first last) := by
    simp [argument, bytes, uWertBody, uRechne, uFixedLocalArraySlice, uFixedLocalArrayExtent, uFullLocalSlice, uSchranke,
      nonnegative, ordered, bind, Except.bind, pure, Except.pure]
  obtain ⟨decoded, valid⟩ := bytesZahl_uint8 text.toUTF8.toList
  have length := bytesZahl_laenge _ decoded valid
  rw [List.length_map] at length
  have inside : first ≤ last ∧ last ≤ decoded.length := ⟨bounds.1, length.symm ▸ bounds.2⟩
  refine ⟨read, ?_⟩
  simp only [uSpecValueArgument, read, bind, Except.bind, argument, uSpecValueType, bytes, valid,
    Option.bind_some, inside, and_self, ite_true, pure, Except.pure] <;> rfl

/-- The ordinary source reader keeps a concatenation of accepted
    arguments as the same pair of operands through the precheck. -/
theorem specStringConcatArgument_erfuellbar (ctx : UCtx) (lhs rhs : SExpr) (left right : Nat)
    (leftAccepted : uSpecValueArgument ctx (.str left) lhs = .ok ())
    (rightAccepted : uSpecValueArgument ctx (.str right) rhs = .ok ()) :
    ∃ a b, uWertBody ctx (.bin "+" lhs rhs) = .ok (.add a b) ∧
      uSpecValueArgument ctx (.str (left + right)) (.bin "+" lhs rhs) = .ok () := by
  obtain ⟨a, readLeft, typedLeft⟩ := uSpecValueArgument_exact leftAccepted
  obtain ⟨b, readRight, typedRight⟩ := uSpecValueArgument_exact rightAccepted
  have read : uWertBody ctx (.bin "+" lhs rhs) = .ok (.add a b) := by
    change uRechne ctx (uWertBlatt ctx) (.bin "+" lhs rhs) = _
    rw [uRechne]
    have plus : strEq "+" "+" = true := rfl
    unfold uWertBody at readLeft readRight
    simp only [plus, Bool.true_or, ite_true, readLeft, readRight]
  exact ⟨a, b, read, by
    simp only [uSpecValueArgument, bind, Except.bind, read, uSpecValueType, typedLeft, typedRight,
      pure, Option.pure_def, Except.pure, ite_true]⟩

/-- Before inlining a static array slice, check both the original base
    and the actual interval. The resulting array retains its element type. -/
theorem specArraySliceArgument_of_local (ctx : UCtx) (name : String) (element : Ty)
    (capacity first last : Nat) (bounds : first ≤ last ∧ last ≤ capacity)
    (read : uWertBody ctx (.variable name) = .ok (.param name))
    (baseType : uValueType ctx (.param name) = some (.arr element capacity)) :
    let argument := SExpr.built "#slice" [.variable name, .lit first, .lit last]
    uWertBody ctx argument = .ok (.slice (.param name) first last) ∧
      uSpecValueArgument ctx (.arr element (last - first)) argument = .ok () := by
  intro argument
  have nonnegative : ¬ (first : Int) < 0 := by omega
  have ordered : ¬ (last : Int) < first := by have low := bounds.1; omega
  have parsed : uWertBody ctx argument = .ok (.slice (.param name) first last) := by
    change uRechne ctx (uWertBlatt ctx) (.variable name) = _ at read
    simp [argument, uWertBody, uRechne, uFixedLocalArraySlice, uFixedLocalArrayExtent, uFullLocalSlice,
      uSchranke, read, nonnegative, ordered, bind, Except.bind, pure, Except.pure]
  exact ⟨parsed, by
    simp only [uSpecValueArgument, parsed, bind, Except.bind, argument, uSpecValueType, uSpecValuePath,
      baseType, bounds, and_self, ite_true, Option.bind_some, pure, Except.pure] <;> rfl⟩

private theorem specArrayLocal (element : Ty) (capacity : Nat) :
    ∃ ctx : UCtx,
      uWertBody ctx (.variable "array") = .ok (.param "array") ∧
      uValueType ctx (.param "array") = some (.arr element capacity) ∧
      uTraegerIndex ctx (.variable "array") = false := by
  let ctx : UCtx := {
    names := ["array"], kinds := [.wert], types := [.arr element capacity],
    tabs := [], locks := [], held := [], res := none, fname := "", alias := [], lits := [] }
  have read : uWertBody ctx (.variable "array") = .ok (.param "array") := by
    simp [ctx, uWertBody, uRechne, uWertBlatt, uParamNr, uParamNrAux, uArtBei, strEq_apply_eq_decide]
  have baseType : uValueType ctx (.param "array") = some (.arr element capacity) := by
    simp [ctx, uValueType, strEq_apply_eq_decide, List.findIdx?_cons]
  exact ⟨ctx, read, baseType, rfl⟩

theorem specArraySliceArgument_erfuellbar (element : Ty) (capacity first last : Nat)
    (bounds : first ≤ last ∧ last ≤ capacity) :
    ∃ ctx : UCtx,
      uWertBody ctx (.variable "array") = .ok (.param "array") ∧
      uValueType ctx (.param "array") = some (.arr element capacity) ∧
      uSpecValueArgument ctx (.arr element (last - first))
        (.built "#slice" [.variable "array", .lit first, .lit last]) = .ok () := by
  obtain ⟨ctx, read, baseType, _⟩ := specArrayLocal element capacity
  exact ⟨ctx, read, baseType, (specArraySliceArgument_of_local ctx "array" element capacity first last
    bounds read baseType).2⟩

/-- An aggregate array element must be in bounds even when substitution
    erases the argument from the predicate's body. -/
theorem specArrayIndexArgument_of_local (ctx : UCtx) (name : String) (element : Ty)
    (capacity index : Nat) (inside : index < capacity)
    (read : uWertBody ctx (.variable name) = .ok (.param name))
    (baseType : uValueType ctx (.param name) = some (.arr element capacity))
    (array : uTraegerIndex ctx (.variable name) = false) :
    let argument := SExpr.index (.variable name) (.lit index)
    uWertBody ctx argument = .ok (.idx (.param name) (.lit index)) ∧
      uSpecValueArgument ctx element argument = .ok () := by
  intro argument
  have parsed : uWertBody ctx argument = .ok (.idx (.param name) (.lit index)) := by
    change uRechne ctx (uWertBlatt ctx) (.variable name) = _ at read
    simp only [argument, uWertBody, uRechne, uSliceObservation, uSliceView, uRelativeSlice, array, Bool.false_eq_true, ite_false, read] <;> rfl
  have valid : (0 : Int) ≤ index ∧ (index : Int) < capacity := ⟨Int.ofNat_zero_le _, Int.ofNat_lt.mpr inside⟩
  exact ⟨parsed, by
    simp only [uSpecValueArgument, parsed, bind, Except.bind, argument, uSpecValueType, uSpecValuePath, baseType,
      foldRangeWithIndexCheck, Option.bind_some, valid, and_self, ite_true, pure, Except.pure] <;> rfl⟩

theorem specArrayIndexArgument_erfuellbar (element : Ty) (capacity index : Nat) (inside : index < capacity) :
    ∃ ctx : UCtx,
      uWertBody ctx (.variable "array") = .ok (.param "array") ∧
      uValueType ctx (.param "array") = some (.arr element capacity) ∧
      uTraegerIndex ctx (.variable "array") = false ∧
      uSpecValueArgument ctx element (.index (.variable "array") (.lit index)) = .ok () := by
  obtain ⟨ctx, read, baseType, array⟩ := specArrayLocal element capacity
  exact ⟨ctx, read, baseType, array,
    (specArrayIndexArgument_of_local ctx "array" element capacity index inside read baseType array).2⟩

/-- A projection retains the prechecked base and uses the same nominal
    schema and field index as dependent record lowering. -/
theorem specFieldArgument_of_checked (ctx : UCtx) (base : SExpr) (field : String)
    {operand : USide} {parent target : Ty} {schema : {s : URecord // s.ty = parent}}
    {position : FieldAt (schema.val.fields.map (·.2)) target}
    (read : uWertBody ctx (.field base field) = .ok (.field operand field))
    (typed : uSpecValueType ctx base operand = some parent)
    (nominal : uRecordOf ctx.records parent = .ok schema)
    (selected : uRecordPosition schema.val.fields field = .ok ⟨target, position⟩) :
    uSpecValueArgument ctx target (.field base field) = .ok () := by
  have same : strEq field field = true := by simp [strEq_apply_eq_decide]
  simp only [uSpecValueArgument, read, bind, Except.bind, uSpecValueType, same, Bool.not_true,
    Bool.false_eq_true, ite_false, typed, nominal, selected, Option.bind_some,
    Except.toOption, pure, Option.pure_def, Except.pure, ite_true]

/-- A field of an indexed local record is a compound argument and all
    source obligations hold together for every in-bounds index. -/
theorem specIndexedFieldArgument_erfuellbar (field : String) (target : Ty)
    (identity capacity index : Nat) (inside : index < capacity) :
    ∃ ctx : UCtx,
      let base := SExpr.index (.variable "array") (.lit index)
      uWertBody ctx (.field base field) =
        .ok (.field (.idx (.param "array") (.lit index)) field) ∧
      uSpecValueArgument ctx target (.field base field) = .ok () := by
  let schema : URecord := { name := "record", identity, fields := [(field, target)] }
  let ctx : UCtx := {
    names := ["array"], kinds := [.wert], types := [.arr schema.ty capacity], records := [schema],
    tabs := [], locks := [], held := [], res := none, fname := "", alias := [], lits := [] }
  let base := SExpr.index (.variable "array") (.lit index)
  let operand := USide.idx (.param "array") (.lit index)
  have arrayRead : uWertBody ctx (.variable "array") = .ok (.param "array") := by
    simp [ctx, uWertBody, uRechne, uWertBlatt, uParamNr, uParamNrAux, uArtBei, strEq_apply_eq_decide]
  have baseType : uValueType ctx (.param "array") = some (.arr schema.ty capacity) := by
    simp [ctx, uValueType, strEq_apply_eq_decide, List.findIdx?_cons]
  have access : uTraegerIndex ctx (.variable "array") = false := rfl
  obtain ⟨baseRead, baseAccepted⟩ :=
    specArrayIndexArgument_of_local ctx "array" schema.ty capacity index inside arrayRead baseType access
  have typed : uSpecValueType ctx base operand = some schema.ty := by
    obtain ⟨parsed, read, type⟩ := uSpecValueArgument_exact baseAccepted
    have same : parsed = operand := Except.ok.inj (read.symm.trans baseRead)
    rw [same] at type
    exact type
  have nominal : uRecordOf ctx.records schema.ty = .ok ⟨schema, rfl⟩ := by
    simp only [ctx, uRecordOf, dite_true]
  have same : strEq field field = true := by simp [strEq_apply_eq_decide]
  have selected : uRecordPosition schema.fields field = .ok ⟨target, .head⟩ := by
    simp only [schema, uRecordPosition, same, ite_true]
  have read : uWertBody ctx (.field base field) = .ok (.field operand field) := by
    change uRechne ctx (uWertBlatt ctx) base = .ok operand at baseRead
    simp only [uWertBody, uRechne, baseRead] <;> rfl
  exact ⟨ctx, read, specFieldArgument_of_checked ctx base field read typed nominal selected⟩

/-- An explicit array literal gets the declared element type even when
    it is empty or its elements are independently narrower. -/
def uSpecArrayArgument (ctx : UCtx) (expected : Ty) (argument : SExpr) : Except String Unit := do
  let value ← uWertBody ctx argument
  if specArrayArgumentFits ctx value expected then pure ()
  else throw "spec array literal does not fit its declared element type or length"

/-- Reuse annotated local elaboration and the existing integer interval calculation.
    Structured and floating values must match the declared type exactly. -/
def uSpecArgument (ctx : UCtx) (g : String) (i : Nat) (ty : STyp) (arg : SExpr) :
    Except String Unit :=
  let checked : Except String Unit := do
    let expected ← uTypIn ctx.alias ctx.tabs ctx.namedTypes ctx.spaces ctx.eigner ty
    match expected with
    | .bool =>
      let _ ← uBool ctx arg
      pure ()
    | .int .. =>
      let (statement, _) ← uBindWertAllg ctx false "#spec-argument" (some ty) arg
      let .bind _ (some (lo, hi)) value := statement
        | throw "spec argument is not an annotated integer binding"
      let some range := foldRangeWithIndexCheck ctx true value
        | throw "spec argument interval is unresolved"
      if lo ≤ range.1 ∧ range.2 ≤ hi then pure ()
      else throw "spec argument is outside its annotated range"
    | .arr .. =>
      match arg with
      | .ext .array [] _ => uSpecArrayArgument ctx expected arg
      | _ => uSpecValueArgument ctx expected arg
    | .prod .. | .str .. | .fl .. =>
      uSpecValueArgument ctx expected arg
    | _ => throw "spec parameter type is unsupported"
  match checked with
  | .ok () => .ok ()
  | .error _ => .error ("spec " ++ g ++ ": argument " ++ toString i ++
      " does not fit its parameter type")

/-- Retain the index of the caller-checked array type in the original
    declaration catalog. Neither this marker nor its numeric indices
    introduce a name that could be captured by substitution. -/
def uSpecAscribeArrays (ctx : UCtx) (name : String) (args : List SExpr) : List SExpr :=
  match ctx.specTypen.findIdx? (fun entry => strEq entry.1 name) with
  | none => args
  | some specIndex =>
    args.zipIdx.map fun (argument, index) =>
      match argument with
      | .ext .array [] _ => .built "#spec-array" [.lit specIndex, .lit index, argument]
      | _ => argument

theorem uSpecAscribeArray_exact (ctx : UCtx) (name : String) (elements : List SExpr)
    {specIndex : Nat}
    (selected : ctx.specTypen.findIdx? (fun entry => strEq entry.1 name) = some specIndex) :
    uSpecAscribeArrays ctx name [.ext .array [] elements] =
      [.built "#spec-array" [.lit specIndex, .lit 0, .ext .array [] elements]] := by
  simp only [uSpecAscribeArrays, selected]
  rfl

def uSpecEinTyped (ctx : UCtx) : Nat → SExpr → SExpr :=
  uSpecEinUsing ctx.specs (uSpecAscribeArrays ctx)

/-- Check every original call before inlining, including calls brought by a helper's body.
    Argument expressions use the caller's scope; quantifiers extend it with their real domain.
    Exhausted expansion refuses instead of allowing an unchecked recursive helper. -/
def uSpecArgs : Nat → UCtx → SExpr → Except String Unit
  | 0, _, _ => .error "spec argument checking exceeded its expansion depth"
  | n + 1, ctx, e => do
    match e with
    | .call g args =>
      for arg in args do uSpecArgs n ctx arg
      match ctx.specs.find? (fun p => strEq p.1 g) with
      | some (_, _, body) =>
        for (arg, i) in args.zipIdx do
          if specArgumentCaptures body (uSpecEinTyped ctx n arg) then
            throw ("spec " ++ g ++ ": argument " ++ toString (i + 1) ++
              " names a binder of the predicate")
      | none => pure ()
      match ctx.specTypen.find? (fun p => strEq p.1 g) with
      | some (_, types) =>
        if args.length != types.length then
          throw ("spec " ++ g ++ ": argument " ++ toString (min args.length types.length + 1) ++
            " does not fit its parameter type")
        for ((ty, arg), i) in (types.zip args).zipIdx do
          uSpecArgument ctx g (i + 1) ty (uSpecEinTyped ctx n arg)
      | none => pure ()
      match ctx.specs.find? (fun p => strEq p.1 g) with
      | some (_, names, body) =>
        if names.length == args.length then
          uSpecArgs n ctx (sErsetze (names.zip (uSpecAscribeArrays ctx g args)) 1000 body)
        else throw ("spec " ++ g ++ ": argument count does not fit its parameter type")
      | none => pure ()
    | .field a _ | .arrow a _ | .un _ a | .old a => uSpecArgs n ctx a
    | .index a b | .bin _ a b =>
      uSpecArgs n ctx a
      uSpecArgs n ctx b
    | .ext k [binder, domain] [subject, body] =>
      if k == .all || k == .any || k == .count then
        uSpecArgs n ctx subject
        -- Read the predicate domain directly: array quantifiers need no traversal carrier.
        let inner ← if domain == "elems" then do
            let (_, _, count) ← uArrayDomain ctx subject
            pure (uMitLokal ctx binder .int (Ty.index count) ctx.muts)
          else do
            let (_, inner, _) ← uLoopExport ctx binder none domain subject "unvisited" "" none
            pure inner
        uSpecArgs n inner body
      else
        uSpecArgs n ctx subject
        uSpecArgs n ctx body
    | .built _ args | .ext _ _ args =>
      for arg in args do uSpecArgs n ctx arg
    | _ => pure ()

end Gabbro.Grammatik.Parser.Uebersetze
