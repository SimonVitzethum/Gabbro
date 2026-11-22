module

public import Grammatik.Parser.Elab.UebersetzeAllg.Teil5
public import Grammatik.Kern.Syntax.Syntax.ProduktZucker
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

/-- The real expression lowerer emits the nominal constructor over the complete field list. -/
theorem record_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (identity : Nat) (reordered : Bool) (sides : List (Ty × USide))
    (args : Args (declOf u) Γ Λ (sides.map (·.1)))
    (gate : u.exportGate = .ok ())
    (lowered : lowProductArgs u Γ Λ fn er sides = .ok args)
    (schema : { s : URecord // s.ty = .prod identity (sides.map (·.1)) })
    (hschema : uRecordOf u.records (.prod identity (sides.map (·.1))) = .ok schema) :
    lowWertE u Γ Λ fn er (.product identity reordered sides) =
      .ok ⟨.prod identity (sides.map (·.1)), Expr.prod identity args⟩ := by
  simp only [lowWertE, gate, hschema, lowered, bind, Except.bind]

/-- Empty products use the canonical empty argument list in the same lexical/result scope. -/
theorem lowProductArgs_nil (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) : lowProductArgs u Γ Λ fn er [] = .ok .nil := by
  rw [lowProductArgs]

/-- Product fields use the actual checking-mode lowerer, with no separate callback instance. -/
theorem lowProductArgs_cons (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (ty : Ty) (side : USide) (rest : List (Ty × USide)) :
    lowProductArgs u Γ Λ fn er ((ty, side) :: rest) = (do
      let head ← lowWertAtE u Γ Λ fn er ty side
      let tail ← lowProductArgs u Γ Λ fn er rest
      pure (.cons head tail)) := by
  rw [lowProductArgs]

/-- Every literal field admitted by the predicate argument reader is
    accepted by the ordinary checking-mode expression elaborator. -/
private theorem specPrimitiveLiteralField_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (ty : Ty) (side : USide) (valid : specPrimitiveLiteralFieldFits ty side = true) :
    (∃ expression, lowWertAtE u Γ Λ fn er ty side = .ok expression) ∧
      (∃ expression : Expr (declOf u) Γ Λ ty, lowLit ty side = .ok expression) := by
  unfold specPrimitiveLiteralFieldFits at valid
  split at valid
  · rename_i lo hi value
    obtain ⟨loFits, hiFits⟩ := of_decide_eq_true valid
    refine ⟨?_, ⟨Expr.widen loFits hiFits (Expr.lit value),
      by simp only [lowLit, dite_eq_left loFits, dite_eq_left hiFits]⟩⟩
    by_cases same : Ty.int value value = .int lo hi
    · refine ⟨same ▸ Expr.lit value, ?_⟩
      simp only [lowWertAtE, lowWertE, LowSide.wert, fitW, dite_eq_left same]
    · refine ⟨Expr.widen loFits hiFits (Expr.lit value), ?_⟩
      simp only [lowWertAtE, lowWertE, LowSide.wert, fitW, dite_eq_right same,
        dite_eq_left loFits, dite_eq_left hiFits]
  · rename_i value
    cases value
    · exact ⟨⟨Expr.fls, by simp only [lowWertAtE, lowWertE, fitW, dite_true] <;> rfl⟩,
        ⟨Expr.fls, by simp only [lowLit]⟩⟩
    · exact ⟨⟨Expr.tru, by simp only [lowWertAtE, lowWertE, fitW, dite_true] <;> rfl⟩,
        ⟨Expr.tru, by simp only [lowLit]⟩⟩
  · rename_i capacity bytes
    cases decoded : bytesZahl bytes with
    | none => simp only [decoded, Bool.false_eq_true] at valid
    | some words =>
      have fits : words.length ≤ capacity := of_decide_eq_true (by simpa only [decoded] using valid)
      refine ⟨?_, ⟨Expr.strLit words fits, by simp only [lowLit, decoded, dite_eq_left fits]⟩⟩
      let literal : Expr (declOf u) Γ Λ (.str words.length) := .strLit words (Nat.le_refl _)
      by_cases same : Ty.str words.length = .str capacity
      · refine ⟨same ▸ literal, ?_⟩
        simp only [lowWertAtE, lowWertE, lowText, decoded, fitW, dite_eq_left same, literal]
      · refine ⟨Expr.strWeit capacity literal, ?_⟩
        simp only [lowWertAtE, lowWertE, lowText, decoded, fitW, dite_eq_right same, literal,
          ite_eq_left fits]
  · cases valid

private theorem lowProductArgs_of_fields (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (fields : List (Ty × USide))
    (lower : ∀ field ∈ fields, ∃ value, lowWertAtE u Γ Λ fn er field.1 field.2 = .ok value) :
    ∃ args, lowProductArgs u Γ Λ fn er fields = .ok args := by
  induction fields with
  | nil => exact ⟨.nil, lowProductArgs_nil u Γ Λ fn er⟩
  | cons field rest ih =>
    obtain ⟨value, lowValue⟩ := lower field List.mem_cons_self
    obtain ⟨args, lowArgs⟩ := ih (fun tailField present => lower tailField (List.mem_cons_of_mem _ present))
    cases field
    exact ⟨.cons value args, by
      simp only [lowProductArgs, lowValue, lowArgs, bind, Except.bind, pure, Except.pure]⟩

private theorem lowLitFields_of_fields (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fields : List (Ty × USide))
    (lower : ∀ field ∈ fields, ∃ value : Expr (declOf u) Γ Λ field.1, lowLit field.1 field.2 = .ok value) :
    ∃ args : Args (declOf u) Γ Λ (fields.map Prod.fst),
      lowLitFields (fields.map Prod.fst) fields = .ok args := by
  induction fields with
  | nil => exact ⟨.nil, by change lowLitFields [] [] = .ok .nil; rw [lowLitFields]⟩
  | cons field rest ih =>
    obtain ⟨value, lowValue⟩ := lower field List.mem_cons_self
    obtain ⟨args, lowArgs⟩ := ih (fun entry present => lower entry (List.mem_cons_of_mem _ present))
    rcases field with ⟨ty, raw⟩
    exact ⟨.cons value args, by
      change lowLitFields (ty :: rest.map Prod.fst) ((ty, raw) :: rest) = .ok (.cons value args)
      simp only [lowLitFields, bne_self_eq_false, Bool.false_eq_true, ite_false,
        lowValue, lowArgs, bind, Except.bind, pure, Except.pure]⟩

theorem specLiteralField_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (ty : Ty) (side : USide) (gate : u.exportGate = .ok ())
    (valid : specLiteralFieldFits u.records side ty = true) :
    (∃ expression, lowWertAtE u Γ Λ fn er ty side = .ok expression) ∧
      (∃ expression : Expr (declOf u) Γ Λ ty, lowLit ty side = .ok expression) := by
  suffices lowers : ∀ (measure : Nat) (source : USide), sizeOf source = measure →
      ∀ (target : Ty), specLiteralFieldFits u.records source target = true →
        (∃ expression, lowWertAtE u Γ Λ fn er target source = .ok expression) ∧
          (∃ expression : Expr (declOf u) Γ Λ target, lowLit target source = .ok expression) from
    lowers _ side rfl ty valid
  intro amount
  induction amount using Nat.strongRecOn with
  | ind amount smaller =>
    intro source measure target accepted
    cases source
    case arrNil =>
      cases target <;> try (simp only [specLiteralFieldFits, Bool.false_eq_true] at accepted)
      case arr element length =>
        cases length with
        | zero => exact ⟨⟨.arrNil, by rw [lowWertAtE]⟩, ⟨.arrNil, by rw [lowLit]⟩⟩
        | succ _ => simp only [specLiteralFieldFits, Bool.false_eq_true] at accepted
    case arrCons first rest =>
      cases target <;> try (simp only [specLiteralFieldFits, Bool.false_eq_true] at accepted)
      case arr element length =>
        cases length with
        | zero => simp only [specLiteralFieldFits, Bool.false_eq_true] at accepted
        | succ length =>
          have both : (specLiteralFieldFits u.records first element &&
              specLiteralFieldFits u.records rest (.arr element length)) = true := by
            simpa only [specLiteralFieldFits] using accepted
          obtain ⟨headOk, tailOk⟩ := Bool.and_eq_true_iff.mp both
          have extent : 1 + sizeOf first + sizeOf rest = amount := measure
          obtain ⟨⟨head, loweredHead⟩, ⟨literalHead, loweredLiteralHead⟩⟩ :=
            smaller (sizeOf first) (by omega) first rfl element headOk
          obtain ⟨⟨tail, loweredTail⟩, ⟨literalTail, loweredLiteralTail⟩⟩ :=
            smaller (sizeOf rest) (by omega) rest rfl (.arr element length) tailOk
          exact ⟨⟨.arrCons head tail, by simp only [lowWertAtE, loweredHead, loweredTail]⟩,
            ⟨.arrCons literalHead literalTail, by simp only [lowLit, loweredLiteralHead, loweredLiteralTail]⟩⟩
    case product identity reordered fields =>
      simp only [specLiteralFieldFits, Bool.and_eq_true_iff, decide_eq_true_eq] at accepted
      obtain ⟨⟨rfl, declared⟩, good⟩ := accepted
      cases named : uRecordOf u.records (.prod identity (fields.map Prod.fst)) with
      | error e => simp only [named, Except.isOk, Except.toBool, Bool.false_eq_true] at declared
      | ok schema =>
        have extent : sizeOf fields < amount := by
          rw [← measure]
          simp +arith
        have lowerField (field : Ty × USide) (present : field ∈ fields) :=
          have checked := List.all_eq_true.mp good ⟨field, present⟩ (List.mem_attach _ _)
          have less := recordField_sizeOf_lt fields field present
          smaller (sizeOf field.2) (by omega) field.2 rfl field.1 checked
        obtain ⟨args, lowered⟩ :=
          lowProductArgs_of_fields u Γ Λ fn er fields (fun field present => (lowerField field present).1)
        obtain ⟨literals, literalLowered⟩ :=
          lowLitFields_of_fields u Γ Λ fields (fun field present => (lowerField field present).2)
        have built := record_lower u Γ Λ fn er identity reordered fields args gate lowered schema named
        exact ⟨⟨.prod identity args, by simp only [lowWertAtE, built, fitW, dite_true]⟩,
          ⟨.prod identity literals, by
            simp only [lowLit, bne_self_eq_false, Bool.false_eq_true, ite_false, named,
              literalLowered, bind, Except.bind, pure, Except.pure]⟩⟩
    all_goals
      apply specPrimitiveLiteralField_lower u Γ Λ fn er
      simpa only [specLiteralFieldFits] using accepted

/-- The ordinary typed constructor traversal checks arrays and records
    with the same lexical environment at every depth. -/
theorem specCompositeArgument_lower {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    (fn : UFn) (er : Option Ty) (ctx : UCtx) (type : Ty) (raw : USide) (gate : u.exportGate = .ok ())
    (scope : ctx.records = u.records)
    (lexical : ∀ name type, specCompositeArgumentFits ctx (.param name) type = true →
      ∃ slot : Var Γ type, lowWertAtE u Γ Λ fn er type (.param name) = .ok (.var slot))
    (valid : specCompositeArgumentFits ctx raw type = true) :
    ∃ term : Expr (declOf u) Γ Λ type, lowWertAtE u Γ Λ fn er type raw = .ok term := by
  suffices lowers : ∀ (fuel : Nat) (source : USide), sizeOf source = fuel →
      ∀ (target : Ty), specCompositeArgumentFits ctx source target = true →
        ∃ term : Expr (declOf u) Γ Λ target, lowWertAtE u Γ Λ fn er target source = .ok term from
    lowers _ raw rfl type valid
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel smaller =>
    intro source size target accepted
    cases source
    case param name =>
      obtain ⟨slot, read⟩ := lexical name target accepted
      exact ⟨.var slot, read⟩
    case arrCons head tail =>
      cases target <;> try (simp only [specCompositeArgumentFits, specLiteralFieldFits, Bool.false_eq_true] at accepted)
      case arr element count =>
        cases count with
        | zero => simp only [specCompositeArgumentFits, specLiteralFieldFits, Bool.false_eq_true] at accepted
        | succ count =>
          have fields : (specCompositeArgumentFits ctx head element &&
              specCompositeArgumentFits ctx tail (.arr element count)) = true := by
            simpa only [specCompositeArgumentFits] using accepted
          obtain ⟨firstOk, restOk⟩ := Bool.and_eq_true_iff.mp fields
          have extent : 1 + sizeOf head + sizeOf tail = fuel := size
          obtain ⟨first, readFirst⟩ := smaller (sizeOf head) (by omega) head rfl element firstOk
          obtain ⟨rest, readRest⟩ := smaller (sizeOf tail) (by omega) tail rfl (.arr element count) restOk
          exact ⟨.arrCons first rest, by simp only [lowWertAtE, readFirst, readRest]⟩
    case product identity reordered fields =>
      simp only [specCompositeArgumentFits, Bool.and_eq_true_iff, decide_eq_true_eq] at accepted
      obtain ⟨⟨rfl, declared⟩, checked⟩ := accepted
      rw [scope] at declared
      cases named : uRecordOf u.records (.prod identity (fields.map Prod.fst)) with
      | error e => simp only [named, Except.isOk, Except.toBool, Bool.false_eq_true] at declared
      | ok schema =>
        have extent : sizeOf fields < fuel := by rw [← size]; simp +arith
        obtain ⟨args, lowered⟩ := lowProductArgs_of_fields u Γ Λ fn er fields
          (fun field present => by
            have valid := List.all_eq_true.mp checked ⟨field, present⟩ (List.mem_attach _ _)
            have smallerField := recordField_sizeOf_lt fields field present
            exact smaller (sizeOf field.2) (by omega) field.2 rfl field.1 valid)
        have built := record_lower u Γ Λ fn er identity reordered fields args gate lowered schema named
        exact ⟨.prod identity args, by simp only [lowWertAtE, built, fitW, dite_true]⟩
    all_goals
      apply (specLiteralField_lower u Γ Λ fn er _ _ gate ?_).1
      simpa only [specCompositeArgumentFits, scope] using accepted

/-- Bind the successful source argument to the ordinary G nominal
    constructor. Every field passed checking mode at the declared type. -/
theorem specRecordArgument_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (ctx : UCtx) (name : String) (source : List SExpr)
    (identity : Nat) (reordered : Bool) (fields : List (Ty × USide)) (result : Ty)
    (read : uWertBody ctx (.call name source) = .ok (.product identity reordered fields))
    (accepted : uSpecValueArgument ctx result (.call name source) = .ok ())
    (gate : u.exportGate = .ok ())
    (scope : u.records = ctx.records)
    (lexical : ∀ name type, specCompositeArgumentFits ctx (.param name) type = true →
      ∃ slot : Var Γ type, lowWertAtE u Γ Λ fn er type (.param name) = .ok (.var slot)) :
    ∃ (args : Args (declOf u) Γ Λ (fields.map Prod.fst)),
      result = .prod identity (fields.map Prod.fst) ∧
      lowWertE u Γ Λ fn er (.product identity reordered fields) =
        .ok ⟨.prod identity (fields.map Prod.fst), Expr.prod identity args⟩ := by
  obtain ⟨parsed, sourceRead, typeRead⟩ := uSpecValueArgument_exact accepted
  have exactSide := Except.ok.inj (read.symm.trans sourceRead)
  subst parsed
  change uSpecRecordType ctx name identity fields = some result at typeRead
  unfold uSpecRecordType at typeRead
  cases selected : uRecordConstructor ctx name with
  | none =>
    simp only [selected, Option.bind_eq_bind, Option.bind_none] at typeRead
    cases typeRead
  | some schema =>
    simp only [selected, Option.bind_eq_bind, Option.bind_some] at typeRead
    split at typeRead
    · rename_i checked
      have resultType : schema.ty = result := Option.some.inj typeRead
      have member : schema ∈ u.records := scope.symm ▸ uRecordConstructor_mem selected
      have schemaExists (type : Ty) (same : schema.ty = type) :
          ∃ hit, uRecordOf u.records type = .ok hit :=
        same ▸ uRecordOf_complete member
      obtain ⟨hit, exactSchema⟩ := schemaExists _ checked.1
      obtain ⟨args, lowered⟩ := lowProductArgs_of_fields u Γ Λ fn er fields (fun field present =>
        specCompositeArgument_lower fn er ctx _ _ gate scope.symm lexical
          (List.all_eq_true.mp checked.2 field present))
      exact ⟨args, resultType.symm.trans checked.1,
        record_lower u Γ Λ fn er identity reordered fields args gate lowered _ exactSchema⟩
    · cases typeRead

/-- A Boolean constructor field jointly satisfies the reader premises
    for arbitrary nominal identity, field name and Boolean value. -/
theorem specLiteralRecord_source_erfuellbar (base : UCtx) (name label : String)
    (identity : Nat) (value : Bool) :
    let schema : URecord := { name, identity, fields := [(label, .bool)] }
    let ctx := { base with records := schema :: base.records }
    let argument := SExpr.call name [.ext .label [label] [if value then .tru else .fls]]
    let fields := [(.bool, USide.truth value)]
    uWertBody ctx argument = .ok (.product identity false fields) ∧
      uSpecValueArgument ctx schema.ty argument = .ok () := by
  intro schema ctx argument fields
  have chosen : uRecordConstructor ctx name = some schema := by
    simp [uRecordConstructor, ctx, schema, strEq_apply_eq_decide]
  have read : uWertBody ctx argument = .ok (.product identity false fields) := by
    cases value <;>
      simp [argument, fields, uWertBody, uRechne, chosen, uRecordSides, uRecordSide, uRecordValues,
        schema, uSuch, strEq_apply_eq_decide, bind, Except.bind, pure, Except.pure] <;> rfl
  refine ⟨read, specRecordArgument_erfuellbar ctx name _ schema fields false chosen read rfl ?_⟩
  simp only [fields, List.all_cons, List.all_nil, specCompositeArgumentFits, specLiteralFieldFits,
    specPrimitiveLiteralFieldFits, Bool.and_self]

/-- A record passed to a predicate can take its field from the lexical
    scope. The constructor reader keeps that field as a typed name. -/
theorem specRecordLocal_erfuellbar (base : UCtx) (name label localName : String) (identity : Nat) :
    let schema : URecord := { name, identity, fields := [(label, .bool)] }
    let ctx := { base with records := schema :: base.records, names := [localName],
      kinds := [.bool], types := [.bool], unknownRanges := [] }
    let args := [SExpr.ext .label [label] [.variable localName]]
    let fields := [(.bool, USide.param localName)]
    uWertBody ctx (.call name args) = .ok (.product identity false fields) ∧
      uSpecValueArgument ctx schema.ty (.call name args) = .ok () := by
  intro schema ctx args fields
  have chosen : uRecordConstructor ctx name = some schema := by
    simp [uRecordConstructor, ctx, schema, strEq_apply_eq_decide]
  have read : uWertBody ctx (.call name args) = .ok (.product identity false fields) := by
    simp [args, fields, ctx, uWertBody, uRechne, chosen, uRecordSides, uRecordSide, uRecordValues,
      uParamNr, uParamNrAux, schema, uSuch, strEq_apply_eq_decide, bind, Except.bind, pure, Except.pure] <;> rfl
  refine ⟨read, specRecordArgument_erfuellbar ctx name args schema fields false chosen read rfl ?_⟩
  have same : strEq localName localName = true := by simp only [strEq, BEq.rfl]
  simp only [fields, List.all_cons, List.all_nil, specCompositeArgumentFits, ctx, List.contains_nil,
    Bool.not_false, uValueType, List.findIdx?_cons, same, ite_true, Option.bind_some, List.getElem?_cons_zero,
    decide_true, Bool.and_self]

/-- Arbitrary Boolean arrays satisfy all the recursive literal field
    checks at their exact declared length. -/
theorem specLiteralArrayField_erfuellbar (records : List URecord) (values : List Bool) :
    specLiteralFieldFits records (values.foldr (fun value rest => .arrCons (.truth value) rest) .arrNil)
      (.arr .bool values.length) = true := by
  induction values with
  | nil => simp only [List.foldr_nil, List.length_nil, specLiteralFieldFits]
  | cons value rest ih =>
    simp only [List.length_cons, List.foldr_cons, specLiteralFieldFits, specPrimitiveLiteralFieldFits, ih, Bool.and_self]

private theorem specBooleanArrayFits (ctx : UCtx) (values : List Bool) :
    specCompositeArgumentFits ctx (values.foldr (fun value rest => .arrCons (.truth value) rest) .arrNil)
      (.arr .bool values.length) = true := by
  induction values with
  | nil => simp only [List.foldr_nil, List.length_nil, specCompositeArgumentFits, specLiteralFieldFits]
  | cons value rest ih =>
    simp only [List.length_cons, List.foldr_cons, specCompositeArgumentFits, specLiteralFieldFits,
      specPrimitiveLiteralFieldFits, ih, Bool.and_self]

theorem specLiteralNestedRecord_erfuellbar (schema : URecord) (field : String) (value : Bool)
    (booleanField : schema.fields = [(field, Ty.bool)]) (records : List URecord)
    (declared : schema ∈ records) :
    specLiteralFieldFits records (.product schema.identity false [(.bool, .truth value)]) schema.ty = true := by
  have shape : schema.ty = .prod schema.identity [.bool] := by
    simp only [URecord.ty, booleanField, List.map_cons, List.map_nil, Ty.prodOf]
  obtain ⟨resolved, exactRecord⟩ := uRecordOf_complete declared
  simp only [specLiteralFieldFits, List.map_cons, List.map_nil, ← shape, decide_true, Bool.true_and,
    exactRecord, Except.isOk, Except.toBool]
  apply List.all_eq_true.mpr
  intro entry _
  have same : entry.val = (Ty.bool, USide.truth value) := List.mem_singleton.mp entry.property
  simp only [same, specLiteralFieldFits, specPrimitiveLiteralFieldFits]

private theorem uArraySides_booleans (ctx : UCtx) (values : List Bool)
    (sources : List SExpr) (same : sources = values.map (fun n => if n then SExpr.tru else SExpr.fls))
    (read : (source : SExpr) → sizeOf source < sizeOf sources → Except String USide) :
    uArraySides ctx sources read =
      .ok (values.foldr (fun value rest => .arrCons (.truth value) rest) .arrNil) := by
  induction values generalizing sources with
  | nil => subst sources; rfl
  | cons value rest ih =>
    simp only [List.map_cons] at same
    subst sources
    simp only [uArraySides, List.foldr_cons]
    cases value <;>
      simp only [uRecordSide, Bool.false_eq_true, ite_false, ite_true, ih _ rfl,
        bind, Except.bind, pure, Except.pure] <;> rfl

/-- The literal array accepted at a predicate parameter retains its
    declared type after substitution, including at array length zero. -/
theorem specArrayLiteral_erfuellbar (ctx : UCtx) (values : List Bool)
    (specIndex argumentIndex : Nat) (name : String) (parameters : List STyp) (annotation : STyp)
    (specFound : ctx.specTypen[specIndex]? = some (name, parameters))
    (argFound : parameters[argumentIndex]? = some annotation)
    (typed : uTypIn ctx.alias ctx.tabs ctx.namedTypes ctx.spaces ctx.eigner annotation =
      .ok (.arr .bool values.length)) :
    let array := SExpr.ext .array [] (values.map (fun value => if value then .tru else .fls))
    let literal := values.foldr (fun value rest => USide.arrCons (.truth value) rest) USide.arrNil
    uSpecArrayArgument ctx (.arr .bool values.length) array = .ok () ∧
      uWertBody ctx (.built "#spec-array" [.lit specIndex, .lit argumentIndex, array]) =
        .ok (.typed (.arr .bool values.length) literal) := by
  intro array literal
  have read : uRechne ctx (uWertBlatt ctx) array = .ok literal := by
    simp only [array, uRechne, uArraySides_booleans ctx values _ rfl, literal]
  refine ⟨?_, ?_⟩
  · simp only [uSpecArrayArgument, uWertBody, read, literal, specBooleanArrayFits,
      bind, Except.bind, ite_true, pure, Except.pure]
  · simp only [uWertBody, uRechne, specFound, argFound, typed, read,
      bind, Except.bind, pure, Except.pure]

/-- The canonical literal reader of the actual typed substitution
    accepts every checked literal with its exact declared type. -/
theorem specLiteralTyped_low {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    (fn : UFn) (er : Option Ty) (type : Ty) (literal : USide) (gate : u.exportGate = .ok ())
    (valid : specLiteralFieldFits u.records literal type = true) :
    ∃ value : Expr (declOf u) Γ Λ type, lowWertE u Γ Λ fn er (.typed type literal) = .ok ⟨type, value⟩ := by
  obtain ⟨value, read⟩ := (specLiteralField_lower u Γ Λ fn er type literal gate valid).2
  exact ⟨value, by simp only [lowWertE, read]⟩

/-- A typed predicate array uses the same canonical checking mode as
    an ordinary array argument. Closed literals also use their existing
    literal reader. Both paths have the declared array type. -/
theorem specTypedArray_low {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    (fn : UFn) (er : Option Ty) (element : Ty) (count : Nat) (raw : USide)
    (term : Expr (declOf u) Γ Λ (.arr element count))
    (checked : lowWertAtE u Γ Λ fn er (.arr element count) raw = .ok term) :
    ∃ value : Expr (declOf u) Γ Λ (.arr element count),
      lowWertE u Γ Λ fn er (.typed (.arr element count) raw) = .ok ⟨.arr element count, value⟩ := by
  cases literal : lowLit (u := u) (Γ := Γ) (Λ := Λ) (.arr element count) raw with
  | ok value => exact ⟨value, by simp only [lowWertE, literal]⟩
  | error diagnostic => exact ⟨term, by simp only [lowWertE, literal, checked, Except.map]⟩

/-- A source array literal can mix a run-time Boolean and a literal
    without losing either type. The actual canonical array retains the
    variable, rather than folding the argument at the caller. -/
theorem specArrayLocal_erfuellbar (ctx : UCtx) (name : String)
    (u : UProg) (fn : UFn) (Λ : List (Res (declOf u))) :
    let scope := { ctx with names := [name], types := [.bool], kinds := [.bool], unknownRanges := [] }
    let declaration := { fn with params := [(name, .bool)], kinds := [.bool] }
    let raw := USide.arrCons (.param name) (.arrCons (.truth false) .arrNil)
    uSpecArrayArgument scope (.arr .bool 2) (.ext .array [] [.variable name, .fls]) = .ok () ∧
    lowWertE u [.bool] Λ declaration none (.typed (.arr .bool 2) raw) =
      .ok ⟨.arr .bool 2, .arrCons (.var .here) (.arrCons .fls .arrNil)⟩ := by
  intro scope declaration raw
  have same : strEq name name = true := by simp only [strEq, BEq.rfl]
  have source : uWertBody scope (.ext .array [] [.variable name, .fls]) = .ok raw := by
    simp [scope, raw, uWertBody, uRechne, uArraySides, uRecordSide,
      uParamNr, uParamNrAux, same, bind, Except.bind, pure, Except.pure] <;> rfl
  constructor
  · simp only [uSpecArrayArgument, source, bind, Except.bind, specCompositeArgumentFits, raw,
      specLiteralFieldFits, specPrimitiveLiteralFieldFits, scope, List.contains_nil, Bool.not_false,
      uValueType, List.findIdx?_cons, same, ite_true, Option.bind_some, List.getElem?_cons_zero,
      decide_true, Bool.and_self, pure, Except.pure]
  · have parameter : lowWertAtE u [.bool] Λ declaration none .bool (.param name) = .ok (.var .here) := by
      simp only [lowWertAtE, lowWertE, declaration, lowParamWert, paramPos, BEq.rfl,
        ite_true, List.getElem?_cons_zero, Option.isSome_none, Bool.false_eq_true, ite_false,
        Nat.zero_add, lowVar, ↓reduceDIte, fitW] <;> rfl
    have truth : lowWertAtE u [.bool] Λ declaration none .bool (.truth false) = .ok .fls := by
      simp only [lowWertAtE, lowWertE, fitW, dite_true] <;> rfl
    simp only [lowWertE, raw, lowLit, lowWertAtE, parameter, truth, Except.map]

/-- Nominal literal construction retains every identity, schema and field-type check. -/
theorem lowLit_product (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (identity actual : Nat) (fields : List Ty) (reordered : Bool) (values : List (Ty × USide)) :
    lowLit (u := u) (Γ := Γ) (Λ := Λ) (.prod identity fields) (.product actual reordered values) = (do
      if identity != actual then throw "source export: constant has a foreign record identity"
      let _ ← uRecordOf u.records (.prod identity fields)
      let args ← lowLitFields fields values
      pure (.prod identity args)) := by
  rw [lowLit]

theorem lowLit_bool (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (value : Bool) :
    lowLit (u := u) (Γ := Γ) (Λ := Λ) .bool (.truth value) =
      .ok (if value then Expr.tru else Expr.fls) := by
  cases value <;> simp only [lowLit, Bool.false_eq_true, ↓reduceIte]

/-- The literal field helper also checks the carried field type before its recursive step. -/
theorem lowLitFields_cons (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (ty actual : Ty) (fields : List Ty) (value : USide) (values : List (Ty × USide)) :
    lowLitFields (u := u) (Γ := Γ) (Λ := Λ) (ty :: fields) ((actual, value) :: values) = (do
      if ty != actual then throw "source export: constant record field has a foreign type"
      let head ← lowLit ty value
      let tail ← lowLitFields fields values
      pure (.cons head tail)) := by
  rw [lowLitFields]

theorem lowLitFields_nil (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) :
    lowLitFields (u := u) (Γ := Γ) (Λ := Λ) [] [] = .ok .nil := by
  rw [lowLitFields]

/-- Nested literal arrays recurse through the same product-aware literal producer. -/
theorem lowLit_array_cons (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (ty : Ty) (count : Nat) (head tail : USide) :
    lowLit (u := u) (Γ := Γ) (Λ := Λ) (.arr ty (count + 1)) (.arrCons head tail) =
      (match lowLit ty head, lowLit (.arr ty count) tail with
       | .ok first, .ok rest => .ok (Expr.arrCons first rest)
       | .error error, _ | _, .error error => .error error) := by
  rw [lowLit]
  cases lowLit (u := u) (Γ := Γ) (Λ := Λ) ty head <;>
    cases lowLit (u := u) (Γ := Γ) (Λ := Λ) (.arr ty count) tail <;> rfl

/-- Product projection and replacement use the canonical semantics, with the whole base footprint. -/
theorem record_replace_meaning {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {identity : Nat}
    {fs : List Ty} {field : Ty} (entry state : World D) (env : Env D Γ)
    (value : Expr D Γ Λ (.prod identity fs)) (position : FieldAt fs field)
    (replacement : Expr D Γ Λ field) :
    eval entry (Expr.prodSet value position replacement) state env =
      prodSetW position (eval entry value state env) (eval entry replacement state env) ∧
    (Expr.prodSet value position replacement).orte = value.orte ++ replacement.orte := ⟨rfl, rfl⟩

end Gabbro.Grammatik.Parser.UebersetzeAllg
