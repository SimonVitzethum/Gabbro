module

import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil13
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.GabbroV.Start.GvStartPflicht

import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.Uebersetze.Tagged.Initializers
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Init.Data.Repr

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

-- The actual width and mutually typed payload/initializer reader equations.
attribute [local cbv_eval] Nat.log2_def
attribute [local cbv_eval] Gabbro.Grammatik.Parser.UebersetzeAllg.lowWertE.eq_def
  Gabbro.Grammatik.Parser.UebersetzeAllg.lowWertAtE.eq_def
  Gabbro.Grammatik.Parser.UebersetzeAllg.lowEns.eq_def
  Gabbro.Grammatik.Parser.UebersetzeAllg.lowCmp.eq_def
attribute [local cbv_eval] uSumKonst.eq_def uKonst.eq_def

-- Proof cuts retain the complete canonical result before its Boolean projection.
private theorem reader_ok {α : Type} {reader : Except String α}
    (result : { actual : α // reader = .ok actual }) :
    (match reader with | .ok _ => true | .error _ => false) = true := by rw [result.property]
private theorem reader_error {α : Type} {reader : Except String α}
    (result : { error : String // reader = .error error }) :
    (match reader with | .ok _ => false | .error _ => true) = true := by rw [result.property]
private theorem chain_ok {α β : Type} {first : Except String α} {next : α → Except String β}
    (parsed : { actual : α // first = .ok actual })
    (lowered : { actual : β // next parsed.val = .ok actual }) :
    (match first with | .error _ => false | .ok value =>
      match next value with | .ok _ => true | .error _ => false) = true := by
  rw [parsed.property, lowered.property]
private theorem chain_first_error {α β : Type} {first : Except String α} {next : α → Except String β}
    (refused : { error : String // first = .error error }) :
    (match first with | .error _ => false | .ok value =>
      match next value with | .ok _ => true | .error _ => false) = false := by rw [refused.property]
private theorem chain_second_error {α β : Type} {first : Except String α} {next : α → Except String β}
    (parsed : { actual : α // first = .ok actual })
    (refused : { error : String // next parsed.val = .error error }) :
    (match first with | .error _ => false | .ok value =>
      match next value with | .ok _ => true | .error _ => false) = false := by
  rw [parsed.property, refused.property]
scoped macro "tagged_ok" : tactic => `(tactic| (
  apply reader_ok
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩))
scoped macro "tagged_error" : tactic => `(tactic| (
  apply reader_error
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩))

-- No successful UProg is assumed: both expansion data and the actual subsequent
-- rejection are inferred separately from the same canonical elaborator.
scoped macro "tagged_rejected " name:ident " from " items:term : command => do
  let expanded := Lean.mkIdentFrom name (name.getId.appendAfter "_expanded")
  let error := Lean.mkIdentFrom name (name.getId.appendAfter "_error")
  let a ← `(command| private def $expanded : { actual : List SItemTief × List (STyp × String) //
      expandU $items = .ok actual } := by refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let b ← `(command| private def $error : { message : String //
      elabUExpanded ($expanded).val = .error message } := by refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let c ← `(command| private theorem $name : elabU $items = .error ($error).val := by
    rw [elabU, ($expanded).property]
    exact ($error).property)
  return ⟨Lean.mkNullNode #[a, b, c]⟩

open scoped Gabbro.Grammatik.Parser.Uebersetze

def nestedPayload : List Token :=
  [.ident "Data", .zeichen "(", .wort "u32", .wort "in", .zeichen "(",
    .num 1, .zeichen "+", .num 2, .zeichen ")", .zeichen "..", .num 10,
    .zeichen ")", .zeichen ",", .ident "Empty"]

/-- The inner closing parenthesis belongs to the bound; the next case is retained. -/
theorem uSumFaelle_nested_zeuge :
    uSumFaelle 100 nestedPayload =
      .ok [("Data", some (.range (.atom "u32") (.bin "+" (.lit 1) (.lit 2)) (.lit 10) false)),
        ("Empty", none)] := rfl

theorem uSumFaelle_nested_resolved_zeuge :
    (uSumFaelle 100 nestedPayload).bind (USum.resolveCases (uSumPayload [])) =
      .ok [("Data", some (.int 3 10)), ("Empty", none)] := by cbv

theorem uSumFaelle_bool_zeuge :
    uSumFaelle 100 [.ident "Flag", .zeichen "(", .wort "bool", .zeichen ")"] =
      .ok [("Flag", some (.atom "bool"))] := rfl

theorem uSumFaelle_array_zeuge :
    uSumFaelle 100 [.ident "Bytes", .zeichen "(", .zeichen "[", .wort "u8", .zeichen ";",
      .num 3, .zeichen "]", .zeichen ")", .zeichen ",", .ident "Empty"] =
      .ok [("Bytes", some (.array (.atom "u8") (.lit 3))), ("Empty", none)] := rfl

theorem uSumFaelle_string_zeuge :
    uSumFaelle 100 [.ident "Text", .zeichen "(", .ident "string", .wort "max", .num 8,
      .zeichen ")"] = .ok [("Text", some (.str (.lit 8)))] := rfl

theorem uSumFaelle_reference_zeuge :
    uSumFaelle 100 [.ident "Cell", .zeichen "(", .wort "index", .wort "into", .ident "Region",
      .zeichen ")"] = .ok [("Cell", some (.index false "Region"))] := rfl

/-- Inline record syntax survives as the canonical parser's complete balanced group. -/
theorem uSumFaelle_record_zeuge :
    uSumFaelle 100 [.ident "Record", .zeichen "(", .zeichen "{", .ident "flag", .zeichen ":",
      .wort "bool", .zeichen "}", .zeichen ")", .zeichen ",", .ident "Empty"] =
      .ok [("Record", some (.raw "{ flag : bool } ")), ("Empty", none)] := rfl

def taggedSourceSchema : USum STyp :=
  { name := "Message", cases := [("Empty", none),
      ("Bytes", some (.array (.atom "u8") (.lit 3))), ("Text", some (.str (.lit 8)))] }

def taggedValueSchema : USum Ty :=
  { name := "Message", cases := [("Empty", none),
      ("Bytes", some (.arr (.int 0 255) 3)), ("Text", some (.str 8))] }

/-- The canonical type elaborator can resolve complete aggregate schemas. Typed sums retain the resolved aggregate payload types. -/
theorem tagged_resolve_zeuge :
    taggedSourceSchema.resolve (uTyp [] [] []) = .ok taggedValueSchema := by cbv

theorem USum.resolveCases_shape_zeuge :
    taggedValueSchema.cases.map (fun c => (c.1, c.2.isSome)) =
      taggedSourceSchema.cases.map (fun c => (c.1, c.2.isSome)) :=
  USum.resolveCases_shape (uTyp [] [] []) taggedSourceSchema.cases (by cbv)

theorem USum.resolve_shape_zeuge :
    taggedValueSchema.name = taggedSourceSchema.name ∧
      taggedValueSchema.cases.map (fun c => (c.1, c.2.isSome)) =
        taggedSourceSchema.cases.map (fun c => (c.1, c.2.isSome)) :=
  USum.resolve_shape (uTyp [] [] []) taggedSourceSchema tagged_resolve_zeuge

theorem uSumFaelle_missing_close_refused :
    (match uSumFaelle 100 nestedPayload.dropLast.dropLast.dropLast with
      | .error _ => true | .ok _ => false) = true := by cbv
theorem uSumFaelle_extra_payload_refused :
    (match uSumFaelle 100 [.ident "Data", .zeichen "(", .wort "u8", .zeichen ",",
      .wort "bool", .zeichen ")"] with | .error _ => true | .ok _ => false) = true := by cbv
theorem uSumFaelle_empty_payload_refused :
    (match uSumFaelle 100 [.ident "Data", .zeichen "(", .zeichen ")"] with
      | .error _ => true | .ok _ => false) = true := by cbv
theorem uSumFaelle_trailing_tokens_refused :
    (match uSumFaelle 100 [.ident "Data", .zeichen "(", .wort "u8", .zeichen ")",
      .ident "Discarded"] with | .error _ => true | .ok _ => false) = true := by cbv

/-- A failed payload resolver refuses the declaration, including a failure after a valid field. -/
theorem tagged_payload_resolved_zeuge :
    taggedSourceSchema.resolve (uSumPayload []) = .ok taggedValueSchema := by cbv

def taggedItems (body : String) : List SItemTief :=
  [.typeT ["tagged"] "Message" [] [] (some (.raw body))]

theorem uSumSchemas_bool_zeuge :
    uSumSchemas (taggedItems "{ Flag(bool), Empty }") =
      .ok [{ name := "Message", cases := [("Flag", some (.atom "bool")), ("Empty", none)] }] := rfl

theorem uSums_numeric_zeuge :
    uSums [] (taggedItems "{ Data(u8), Empty }") =
      .ok [{ name := "Message", cases := [("Data", some (.int 0 255)), ("Empty", none)] }] := by cbv

theorem uSums_alias_zeuge :
    uSums [("Code", (3, 10))] (taggedItems "{ Data(Code), Empty }") =
      .ok [{ name := "Message", cases := [("Data", some (.int 3 10)), ("Empty", none)] }] := by cbv

theorem uSumSchemas_duplicate_refused :
    uSumSchemas (taggedItems "{ Data(u8), Data }") = .error "duplicate tagged case name" := rfl
theorem uSumSchemas_empty_refused :
    uSumSchemas (taggedItems "{ }") = .error "tagged type without cases" := rfl
theorem uSumSchemas_duplicate_type_refused :
    uSumSchemas (taggedItems "{ Data(u8) }" ++ taggedItems "{ Empty }") =
      .error "duplicate tagged type name" := rfl
theorem uSumSchemas_parameters_refused :
    uSumSchemas [.typeT ["tagged"] "Message" [.atom "u8"] []
      (some (.raw "{ Empty }"))] = .error "tagged declaration without G form" := rfl
theorem uSumSchemas_constraints_refused :
    uSumSchemas [.typeT ["tagged"] "Message" [] ["discarded"]
      (some (.raw "{ Empty }"))] = .error "tagged declaration without G form" := rfl
theorem uSumSchemas_linear_refused :
    uSumSchemas [.typeT ["linear", "tagged"] "Message" [] []
      (some (.raw "{ Empty }"))] = .error "tagged declaration without G form" := rfl
theorem uSumSchemas_missing_body_refused :
    uSumSchemas [.typeT ["tagged"] "Message" [] [] none] =
      .error "tagged declaration without G form" := rfl

theorem uSums_ranged_bool_refused :
    (match uSums [] (taggedItems "{ Flag(bool in 0 .. 1) }") with
      | .error _ => true | .ok _ => false) = true := by cbv

theorem uSums_ranged_unknown_refused :
    (match uSums [] (taggedItems "{ Data(Undeclared in 0 .. 1) }") with
      | .error _ => true | .ok _ => false) = true := by cbv

theorem uSums_bool_admitted_zeuge :
    (match uSums [] (taggedItems "{ Flag(bool), Empty }") with
      | .error _ => false | .ok _ => true) = true := by cbv

theorem uSums_array_admitted_zeuge :
    (match uSums [] (taggedItems "{ Bytes([u8; 3]), Empty }") with
      | .error _ => false | .ok _ => true) = true := by cbv

theorem uSums_reference_still_refused :
    (match uSums [] (taggedItems "{ Cell(index into Region), Empty }") with
      | .error _ => true | .ok _ => false) = true := by cbv

theorem uSums_string_admitted_zeuge :
    (match uSums [] (taggedItems "{ Text(string max 8), Empty }") with
      | .error _ => false | .ok _ => true) = true := by cbv

theorem uSums_record_still_refused :
    (match uSums [] (taggedItems "{ Record({ flag: bool }), Empty }") with
      | .error _ => true | .ok _ => false) = true := by cbv

/-- Type-only fixtures exercise declaration collection, not function admission. -/
private def declarationSums : { actual : List USum //
    uSums [] (taggedItems "{ Bytes([u8; 3]), Empty }") = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
theorem tagged_declaration_payload_zeuge :
    uSums [] (taggedItems "{ Bytes([u8; 3]), Empty }") =
      .ok [{ name := "Message", cases := [("Bytes", some (.arr (.int 0 255) 3)), ("Empty", none)] }] :=
  declarationSums.property

tagged_rejected declaration_without_fn from (taggedItems "{ Bytes([u8; 3]), Empty }")
tagged_rejected declaration_duplicate from (taggedItems "{ Data(u8), Data }")
tagged_rejected declaration_shape from [.typeT ["tagged"] "Message" [] [] none]
/-- The full exporter still requires an actual function; schema support does not bypass this gate. -/
theorem elabU_tagged_payload_without_function_refused :
    elabU (taggedItems "{ Bytes([u8; 3]), Empty }") = .error "unit without a fn" :=
  declaration_without_fn

theorem elabU_tagged_duplicate_refused :
    elabU (taggedItems "{ Data(u8), Data }") = .error "duplicate tagged case name" :=
  declaration_duplicate

theorem elabU_tagged_shape_refused :
    elabU [.typeT ["tagged"] "Message" [] [] none] =
      .error "tagged declaration without G form" := declaration_shape

namespace TypedPayload

open Gabbro.Grammatik.Parser.UebersetzeAllg2

def sums : List USum :=
  [{ name := "Message", cases := [("Empty", none), ("Flag", some .bool),
      ("Count", some (.int 0 255)), ("Bytes", some (.arr (.int 0 255) 2)),
      ("Text", some (.str 8)), ("Nested", some (.sum [none, some .bool]))] }]

def unit : UProg := { tabs := [], locks := [], fns := [], sums := sums }
def scope : UFn :=
  { name := "fixture", params := [], kinds := [], res := none, held := [], puts := [],
    gives := [], body := [], ret := .empty }

/-- The actual tagged lowering path accepts complete record-free payloads. -/
theorem lower_bool_zeuge :
    (match lowSVal unit [] [] scope 0 0 (by decide) (.fall 1 (some (.truth true))) with
      | .ok _ => true | .error _ => false) = true := by tagged_ok

theorem lower_bool_variable_zeuge :
    (match lowSVal unit [.bool] [] { scope with params := [("flag", .bool)], kinds := [.bool] }
      0 0 (by decide) (.fall 1 (some (.param "flag"))) with
      | .ok _ => true | .error _ => false) = true := by tagged_ok

theorem lower_scalar_zeuge :
    (match lowSVal unit [] [] scope 0 0 (by decide) (.fall 2 (some (.lit 37))) with
      | .ok _ => true | .error _ => false) = true := by tagged_ok

theorem lower_array_zeuge :
    (match lowSVal unit [] [] scope 0 0 (by decide)
      (.fall 3 (some (.arrCons (.lit 7) (.arrCons (.lit 9) .arrNil)))) with
      | .ok _ => true | .error _ => false) = true := by tagged_ok

theorem lower_string_zeuge :
    (match lowSVal unit [] [] scope 0 0 (by decide) (.fall 4 (some (.text [65, 66]))) with
      | .ok _ => true | .error _ => false) = true := by tagged_ok

theorem lower_nested_sum_zeuge :
    (match lowSVal unit [] [] scope 0 0 (by decide)
      (.fall 5 (some (.taggedValue [none, some .bool] 1 (.truth false)))) with
      | .ok _ => true | .error _ => false) = true := by tagged_ok

theorem lower_missing_payload_refused :
    (match lowSVal unit [] [] scope 0 0 (by decide) (.fall 1 none) with
      | .ok _ => false | .error _ => true) = true := by tagged_error

theorem lower_extra_payload_refused :
    (match lowSVal unit [] [] scope 0 0 (by decide) (.fall 0 (some (.lit 1))) with
      | .ok _ => false | .error _ => true) = true := by tagged_error

theorem lower_wrong_payload_refused :
    (match lowSVal unit [] [] scope 0 0 (by decide) (.fall 1 (some (.lit 1))) with
      | .ok _ => false | .error _ => true) = true := by tagged_error

/-- Dependency resolution preserves source order even for a forward reference. -/
theorem nested_schema_export_zeuge :
    uSums [] [.typeT ["tagged"] "Outer" [] [] (some (.raw "{ Wrap(Inner) }")),
      .typeT ["tagged"] "Inner" [] [] (some (.raw "{ Flag(bool), Empty }"))] =
      .ok [{ name := "Outer", cases := [("Wrap", some (.sum [some .bool, none]))] },
        { name := "Inner", cases := [("Flag", some .bool), ("Empty", none)] }] := by cbv

theorem recursive_schema_refused :
    (match uSums [] [.typeT ["tagged"] "Recursive" [] []
        (some (.raw "{ Wrap(Recursive) }"))] with
      | .ok _ => false | .error _ => true) = true := by tagged_error

/-- Export and lower a source predicate as the selected complete bool payload. -/
def sourceBoolPayload (locks : List ULock) (source : SExpr) : Bool :=
  let tabs : List UTab := [{ name := "Flags", count := 2, cols := [("ready", (0, 1))], bools := ["ready"] }]
  let ctx : UCtx := { names := ["flag", "n"], kinds := [.bool, .int], types := [.bool, .int 0 255], tabs, locks, held := [], res := none, fname := "fixture", alias := [], lits := [], sums }
  let fn := { scope with params := [("flag", .bool), ("n", .int 0 255)], kinds := [.bool, .int] }
  match uSVal ctx 0 (.call "Flag" [source]) with
  | .error _ => false
  | .ok value =>
    match lowSVal { unit with tabs, locks } [.bool, .int 0 255] [] fn 0 0 (by decide) value with
    | .ok _ => true
    | .error _ => false

theorem source_comparison_payload_zeuge :
    sourceBoolPayload [] (.bin "<" (.variable "n") (.lit 7)) = true := by
  unfold sourceBoolPayload
  apply chain_ok <;> refine ⟨?_, by cbv <;> exact Eq.refl _⟩

theorem source_boolean_payload_zeuge :
    sourceBoolPayload [] (.bin "&&" (.un "!" (.variable "flag")) (.bin "<" (.variable "n") (.lit 7))) = true := by
  unfold sourceBoolPayload
  apply chain_ok <;> refine ⟨?_, by cbv <;> exact Eq.refl _⟩

def sourceFlagRead : SExpr := .field (.index (.field (.variable "Flags") "slots") (.lit 1)) "ready"

theorem source_bool_field_payload_zeuge : sourceBoolPayload [] sourceFlagRead = true := by
  unfold sourceBoolPayload
  apply chain_ok <;> refine ⟨?_, by cbv <;> exact Eq.refl _⟩

theorem source_guarded_payload_refused :
    sourceBoolPayload [{ name := "Guard", rank := 1, guard := ["Flags"] }] sourceFlagRead = false := by
  unfold sourceBoolPayload
  apply chain_second_error <;> refine ⟨?_, by cbv <;> exact Eq.refl _⟩

theorem source_numeric_bool_payload_refused : sourceBoolPayload [] (.lit 1) = false := by
  unfold sourceBoolPayload
  apply chain_first_error
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

theorem source_old_payload_refused :
    sourceBoolPayload [] (.old sourceFlagRead) = false := by
  unfold sourceBoolPayload
  apply chain_first_error
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

theorem source_result_payload_refused : sourceBoolPayload [] .res = false := by
  unfold sourceBoolPayload
  apply chain_first_error
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

/-- Scalar introductions are typed by the common value lowerer. -/
theorem lower_option_payload_zeuge :
    (match Gabbro.Grammatik.Parser.UebersetzeAllg.lowWertAtE unit [] [] scope none (.sum [some (.opt 4)])
      (.taggedValue [some (.opt 4)] 0 (.present 4 (.lit 2))) with
      | .ok _ => true | .error _ => false) = true := by tagged_ok

theorem lower_option_payload_range_refused :
    (match Gabbro.Grammatik.Parser.UebersetzeAllg.lowWertAtE unit [] [] scope none (.sum [some (.opt 4)])
      (.taggedValue [some (.opt 4)] 0 (.present 4 (.lit 4))) with
      | .ok _ => false | .error _ => true) = true := by tagged_error

end TypedPayload

namespace TypedInitializers

open Gabbro.Grammatik.GabbroV

def inner : USum := { name := "Inner", cases := [("InnerEmpty", none), ("InnerFlag", some .bool)] }
def outer : USum := { name := "Outer", cases := [("Empty", none), ("Flag", some .bool), ("Text", some (.str 8)), ("Nested", some (.sum inner.spec))] }
def schemas : List USum := [outer, inner]

theorem static_bool_payload_zeuge :
    uSumKonst [] schemas outer (.one (.call "Flag" [.tru])) = .ok (.fall 1 (.wahr true)) := by cbv

theorem static_string_payload_zeuge :
    uSumKonst [] schemas outer (.one (.call "Text" [.ext .text ["AB"] []])) =
      .ok (.fall 2 (.text [65, 66])) := by cbv

theorem static_nested_payload_zeuge :
    uSumKonst [] schemas outer (.one (.call "Nested" [.call "InnerFlag" [.fls]])) =
      .ok (.fall 3 (.fall 1 (.wahr false))) := by cbv

theorem static_missing_payload_refused :
    uSumKonst [] schemas outer (.one (.variable "Flag")) =
      .error "missing tagged payload in static initializer" := by cbv

theorem static_extra_payload_refused :
    uSumKonst [] schemas outer (.one (.call "Empty" [.tru])) =
      .error "missing or extra tagged payload in static initializer" := by cbv

/-- The existing initial-world decoder retains the whole recursively typed value. -/
theorem static_nested_value_zeuge :
    ((uSumKonst [] schemas outer (.one (.call "Nested" [.call "InnerFlag" [.fls]]))).toOption.bind
      (konstWert (F := Unit) (P := fun _ _ => true) (.sum outer.spec))) =
      some ⟨⟨3, by decide⟩, ⟨⟨1, by decide⟩, false⟩⟩ := by
  rw [static_nested_payload_zeuge]
  rfl

private def wrongInitializer : { actual : UKonst //
    uSumKonst [] schemas outer (.one (.call "Flag" [.lit 1])) = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def longInitializer : { actual : UKonst //
    uSumKonst [] schemas outer (.one (.call "Text" [.ext .text ["123456789"] []])) = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

theorem static_wrong_payload_refused :
    ((uSumKonst [] schemas outer (.one (.call "Flag" [.lit 1]))).toOption.bind
      (konstWert (F := Unit) (P := fun _ _ => true) (.sum outer.spec))) = none := by
  rw [wrongInitializer.property]
  cbv

theorem static_long_string_refused :
    ((uSumKonst [] schemas outer (.one (.call "Text" [.ext .text ["123456789"] []]))).toOption.bind
      (konstWert (F := Unit) (P := fun _ _ => true) (.sum outer.spec))) = none := by
  rw [longInitializer.property]
  cbv

-- Retain the original two declarations, with no invented function or default unit.
private def staticItems : List SItemTief :=
  [.typeT ["tagged"] "FlagType" [] [] (some (.raw "{ Flag(bool), Empty }")),
    .globT false "MSG" (.atom "FlagType") (.one (.call "Flag" [.tru])) none none false]
private def staticSchemas : { actual : List USum // uSums [] staticItems = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def staticRaw : { actual : List UGlob // uGlobs [] [] staticItems = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def staticTyped : { actual : List UGlob //
    uSumGlobs [] staticSchemas.val staticItems staticRaw.val = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
/-- Positive coverage is the actual static collector, before whole-unit function admission. -/
theorem static_collection_zeuge :
    ((uSums [] [.typeT ["tagged"] "FlagType" [] [] (some (.raw "{ Flag(bool), Empty }")),
      .globT false "MSG" (.atom "FlagType") (.one (.call "Flag" [.tru])) none none false]).bind fun sums =>
      ((uGlobs [] [] [.typeT ["tagged"] "FlagType" [] [] (some (.raw "{ Flag(bool), Empty }")),
        .globT false "MSG" (.atom "FlagType") (.one (.call "Flag" [.tru])) none none false]).bind
        (uSumGlobs [] sums [.typeT ["tagged"] "FlagType" [] [] (some (.raw "{ Flag(bool), Empty }")),
          .globT false "MSG" (.atom "FlagType") (.one (.call "Flag" [.tru])) none none false])).map
        (fun globs => globs.map (·.initK))) = .ok [.fall 0 (.wahr true)] := by
  change ((uSums [] staticItems).bind fun sums =>
    ((uGlobs [] [] staticItems).bind (uSumGlobs [] sums staticItems)).map
      (fun globs => globs.map (·.initK))) = _
  rw [staticSchemas.property, staticRaw.property]
  dsimp only [bind, Except.bind]
  rw [staticTyped.property]
  rfl

tagged_rejected static_without_fn from staticItems
/-- The unchanged global-only fixture is not an executable unit. -/
theorem static_export_without_function_refused :
    elabU [.typeT ["tagged"] "FlagType" [] [] (some (.raw "{ Flag(bool), Empty }")),
      .globT false "MSG" (.atom "FlagType") (.one (.call "Flag" [.tru])) none none false] =
      .error "unit without a fn" := static_without_fn

end TypedInitializers

end Gabbro.Grammatik.Parser.Uebersetze
