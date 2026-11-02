module

public import Grammatik.Parser.Elab.Uebersetze.Tagged.Schema

import all Init.Data.Repr
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

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

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
    (uSumFaelle 100 nestedPayload).bind (USum.resolveCases (uErgBereich [])) =
      .ok [("Data", some (3, 10)), ("Empty", none)] := by decide

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

/-- The canonical type elaborator can resolve complete aggregate schemas. The current
    `Ty.sum` admission gate below still refuses to execute them as sum payloads. -/
theorem tagged_resolve_zeuge :
    taggedSourceSchema.resolve (uTyp [] []) = .ok taggedValueSchema := by decide

theorem USum.resolveCases_shape_zeuge :
    taggedValueSchema.cases.map (fun c => (c.1, c.2.isSome)) =
      taggedSourceSchema.cases.map (fun c => (c.1, c.2.isSome)) :=
  USum.resolveCases_shape (uTyp [] []) taggedSourceSchema.cases (by decide)

theorem USum.resolve_shape_zeuge :
    taggedValueSchema.name = taggedSourceSchema.name ∧
      taggedValueSchema.cases.map (fun c => (c.1, c.2.isSome)) =
        taggedSourceSchema.cases.map (fun c => (c.1, c.2.isSome)) :=
  USum.resolve_shape (uTyp [] []) taggedSourceSchema tagged_resolve_zeuge

theorem uSumFaelle_missing_close_refused :
    (match uSumFaelle 100 nestedPayload.dropLast.dropLast.dropLast with
      | .error _ => true | .ok _ => false) = true := by decide

theorem uSumFaelle_extra_payload_refused :
    (match uSumFaelle 100 [.ident "Data", .zeichen "(", .wort "u8", .zeichen ",",
      .wort "bool", .zeichen ")"] with | .error _ => true | .ok _ => false) = true := by decide

theorem uSumFaelle_empty_payload_refused :
    (match uSumFaelle 100 [.ident "Data", .zeichen "(", .zeichen ")"] with
      | .error _ => true | .ok _ => false) = true := by decide

theorem uSumFaelle_trailing_tokens_refused :
    (match uSumFaelle 100 [.ident "Data", .zeichen "(", .wort "u8", .zeichen ")",
      .ident "Discarded"] with | .error _ => true | .ok _ => false) = true := by decide

/-- A failed payload resolver refuses the declaration, including a failure after a valid field. -/
theorem tagged_unsupported_payload_refused :
    taggedSourceSchema.resolve (uErgBereich []) = .error "result without G form: [u8; ..]" := by
  decide

def taggedItems (body : String) : List SItemTief :=
  [.typeT ["tagged"] "Message" [] [] (some (.raw body))]

theorem uSumSchemas_bool_zeuge :
    uSumSchemas (taggedItems "{ Flag(bool), Empty }") =
      .ok [{ name := "Message", cases := [("Flag", some (.atom "bool")), ("Empty", none)] }] := rfl

theorem uSums_numeric_zeuge :
    uSums [] (taggedItems "{ Data(u8), Empty }") =
      .ok [{ name := "Message", cases := [("Data", some (0, 255)), ("Empty", none)] }] := by decide

theorem uSums_alias_zeuge :
    uSums [("Code", (3, 10))] (taggedItems "{ Data(Code), Empty }") =
      .ok [{ name := "Message", cases := [("Data", some (3, 10)), ("Empty", none)] }] := by decide

theorem uSumSchemas_duplicate_refused :
    uSumSchemas (taggedItems "{ Data(u8), Data }") = .error "duplicate tagged case name" := rfl

theorem uSumSchemas_empty_refused :
    uSumSchemas (taggedItems "{ }") = .error "tagged type without cases" := rfl

theorem uSums_bool_still_refused :
    (match uSums [] (taggedItems "{ Flag(bool), Empty }") with
      | .error _ => true | .ok _ => false) = true := by decide

theorem uSums_array_still_refused :
    (match uSums [] (taggedItems "{ Bytes([u8; 3]), Empty }") with
      | .error _ => true | .ok _ => false) = true := by decide

theorem uSums_reference_still_refused :
    (match uSums [] (taggedItems "{ Cell(index into Region), Empty }") with
      | .error _ => true | .ok _ => false) = true := by decide

theorem uSums_string_still_refused :
    (match uSums [] (taggedItems "{ Text(string max 8), Empty }") with
      | .error _ => true | .ok _ => false) = true := by decide

theorem uSums_record_still_refused :
    (match uSums [] (taggedItems "{ Record({ flag: bool }), Empty }") with
      | .error _ => true | .ok _ => false) = true := by decide

end Gabbro.Grammatik.Parser.Uebersetze
