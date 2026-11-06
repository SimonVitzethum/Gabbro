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
public import Grammatik.Parser.Elab.Uebersetze.Tagged.PayloadProbes
public import Grammatik.Parser.Elab.Uebersetze.Tagged.InitializerProbes
import all Grammatik.Parser.Elab.Uebersetze.Tagged.ProbeResults
import all Grammatik.GabbroV.Start.GvStartPflichta
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

attribute [local cbv_eval] Nat.log2_def

-- Select one actual parser step without expanding the mutually recursive fuel tuple.
attribute [local cbv_opaque] parseTyp parseTypNach parseOr parseOrL parseAnd parseAndL
  parseCmp parseBit parseBitL parseAdd parseAddL parseMul parseMulL parseUnary
  parsePrimary parseKopf parseSuffixe
attribute [local cbv_eval] parseTyp.eq_def parseTypNach.eq_def parseOr.eq_def parseOrL.eq_def
  parseAnd.eq_def parseAndL.eq_def parseCmp.eq_def parseBit.eq_def parseBitL.eq_def
  parseAdd.eq_def parseAddL.eq_def parseMul.eq_def parseMulL.eq_def parseUnary.eq_def
  parsePrimary.eq_def parseKopf.eq_def parseSuffixe.eq_def

open scoped Gabbro.Grammatik.Parser.Uebersetze

def nestedPayload : List Token :=
  [.ident "Data", .zeichen "(", .wort "u32", .wort "in", .zeichen "(",
    .num 1, .zeichen "+", .num 2, .zeichen ")", .zeichen "..", .num 10,
    .zeichen ")", .zeichen ",", .ident "Empty"]

/-- The inner closing parenthesis belongs to the bound; the next case is retained. -/
theorem uSumFaelle_nested_zeuge :
    uSumFaelle 100 nestedPayload =
      .ok [("Data", some (.range (.atom "u32") (.bin "+" (.lit 1) (.lit 2)) (.lit 10) false)),
        ("Empty", none)] := by cbv

theorem uSumFaelle_nested_resolved_zeuge :
    (uSumFaelle 100 nestedPayload).bind (USum.resolveCases (uSumPayload [])) =
      .ok [("Data", some (.int 3 10)), ("Empty", none)] := by cbv

theorem uSumFaelle_bool_zeuge :
    uSumFaelle 100 [.ident "Flag", .zeichen "(", .wort "bool", .zeichen ")"] =
      .ok [("Flag", some (.atom "bool"))] := by cbv

theorem uSumFaelle_array_zeuge :
    uSumFaelle 100 [.ident "Bytes", .zeichen "(", .zeichen "[", .wort "u8", .zeichen ";",
      .num 3, .zeichen "]", .zeichen ")", .zeichen ",", .ident "Empty"] =
      .ok [("Bytes", some (.array (.atom "u8") (.lit 3))), ("Empty", none)] := by cbv

theorem uSumFaelle_string_zeuge :
    uSumFaelle 100 [.ident "Text", .zeichen "(", .ident "string", .wort "max", .num 8,
      .zeichen ")"] = .ok [("Text", some (.str (.lit 8)))] := by cbv

theorem uSumFaelle_reference_zeuge :
    uSumFaelle 100 [.ident "Cell", .zeichen "(", .wort "index", .wort "into", .ident "Region",
      .zeichen ")"] = .ok [("Cell", some (.index false "Region"))] := by cbv

/-- Inline record syntax survives as the canonical parser's complete balanced group. -/
theorem uSumFaelle_record_zeuge :
    uSumFaelle 100 [.ident "Record", .zeichen "(", .zeichen "{", .ident "flag", .zeichen ":",
      .wort "bool", .zeichen "}", .zeichen ")", .zeichen ",", .ident "Empty"] =
      .ok [("Record", some (.raw "{ flag : bool } ")), ("Empty", none)] := by cbv

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
      .ok [{ name := "Message", cases := [("Flag", some (.atom "bool")), ("Empty", none)] }] := by cbv

theorem uSums_numeric_zeuge :
    uSums [] (taggedItems "{ Data(u8), Empty }") =
      .ok [{ name := "Message", cases := [("Data", some (.int 0 255)), ("Empty", none)] }] := by cbv

theorem uSums_alias_zeuge :
    uSums [("Code", (3, 10))] (taggedItems "{ Data(Code), Empty }") =
      .ok [{ name := "Message", cases := [("Data", some (.int 3 10)), ("Empty", none)] }] := by cbv

theorem uSumSchemas_duplicate_refused :
    uSumSchemas (taggedItems "{ Data(u8), Data }") = .error "duplicate tagged case name" := by cbv
theorem uSumSchemas_empty_refused :
    uSumSchemas (taggedItems "{ }") = .error "tagged type without cases" := by cbv
theorem uSumSchemas_duplicate_type_refused :
    uSumSchemas (taggedItems "{ Data(u8) }" ++ taggedItems "{ Empty }") =
      .error "duplicate tagged type name" := by cbv
theorem uSumSchemas_parameters_refused :
    uSumSchemas [.typeT ["tagged"] "Message" [.atom "u8"] []
      (some (.raw "{ Empty }"))] = .error "tagged declaration without G form" := by cbv
theorem uSumSchemas_constraints_refused :
    uSumSchemas [.typeT ["tagged"] "Message" [] ["discarded"]
      (some (.raw "{ Empty }"))] = .error "tagged declaration without G form" := by cbv
theorem uSumSchemas_linear_refused :
    uSumSchemas [.typeT ["linear", "tagged"] "Message" [] []
      (some (.raw "{ Empty }"))] = .error "tagged declaration without G form" := by cbv
theorem uSumSchemas_missing_body_refused :
    uSumSchemas [.typeT ["tagged"] "Message" [] [] none] =
      .error "tagged declaration without G form" := by cbv

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

end Gabbro.Grammatik.Parser.Uebersetze
