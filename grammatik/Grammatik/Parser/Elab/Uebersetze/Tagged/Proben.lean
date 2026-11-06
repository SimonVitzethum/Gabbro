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

-- Keep the schema result abstract while selecting the actual empty function
-- list. In particular, do not normalize any function elaborator callback or
-- the successful UProg constructor, neither of which this source can reach.
private theorem tagged_scoped_declaration (body : Option STyp)
    (requirements : List (STyp × String)) :
    elabExpandedWithScopes [.typeT ["tagged"] "Message" [] [] body]
      [] [] [] (uTabelle [] []) requirements =
      (uSums [] [.typeT ["tagged"] "Message" [] [] body] [] ["normal"] []).bind
        (fun _ => .error "unit without a fn") := by
  let items : List SItemTief := [.typeT ["tagged"] "Message" [] [] body]
  have guests : guestSources items = .ok ([], items) := by rfl
  have remaining : uRestFehler items = .ok () := by rfl
  have constants : Konst.checkSourceConstants items = .ok () := by rfl
  have sinks : uOhneSenken items = items := by rfl
  have globs : uGlobs [] [] items = .ok [] := by rfl
  have spaces : uSpaces items = ["normal"] := by rfl
  have owners : uOhneDoppelte (uEignerMs items) = [] := by rfl
  have orders : uMarkOrders items = .ok [] := by rfl
  have arenas : uArenen [] [] items = .ok ([], []) := by rfl
  have carriers : uArrayCarriers [] items = [] := by rfl
  have types : uTypes [] [] [] items [] ["normal"] =
      .ok ({ types := [], records := [] } : UTypeScope) := by rfl
  have checks : uChecks [] [] items = .ok [] := by rfl
  have locks : uSperrInvs [] [] [] [] items [] = .ok [] := by rfl
  have storage : uAkkuErweiterung [] [] 1 items = .ok ([], []) := by rfl
  have replacement : Konst.konstErsetzePipeline items = .ok items := by rfl
  have functions : uAkkuVorlauf [] [] items [] = .ok ([], [], []) := by rfl
  have reasons : uWhys items [] = .ok [] := by rfl
  have sumGlobs (schemas : List USum) :
      uSumGlobs [] schemas items [] = .ok [] := by rfl
  have sumTabs (schemas : List USum) : uSumTabs schemas [] = .ok [] := by rfl
  have registers : uRegs [] [] [] [] items = .ok [] := by rfl
  have invariants : uInvs [] [] [] [] [] items = .ok [] := by rfl
  have transitions : uGenerateTransitions [] [] [] = .ok [] := by rfl
  have tableOwners : items.filterMap
      (fun | .tableT _ _ _ _ owner _ _ _ => owner | _ => none) = [] := by rfl
  have tables : items.filter
      (fun | .tableT _ _ _ _ _ _ _ _ => true | _ => false) = [] := by rfl
  have lockItems : items.filter
      (fun | .lockT _ _ _ _ _ _ _ => true | _ => false) = [] := by rfl
  have runtimeItems : items.filterMap (fun
      | .fnT signature code => if strEq signature.art "const" then none else some (signature, code)
      | _ => none) = [] := by rfl
  have stateItems (ctx : UCtx) : items.filterMap
      (fun | .stateT name transitions => some (uZustand name transitions ctx) | _ => none) =
        [] := by rfl
  have noDuplicates : ((uEindeutig ([] : List String)).length != 0) = false := by rfl
  have pointers : uOhneDoppelte [] = [] := by rfl
  change elabExpandedWithScopes items [] [] [] (uTabelle [] []) requirements = _
  -- Apply whole producer equations before reducing their owner/item arguments.
  simp only [elabExpandedWithScopes, guests, remaining, constants, sinks, globs,
    spaces, owners, orders]
  simp only [items, List.filterMap_cons, List.filterMap_nil, List.filter_cons,
    List.filter_nil, Bool.false_eq_true, ite_false]
  simp only [tableOwners, tables, List.map_nil, uSeq, arenas, carriers,
    List.append_nil, List.nil_append, uIdxTabs, uOptGlobs, types]
  -- The floor is Int-valued; normalize only the selected empty-lock fold.
  try simp only [checks, lockItems, List.map_nil, uSeq, locks, List.foldl_nil,
    Int.zero_add, storage, List.append_nil, List.nil_append, List.all_nil,
    Bool.not_true, Bool.false_eq_true, ite_false]
  try simp only [replacement, runtimeItems, functions, reasons]
  simp only [sumGlobs, sumTabs, registers, invariants, stateItems, List.map_nil,
    uSeq, List.length_nil, noDuplicates, Bool.false_eq_true, ite_false, transitions,
    List.any_nil, List.flatMap_nil, pointers, List.range_zero, List.zip_nil_right,
    bind, Except.bind] <;> rfl

/-- Canonical collection remains before the no-function gate. Only the
    surrounding, type-only phases reduce; the payload parser stays symbolic. -/
private theorem tagged_expanded_declaration (body : Option String)
    (requirements : List (STyp × String)) :
    elabUExpanded ([.typeT ["tagged"] "Message" [] [] (body.map STyp.raw)], requirements) =
      (uSums [] [.typeT ["tagged"] "Message" [] [] (body.map STyp.raw)]
        [] ["normal"] []).bind (fun _ => .error "unit without a fn") := by
  have canonical : checkCanonicalConstants
      [.typeT ["tagged"] "Message" [] [] (body.map STyp.raw)] = .ok () := by rfl
  have sourceFunctions : uKonstFns
      [.typeT ["tagged"] "Message" [] [] (body.map STyp.raw)] = [] := by rfl
  have values : uConstsRech []
      [.typeT ["tagged"] "Message" [] [] (body.map STyp.raw)] [] = [] := by rfl
  have runtimeFunctions : uKonstFns (uOhneSenken
      [.typeT ["tagged"] "Message" [] [] (body.map STyp.raw)]) = [] := by rfl
  have collectors :
      uAliase [] [.typeT ["tagged"] "Message" [] [] (body.map STyp.raw)] ++
        uAliasBreiten [.typeT ["tagged"] "Message" [] [] (body.map STyp.raw)] = [] := by
    cases body <;> rfl
  unfold elabUExpanded
  simp only [canonical, bind, Except.bind]
  simp only [sourceFunctions, values, runtimeFunctions]
  simpa only [List.map_nil, List.append_nil, collectors, bind, Except.bind] using
    tagged_scoped_declaration (body.map STyp.raw) requirements

-- Expansion and each subsequent phase are certified separately. The complete
-- actual pair is transported before any projection feeds the elaborator.
private def declaration_without_fn_expanded :
    { actual : List SItemTief × List (STyp × String) //
      expandU (taggedItems "{ Bytes([u8; 3]), Empty }") = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private theorem declaration_without_fn_phase :
    elabUExpanded declaration_without_fn_expanded.val = .error "unit without a fn" := by
  have actual : declaration_without_fn_expanded.val =
      (taggedItems "{ Bytes([u8; 3]), Empty }", []) := by rfl
  have schema : uSums [] (taggedItems "{ Bytes([u8; 3]), Empty }") [] ["normal"] [] =
      .ok declarationSums.val := by cbv <;> exact Eq.refl _
  exact (congrArg elabUExpanded actual).trans
    ((tagged_expanded_declaration (some "{ Bytes([u8; 3]), Empty }") []).trans
      (congrArg (fun result : Except String (List USum) =>
        result.bind (fun _ => (.error "unit without a fn" : Except String UProg))) schema))

private theorem declaration_without_fn :
    elabU (taggedItems "{ Bytes([u8; 3]), Empty }") = .error "unit without a fn" :=
  (congrArg (fun result : Except String (List SItemTief × List (STyp × String)) =>
    result.bind elabUExpanded) declaration_without_fn_expanded.property).trans
      declaration_without_fn_phase

private def declaration_duplicate_expanded :
    { actual : List SItemTief × List (STyp × String) //
      expandU (taggedItems "{ Data(u8), Data }") = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private theorem declaration_duplicate_phase :
    elabUExpanded declaration_duplicate_expanded.val =
      .error "duplicate tagged case name" := by
  have actual : declaration_duplicate_expanded.val =
      (taggedItems "{ Data(u8), Data }", []) := by rfl
  have schema : uSums [] (taggedItems "{ Data(u8), Data }") [] ["normal"] [] =
      .error "duplicate tagged case name" := by
    simp only [uSums, uSumSchemas_duplicate_refused, bind, Except.bind]
  exact (congrArg elabUExpanded actual).trans
    ((tagged_expanded_declaration (some "{ Data(u8), Data }") []).trans
      (congrArg (fun result : Except String (List USum) =>
        result.bind (fun _ => (.error "unit without a fn" : Except String UProg))) schema))

private theorem declaration_duplicate :
    elabU (taggedItems "{ Data(u8), Data }") = .error "duplicate tagged case name" :=
  (congrArg (fun result : Except String (List SItemTief × List (STyp × String)) =>
    result.bind elabUExpanded) declaration_duplicate_expanded.property).trans
      declaration_duplicate_phase

private def declaration_shape_expanded :
    { actual : List SItemTief × List (STyp × String) //
      expandU [.typeT ["tagged"] "Message" [] [] none] = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private theorem declaration_shape_phase :
    elabUExpanded declaration_shape_expanded.val =
      .error "tagged declaration without G form" := by
  have actual : declaration_shape_expanded.val =
      ([.typeT ["tagged"] "Message" [] [] none], []) := by rfl
  have schema : uSums [] [.typeT ["tagged"] "Message" [] [] none] [] ["normal"] [] =
      .error "tagged declaration without G form" := by
    simp only [uSums, uSumSchemas_missing_body_refused, bind, Except.bind]
  exact (congrArg elabUExpanded actual).trans
    ((tagged_expanded_declaration none []).trans
      (congrArg (fun result : Except String (List USum) =>
        result.bind (fun _ => (.error "unit without a fn" : Except String UProg))) schema))

private theorem declaration_shape :
    elabU [.typeT ["tagged"] "Message" [] [] none] =
      .error "tagged declaration without G form" :=
  (congrArg (fun result : Except String (List SItemTief × List (STyp × String)) =>
    result.bind elabUExpanded) declaration_shape_expanded.property).trans declaration_shape_phase
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
