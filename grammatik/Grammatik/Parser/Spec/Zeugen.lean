module

public import Grammatik.Parser.Spec.Expand
public import Grammatik.Parser.Elab.Uebersetze.Teil13

@[expose] public section

namespace Gabbro.Grammatik.Parser.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The non-degenerate Shape/Circles instance of §5.1, with its actual arithmetic body. -/
def areaSpec : FnSig :=
  { art := "spec", name := "area", params := [("s", .atom "T")], res := some (.atom "u64"),
    fehler := none, klauseln := [.gives (.bin ">=" .res (.lit 1)), .effs [.param "E"], .cost (.lit 50)] }

def radius : SExpr := .field (.index (.variable "Circles") (.variable "s")) "r"

def areaBody : SAnw := .block [] (some (.ret (some
  (.bin "+" (.bin "*" (.bin "*" (.lit 3) radius) radius) (.lit 1)))))

def areaImpl : FnSig :=
  { areaSpec with art := "impl", params := [("s", .index false "Circles")],
    klauseln := [.gives (.bin ">=" .res (.lit 1)), .effs [.reads (.variable "Circles")], .cost (.lit 20)] }

def shapeSpec : SItemTief := .specGroupT "Shape" ["T"] ["E"] [areaSpec]

def shapeImpl (s : FnSig := areaImpl) : SItemTief :=
  .implGroupT "Shape" [.index false "Circles"] [[.reads (.variable "Circles")]] [.fnT s areaBody]

def callerBody (name : String := "Shape::area") : SAnw :=
  .block [.bind false "a" none (.call name [.variable "c"])] (some (.ret (some (.variable "a"))))

def caller : FnSig :=
  { art := "impl", name := "draw", params := [("c", .index false "Circles")],
    res := some (.atom "u64"), fehler := none, klauseln := [] }

def circles : SItemTief := .tableT "Circles" none (some (.lit 4)) none none false
  [.tSlot [⟨"r", .range (.atom "u64") (.lit 0) (.lit 9) false, none, none, none, false, false⟩]]

def shape : List SItemTief := [circles, shapeSpec, shapeImpl, .fnT caller (callerBody)]

theorem shape_conformance_zeuge : conforms shape = true := by rfl

theorem shape_inferred_call_zeuge :
    resolveCall shape caller.params "Shape::area" none [.variable "c"] = .ok "$spec$0$area" := by rfl

theorem shape_explicit_call_zeuge :
    resolveCall shape [] "Shape::area" (some [.index false "Circles"]) [.variable "c"] =
      .ok "$spec$0$area" := by rfl

/-- The actual elaborator sees the instantiated program, including the arithmetic implementation. -/
theorem shape_elaboration_zeuge : (Uebersetze.elabU shape).toOption.isSome = true := by rfl

theorem shape_expansion_zeuge : (expand shape).toOption.isSome = true := by rfl

def expandedDraw : Option SAnw := (expand shape).toOption.bind fun its => its.findSome? fun
  | .fnT s body => if strEq s.name "draw" then some body else none
  | _ => none

theorem shape_rewritten_call_zeuge :
    beqSAnw (expandedDraw.getD (.other "missing")) (callerBody "$spec$0$area") = true := by rfl

/-- Exact parser tokens avoid decoding a whole source string in the kernel. -/
def specTokens : List Token :=
  [.wort "spec", .ident "Shape", .zeichen "[", .ident "T", .zeichen ";", .wort "effects", .ident "E",
   .zeichen "]", .zeichen "{", .wort "fn", .ident "area", .zeichen "(", .ident "s", .zeichen ":",
   .ident "T", .zeichen ")", .zeichen "->", .wort "u64", .wort "ensures", .wort "result", .zeichen ">=",
   .num 1, .wort "effects", .zeichen "{", .ident "E", .zeichen "}", .wort "costs", .zeichen "<=", .num 50,
   .wort "ops", .zeichen ";", .zeichen "}"]

def implTokens : List Token :=
  [.wort "impl", .ident "Shape", .zeichen "[", .wort "index", .wort "into", .ident "Circles", .zeichen ";",
   .wort "effects", .zeichen "{", .wort "reads", .ident "Circles", .zeichen "}", .zeichen "]", .zeichen "{",
   .wort "fn", .ident "area", .zeichen "(", .ident "s", .zeichen ":", .wort "index", .wort "into",
   .ident "Circles", .zeichen ")", .zeichen "->", .wort "u64", .wort "ensures", .wort "result", .zeichen ">=",
   .num 1, .wort "effects", .zeichen "{", .wort "reads", .ident "Circles", .zeichen "}",
   .wort "costs", .zeichen "<=", .num 20, .wort "ops", .zeichen "{", .wort "return", .num 3, .zeichen "*",
   .ident "Circles", .zeichen "[", .ident "s", .zeichen "]", .zeichen ".", .ident "r", .zeichen "*",
   .ident "Circles", .zeichen "[", .ident "s", .zeichen "]", .zeichen ".", .ident "r", .zeichen "+", .num 1,
   .zeichen ";", .zeichen "}", .zeichen "}"]

theorem shape_parser_zeuge :
    beqTopTief (parseTopTief (specTokens ++ implTokens ++ [.ende])) (.ok [shapeSpec, shapeImpl]) = true := by
  rfl

def explicitCallTokens : List Token :=
  [.ident "Shape", .zeichen "::", .ident "area", .zeichen "::", .zeichen "[", .wort "index", .wort "into",
   .ident "Circles", .zeichen "]", .zeichen "(", .ident "c", .zeichen ")", .ende]

theorem explicit_call_parser_zeuge :
    beqTop (parseTop explicitCallTokens)
      (.ok (.ext .inst ["Shape::area", "index into Circles"] [.variable "c"])) = true := by rfl

theorem explicit_statement_parser_zeuge :
    beqSAnw ((parseKopfStmt 1000 (explicitCallTokens.dropLast ++ [.zeichen ";"])).toOption.map Prod.fst
      |>.getD (.other "missing")) (.call "Shape::area::[index into Circles]" [.variable "c"]) = true := by rfl

theorem missing_function_zeuge :
    check [shapeSpec, .implGroupT "Shape" [.index false "Circles"] [[.reads (.variable "Circles")]] []] =
      .error "spec.function.missing: area" := by rfl

theorem stronger_requires_zeuge :
    check [shapeSpec, shapeImpl { areaImpl with klauseln := .needs (.bin ">=" radius (.lit 1)) :: areaImpl.klauseln }] =
      .error "spec.requires" := by rfl

theorem weaker_ensures_zeuge :
    check [shapeSpec, shapeImpl { areaImpl with
      klauseln := [.effs [.reads (.variable "Circles")], .cost (.lit 20)] }] = .error "spec.ensures" := by rfl

theorem larger_effects_zeuge :
    check [shapeSpec, shapeImpl { areaImpl with klauseln :=
      [.gives (.bin ">=" .res (.lit 1)), .effs [.writes (.variable "Circles")], .cost (.lit 20)] }] =
      .error "spec.effects" := by rfl

theorem larger_cost_zeuge :
    check [shapeSpec, shapeImpl { areaImpl with klauseln :=
      [.gives (.bin ">=" .res (.lit 1)), .effs [.reads (.variable "Circles")], .cost (.lit 51)] }] =
      .error "spec.cost" := by rfl

theorem held_in_spec_zeuge :
    check [.specGroupT "Shape" ["T"] ["E"]
      [{ areaSpec with klauseln := .needs (.call "Held" [.variable "L"]) :: areaSpec.klauseln }], shapeImpl] =
      .error "spec.held" := by rfl

theorem extra_function_zeuge :
    check [shapeSpec, .implGroupT "Shape" [.index false "Circles"] [[.reads (.variable "Circles")]]
      [.fnT areaImpl areaBody, .fnT { areaImpl with name := "perimeter" } areaBody]] =
      .error "spec.function.extra" := by rfl

theorem duplicate_impl_zeuge :
    check [shapeSpec, shapeImpl, shapeImpl] = .error "spec.implementation.duplicate" := by rfl

theorem wrong_signature_zeuge :
    check [shapeSpec, shapeImpl { areaImpl with res := some (.atom "bool") }] = .error "spec.signature" := by rfl

theorem missing_effect_argument_zeuge :
    check [shapeSpec, .implGroupT "Shape" [.index false "Circles"] [] [.fnT areaImpl areaBody]] =
      .error "spec.arguments" := by rfl

theorem unknown_instance_zeuge :
    resolveCall [shapeSpec] caller.params "Shape::area" none [.variable "c"] =
      .error "spec.call.implementation.missing" := by rfl

theorem explicit_statement_resolution_zeuge :
    (Walk.mk shape true).call [] "Shape::area::[index into Circles]" none [.variable "c"] =
      .ok "$spec$0$area" := by rfl

theorem normalized_conjunctions_zeuge :
    predicateSubset (conjuncts (.bin "&&" .tru .fls)) (conjuncts (.bin "&&" .fls .tru)) = true := by rfl

theorem duplicate_impl_ignores_effect_arguments_zeuge :
    check [shapeSpec, shapeImpl,
      .implGroupT "Shape" [.index false "Circles"] [[]] [.fnT areaImpl areaBody]] =
      .error "spec.implementation.duplicate" := by rfl

theorem duplicate_function_zeuge :
    check [shapeSpec, .implGroupT "Shape" [.index false "Circles"] [[.reads (.variable "Circles")]]
      [.fnT areaImpl areaBody, .fnT areaImpl areaBody]] = .error "spec.function.duplicate" := by rfl

theorem undeclared_effect_parameter_zeuge :
    check [.specGroupT "Shape" ["T"] ["Other"] [areaSpec]] = .error "spec.effects.parameter" := by rfl

theorem missing_effect_bound_zeuge :
    check [.specGroupT "Shape" ["T"] ["E"]
      [{ areaSpec with klauseln := [.gives (.bin ">=" .res (.lit 1)), .cost (.lit 50)] }]] =
      .error "spec.effects.required" := by rfl

theorem missing_cost_bound_zeuge :
    check [.specGroupT "Shape" ["T"] ["E"]
      [{ areaSpec with klauseln := [.gives (.bin ">=" .res (.lit 1)), .effs [.param "E"]] }]] =
      .error "spec.cost.required" := by rfl

theorem instance_effects_zeuge :
    expandEffects shape (groups shape) (instances shape) [] [] 1000
      [.instanceEffects "Shape" [.index false "Circles"]] = .ok [.reads (.variable "Circles")] := by rfl

theorem bare_u32_normalization_zeuge :
    beqSTyp (canonicalType [] 128 (.range (.atom "u32") (.lit 0) (.lit 4294967295) false))
      (.atom "u32") = true := by rfl

end Gabbro.Grammatik.Parser.Spec
