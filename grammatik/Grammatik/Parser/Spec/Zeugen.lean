module

public import Grammatik.Parser.Spec.Expand
import all Grammatik.Parser.Spec.Walk
import all Grammatik.Parser.Spec.Items
import all Grammatik.Parser.Spec.Expand
-- Generic equations of the unchanged mutual reader, not accumulator fixtures.
import all Grammatik.Parser.Elab.Uebersetze.Akku.ProbenPhases
import all Grammatik.Parser.Elab.Uebersetze.Folds.Substitution
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
import all Grammatik.Parser.Elab.Uebersetze.Einheit.Elaboration
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil13

-- The elaboration witness executes the actual empty static/check gates.
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Legacy
import all Init.Data.String.Slice
import all Init.Data.String.Pattern.String
import all Init.Data.String.TakeDrop
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Grammatik.Parser.Spec
open Uebersetze
-- Literal spelling comparisons use proof-producing evaluation, without decoding strings.
attribute [local cbv_eval] strEq_apply_eq_decide
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The non-degenerate Shape/Circles instance of §5.1, with its actual arithmetic body. -/
def areaSpec : FnSig :=
  { art := "spec", name := "area", params := [("s", .atom "T")], res := some (.atom "u64"),
    fehler := none, klauseln := [.gives (.bin ">=" .res (.lit 1)), .effs [.param "E"], .cost (.lit 50)],
    generics := [] }

def radius : SExpr := .field (.index (.variable "Circles") (.variable "s")) "r"

def areaBody : SAnw := .block [] (some (.ret (some
  (.bin "+" (.bin "*" (.bin "*" (.lit 3) radius) radius) (.lit 1)))))

def areaImpl : FnSig :=
  { areaSpec with
    art := "impl"
    params := [("s", .index false "Circles")]
    klauseln := [.gives (.bin ">=" .res (.lit 1)), .effs [.reads (.variable "Circles")], .cost (.lit 20)] }

def shapeSpec : SItemTief := .specGroupT "Shape" ["T"] ["E"] [areaSpec]

def shapeImpl (s : FnSig := areaImpl) : SItemTief :=
  .implGroupT "Shape" [.index false "Circles"] [[.reads (.variable "Circles")]] [.fnT s areaBody]

def callerBody (name : String := "Shape::area") : SAnw :=
  .block [.bind false "a" none (.call name [.variable "c"])] (some (.ret (some (.variable "a"))))

def caller : FnSig :=
  { art := "impl", name := "draw", params := [("c", .index false "Circles")],
    res := some (.atom "u64"), fehler := none, klauseln := [], generics := [] }

def circles : SItemTief := .tableT "Circles" none (some (.lit 4)) none none false
  [.tSlot [⟨"r", .range (.atom "u64") (.lit 0) (.lit 9) false, none, none, none, false, false⟩]]

def shape : List SItemTief := [circles, shapeSpec, shapeImpl, .fnT caller (callerBody)]

theorem shape_conformance_zeuge : conforms shape = true := by cbv

theorem shape_inferred_call_zeuge :
    resolveCall shape caller.params "Shape::area" none [.variable "c"] = .ok "$spec$0$area" := by rfl

theorem shape_explicit_call_zeuge :
    resolveCall shape [] "Shape::area" (some [.index false "Circles"]) [.variable "c"] =
      .ok "$spec$0$area" := by rfl

-- Select the canonical substitution only after its actual expression is known.
-- The entire specification environment and the original fuel remain arguments.
private theorem spec_expression_select (specs : List (String × List String × SExpr))
    (fuel : Nat) (expr : SExpr) :
    uSpecEin specs fuel expr = match fuel with
      | 0 => expr
      | next + 1 => match expr with
        | .call name args =>
          let args' := args.map (uSpecEin specs next)
          match specs.find? (fun p => strEq p.1 name) with
          | some (_, params, body) =>
            if params.length == args'.length && !(args'.any (specArgumentCaptures body)) then
              uSpecEin specs next (sErsetze (params.zip args') 1000 body)
            else .call name args'
          | none => .call name args'
        | .field a name => .field (uSpecEin specs next a) name
        | .index a i => .index (uSpecEin specs next a) (uSpecEin specs next i)
        | .arrow a name => .arrow (uSpecEin specs next a) name
        | .un op a => .un op (uSpecEin specs next a)
        | .bin op a b => .bin op (uSpecEin specs next a) (uSpecEin specs next b)
        | .built name args => .built name (args.map (uSpecEin specs next))
        | .old a => .old (uSpecEin specs next a)
        | .ext kind names args => .ext kind names (args.map (uSpecEin specs next))
        | expr => expr := by
  cases fuel <;> rfl

private theorem substitution_select (bindings : List (String × SExpr))
    (fuel : Nat) (expr : SExpr) :
    sErsetze bindings fuel expr = match fuel with
      | 0 => expr
      | next + 1 => match expr with
        | .variable name => match bindings.find? (fun p => strEq p.1 name) with
          | some pair => pair.2
          | none => expr
        | .field a name => .field (sErsetze bindings next a) name
        | .index a i => .index (sErsetze bindings next a) (sErsetze bindings next i)
        | .arrow a name => .arrow (sErsetze bindings next a) name
        | .un op a => .un op (sErsetze bindings next a)
        | .bin op a b => .bin op (sErsetze bindings next a) (sErsetze bindings next b)
        | .call name args => .call name (args.map (sErsetze bindings next))
        | .built name args => .built name (args.map (sErsetze bindings next))
        | .old a => .old (sErsetze bindings next a)
        | .ext kind names args =>
          if isFold kind then
            match names, args with
            | binder :: _, subject :: filter :: value :: fallback =>
              let inner := bindings.filter (fun pair => !strEq pair.1 binder)
              .ext kind names (sErsetze bindings next subject :: sErsetze inner next filter ::
                sErsetze inner next value :: fallback.map (sErsetze bindings next))
            | _, _ => .ext kind names (args.map (sErsetze bindings next))
          else if kind == XKind.all || kind == XKind.any || kind == XKind.count then
            let inner := bindings.filter (fun p => !(names.head?.any (strEq p.1 ·)))
            .ext kind names ((args.dropLast.map (sErsetze bindings next)) ++
              (args.getLast?.map (sErsetze inner next)).toList)
          else .ext kind names (args.map (sErsetze bindings next))
        | expr => expr := by
  cases fuel <;> rfl

-- One actual block equation retains clauses, all resulting contexts, fold/call
-- prefixes and the original early-ending refusal rule. In particular ctx.specs
-- is neither erased nor assumed empty when its clauses are elaborated.
private theorem function_block (ctx : UCtx) (heads : List UFnKopf)
    (clauses : List SKlausel) (statements : List SAnw) (ending : Option SEnde) :
    elabFn ctx heads clauses (.block statements ending) =
      match elabKlauseln ctx clauses with
      | .error error => .error error
      | .ok (gives, needs) =>
        match uAnwReihe ctx.tabs heads 1000000 ctx statements with
        | .error error => .error error
        | .ok (body, afterBody) =>
          match expandFoldEnd afterBody ending with
          | .error error => .error error
          | .ok (beforeEnd, afterEnd, ending) =>
            match expandReturnCall afterEnd heads ending with
            | .error error => .error error
            | .ok (beforeCall, afterCall, returning) =>
              match uEnde afterCall returning with
              | .error error =>
                if returning.isNone &&
                    (match statements.getLast? with | some s => uEndetTief 64 s | none => false) then
                  .ok (gives, needs, body, .keins)
                else .error error
              | .ok result => .ok (gives, needs, body ++ beforeEnd ++ beforeCall, result) := by
  rfl

-- These equations apply only to fully selected operations. They keep unused
-- large-fuel callbacks symbolic without altering the compiler's fuel or gates.
attribute [local cbv_opaque] uSpecEin sErsetze elabFn uAnwReihe uAnwReiheCore
  uAkkuBinder uZeigerAnw uStartNamen uSondenFns uTorHuellen uFloatLimit
attribute [local cbv_eval] spec_expression_select substitution_select function_block
  row_nil row_cons core_bind bound_names_select pointer_source_select start_source_select
  sonden_nil wrappers_nil

private theorem elaboration_from_phases {source : List SItemTief}
    {prepared : List SItemTief × List (STyp × String)} {unit : UProg}
    (expanded : expandU source = .ok prepared)
    (elaborated : elabUExpanded prepared = .ok unit) : elabU source = .ok unit := by
  simp only [elabU, expanded, bind, Except.bind, elaborated]

-- Retain the whole actual result before projecting success or finding a body.
private theorem shape_elaborated : ∃ unit, Uebersetze.elabU shape = .ok unit := by
  refine ⟨?unit, ?checked⟩
  case checked =>
    apply elaboration_from_phases
    all_goals cbv <;> exact Eq.refl _

/-- The actual elaborator sees the instantiated program, including the arithmetic implementation. -/
theorem shape_elaboration_zeuge : (Uebersetze.elabU shape).toOption.isSome = true := by
  rcases shape_elaborated with ⟨unit, checked⟩
  rw [checked]
  rfl

def expandedDraw : Option SAnw := (expand shape).toOption.bind fun its => its.findSome? fun
  | .fnT s body => if strEq s.name "draw" then some body else none
  | _ => none

private theorem expand_from_phases {source output : List SItemTief}
    (checked : check source = .ok ())
    (unique : uniqueNames ((functionHeads (materialize source)).map (·.name)) = true)
    (rewritten : ((materialize source).mapM
      (({ source, instantiate := true } : Walk).item 100000)) = .ok output)
    (accepted : ordinary source output = true) : expand source = .ok output := by
  simp only [expand, checked, unique, rewritten, accepted, Bool.not_true,
    Bool.false_eq_true, reduceIte, bind, Except.bind, pure, Except.pure]

private theorem shape_expanded : ∃ items, expand shape = .ok items ∧
    beqSAnw ((items.findSome? fun
      | .fnT s body => if strEq s.name "draw" then some body else none
      | _ => none).getD (.other "missing")) (callerBody "$spec$0$area") = true := by
  refine ⟨?items, ?checked, ?body⟩
  case checked =>
    apply expand_from_phases
    all_goals cbv <;> exact Eq.refl _
  case body => cbv

theorem shape_expansion_zeuge : (expand shape).toOption.isSome = true := by
  rcases shape_expanded with ⟨items, checked, _⟩
  rw [checked]
  rfl

theorem shape_rewritten_call_zeuge :
    beqSAnw (expandedDraw.getD (.other "missing")) (callerBody "$spec$0$area") = true := by
  rcases shape_expanded with ⟨items, checked, body⟩
  unfold expandedDraw
  rw [checked]
  exact body

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
      (.ok (.ext .instantiate ["Shape::area", "index into Circles"] [.variable "c"])) = true := by rfl

theorem explicit_statement_parser_zeuge :
    beqSAnw ((parseKopfStmt 1000 (explicitCallTokens.dropLast ++ [.zeichen ";"])).toOption.map Prod.fst
      |>.getD (.other "missing")) (.genericCall "Shape::area" ["index into Circles"] [.variable "c"]) = true := by rfl

theorem missing_function_zeuge :
    check [shapeSpec, .implGroupT "Shape" [.index false "Circles"] [[.reads (.variable "Circles")]] []] =
      .error "spec.function.missing: area" := by rfl

theorem stronger_requires_zeuge :
    check [shapeSpec, shapeImpl { areaImpl with klauseln := .needs (.bin ">=" radius (.lit 1)) :: areaImpl.klauseln }] =
      .error "spec.requires" := by cbv

theorem weaker_ensures_zeuge :
    check [shapeSpec, shapeImpl { areaImpl with
      klauseln := [.effs [.reads (.variable "Circles")], .cost (.lit 20)] }] = .error "spec.ensures" := by cbv

theorem larger_effects_zeuge :
    check [shapeSpec, shapeImpl { areaImpl with klauseln :=
      [.gives (.bin ">=" .res (.lit 1)), .effs [.writes (.variable "Circles")], .cost (.lit 20)] }] =
      .error "spec.effects" := by cbv

theorem larger_cost_zeuge :
    check [shapeSpec, shapeImpl { areaImpl with klauseln :=
      [.gives (.bin ">=" .res (.lit 1)), .effs [.reads (.variable "Circles")], .cost (.lit 51)] }] =
      .error "spec.cost" := by cbv

theorem held_in_spec_zeuge :
    check [.specGroupT "Shape" ["T"] ["E"]
      [{ areaSpec with klauseln := .needs (.call "Held" [.variable "L"]) :: areaSpec.klauseln }], shapeImpl] =
      .error "spec.held" := by rfl

theorem extra_function_zeuge :
    check [shapeSpec, .implGroupT "Shape" [.index false "Circles"] [[.reads (.variable "Circles")]]
      [.fnT areaImpl areaBody, .fnT { areaImpl with name := "perimeter" } areaBody]] =
      .error "spec.function.extra" := by cbv

theorem duplicate_impl_zeuge :
    check [shapeSpec, shapeImpl, shapeImpl] = .error "spec.implementation.duplicate" := by rfl

theorem wrong_signature_zeuge :
    check [shapeSpec, shapeImpl { areaImpl with res := some (.atom "bool") }] = .error "spec.signature" := by cbv

theorem missing_effect_argument_zeuge :
    check [shapeSpec, .implGroupT "Shape" [.index false "Circles"] [] [.fnT areaImpl areaBody]] =
      .error "spec.arguments" := by rfl

theorem unknown_instance_zeuge :
    resolveCall [shapeSpec] caller.params "Shape::area" none [.variable "c"] =
      .error "spec.call.implementation.missing" := by rfl

theorem explicit_statement_resolution_zeuge :
    ({ source := shape, instantiate := true } : Walk).statement [] 1000
      (.genericCall "Shape::area" ["index into Circles"] [.variable "c"]) =
      .ok (.call "$spec$0$area" [.variable "c"]) := by rfl

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
      [.instanceEffects "Shape" [.index false "Circles"]] = .ok [.reads (.variable "Circles")] := by cbv

theorem bare_u32_normalization_zeuge :
    beqSTyp (canonicalType [] 128 (.range (.atom "u32") (.lit 0) (.lit 4294967295) false))
      (.atom "u32") = true := by rfl

end Gabbro.Grammatik.Parser.Spec
