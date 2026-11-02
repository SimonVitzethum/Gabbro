module
public import Grammatik.Parser.Elab.Generic.PipelineWitness
public import Grammatik.Parser.Spec.Zeugen
@[expose] public section
namespace Gabbro.Grammatik.Parser.Generic
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The plan's total header and effect/cost expressions. The two-element body isolates
    spec-bound instantiation from the independently missing surface fold parser. -/
def totalSignature : FnSig :=
  { art := "", name := "total", params := [("xs", .array (.atom "T") (.variable "N"))],
    res := some (.atom "u64"), fehler := none,
    generics := [.type "T" ["Shape"], .constant "N" (.range (.atom "u32") (.lit 1) (.lit 4096) false)],
    klauseln := [.effs [.instanceEffects "Shape" [.atom "T"]],
      .cost (.bin "*" (.variable "N") (.lit 60))] }

def totalBody (area : String := "Shape::area") : SAnw :=
  .block [.bind false "first" none (.index (.variable "xs") (.lit 0)),
    .bind false "a" none (.call area [.variable "first"]),
    .bind false "b" none (.call area [.index (.variable "xs") (.lit 1)])]
    (some (.ret (some (.bin "+" (.variable "a") (.variable "b")))))

def totalKey : Instance := ⟨"total", ["index into Circles", "2"]⟩

def totalCaller : SItemTief :=
  .fnT { art := "", name := "measure", params := [("xs", .array (.index false "Circles") (.lit 2))],
    res := some (.atom "u64"), fehler := none, klauseln := [] }
    (.block [.bind false "result_value" none
      (.ext .instantiate ["total", "index into Circles", "2"] [.variable "xs"])]
      (some (.ret (some (.variable "result_value")))))

def boundedSource : List SItemTief :=
  [Spec.circles, Spec.shapeSpec, Spec.shapeImpl, .fnT totalSignature (totalBody), totalCaller]

/-- The same two front-end entries called by elabU, before ordinary G admission. -/
def boundedExpansion : Except String (List SItemTief) := do
  exportDeclarationUnit (← expand boundedSource)

theorem total_body_parametric_zeuge :
    checkParametricBody boundedSource totalSignature (totalBody) = .ok () := rfl

theorem multiple_bounds_parser_zeuge :
    (parsedSource "fn both[T: Shape + Other](x: T) -> T { return x; }").map (fun items =>
      match items with
      | [.fnT sig _] => beqSGenericParams sig.generics [.type "T" ["Shape", "Other"]]
      | _ => false) = .ok true := by decide +kernel


/-- Both area calls become calls to the Circles implementation, with no abstract call left.
    The instance effect becomes reads Circles and its constant budget becomes 2 * 60. -/
theorem total_circles_direct_calls_zeuge :
    boundedExpansion.map (fun items => items.any fun
      | .fnT sig body => strEq sig.name (instanceName totalKey) &&
          beqSTypList (sig.params.map Prod.snd) [.array (.index false "Circles") (.lit 2)] &&
          beqSAnw body (totalBody (Spec.implementationName 0 "area")) &&
          beqSKlauselList sig.klauseln [.effs [.reads (.variable "Circles")],
            .cost (.bin "*" (.lit 2) (.lit 60))]
      | _ => false) = .ok true := rfl

/-- The full declaration expansion inhabits the canonical ordinary-form theorem. -/
theorem bounded_output_ordinary_zeuge :
    boundedExpansion.map (Spec.ordinary boundedSource) = .ok true := rfl

theorem all_bounds_required_zeuge :
    checkTypeBounds [Spec.shapeSpec, Spec.shapeImpl, .specGroupT "Other" ["U"] [] []]
      (.index false "Circles") ["Shape", "Other"] =
      .error "generic.bound.implementation.missing: Other" := rfl

theorem missing_impl_zeuge :
    expand [Spec.shapeSpec, .fnT totalSignature (totalBody), totalCaller] =
      .error "generic.bound.implementation.missing: Shape" := rfl

/-- An alias uses the unified spec resolver's canonical type identity. -/
theorem bound_alias_zeuge :
    checkTypeBounds [Spec.shapeSpec, Spec.shapeImpl,
      .typeT [] "Circle" [] [] (some (.index false "Circles"))]
      (.atom "Circle") ["Shape"] = .ok () := rfl

def abstractSignature : FnSig :=
  { art := "", name := "abstract", params := [("x", .atom "T")],
    res := some (.atom "T"), fehler := none, klauseln := [], generics := [.type "T" ["Shape"]] }

/-- Unused templates are checked, before even a numerical instance could enable arithmetic. -/
theorem abstract_arithmetic_refused_zeuge :
    expand [Spec.shapeSpec, .fnT abstractSignature
      (.block [] (some (.ret (some (.bin "+" (.variable "x") (.lit 1))))))] =
      .error "generic.parametricity.arithmetic: +" := rfl

theorem inferred_binding_remains_abstract_zeuge :
    checkParametricBody [Spec.shapeSpec] abstractSignature
      (.block [.bind false "copy" none (.variable "x")]
        (some (.ret (some (.bin "+" (.variable "copy") (.lit 1)))))) =
      .error "generic.parametricity.arithmetic: +" := rfl

theorem abstract_comparison_refused_zeuge :
    checkParametricBody [Spec.shapeSpec] { abstractSignature with res := some (.atom "bool") }
      (.block [] (some (.ret (some (.bin "==" (.variable "x") (.variable "x")))))) =
      .error "generic.parametricity.comparison: ==" := rfl

theorem abstract_field_refused_zeuge :
    checkParametricBody [Spec.shapeSpec] abstractSignature
      (.block [] (some (.ret (some (.field (.variable "x") "r"))))) =
      .error "generic.parametricity.field" := rfl

theorem concrete_annotation_refused_zeuge :
    checkParametricBody [Spec.shapeSpec] abstractSignature
      (.block [.bind false "copy" (some (.atom "u64")) (.variable "x")] none) =
      .error "generic.parametricity.binding" := rfl

theorem unwritten_bound_refused_zeuge :
    checkParametricBody [Spec.shapeSpec]
      { abstractSignature with generics := [.type "T" []], res := some (.atom "u64") }
      (.block [] (some (.ret (some (.call "Shape::area" [.variable "x"]))))) =
      .error "generic.parametricity.bound: Shape" := rfl

/-- Generic forwarding cannot obtain a bound from the eventual concrete specialization. -/
theorem forwarded_bound_refused_zeuge :
    checkParametricBody [Spec.shapeSpec, .fnT abstractSignature (.block [] none)]
      { abstractSignature with name := "forward", generics := [.type "T" []] }
      (.block [] (some (.ret (some (.ext .instantiate ["abstract", "T"] [.variable "x"]))))) =
      .error "generic.parametricity.bound: Shape" := rfl

/-- Inferred results of spec functions returning T remain abstract too. -/
theorem abstract_spec_result_refused_zeuge :
    checkParametricBody [.specGroupT "Copy" ["U"] []
      [{ art := "spec", name := "copy", params := [("x", .atom "U")],
         res := some (.atom "U"), fehler := none, klauseln := [.effs [], .cost (.lit 1)] }]]
      { abstractSignature with generics := [.type "T" ["Copy"]] }
      (.block [.bind false "copy" none (.call "Copy::copy" [.variable "x"])]
        (some (.ret (some (.bin "+" (.variable "copy") (.lit 1)))))) =
      .error "generic.parametricity.arithmetic: +" := rfl

/-- A global concrete alias with the same spelling as T cannot impersonate the binder. -/
theorem concrete_alias_is_not_parameter_zeuge :
    checkParametricBody [.typeT [] "T" [] [] (some (.atom "u64")),
      .globT false "default_value" (.atom "T") (.one (.lit 0)) none none false]
      abstractSignature (.block [] (some (.ret (some (.variable "default_value"))))) =
      .error "generic.parametricity.binding" := rfl


theorem concrete_alias_call_refused_zeuge :
    checkParametricBody [.typeT [] "T" [] [] (some (.atom "u64")),
      .fnT { art := "", name := "concrete", params := [("x", .atom "T")],
        res := none, fehler := none, klauseln := [] } (.block [] none)]
      abstractSignature (.block [.call "concrete" [.variable "x"]] none) =
      .error "generic.parametricity.argument: concrete" := rfl


/-- Explicit spec type arguments share the generic application AST and defer to the spec pass. -/
theorem explicit_bound_statement_zeuge :
    ((do
      let items ← expand [Spec.shapeSpec, Spec.shapeImpl,
        .fnT { abstractSignature with name := "visit", res := none }
          (.block [.genericCall "Shape::area" ["T"] [.variable "x"]] none),
        .fnT { art := "", name := "entry", params := [("c", .index false "Circles")],
          res := none, fehler := none, klauseln := [] }
          (.block [.genericCall "visit" ["index into Circles"] [.variable "c"]] none)]
      exportDeclarationUnit items) : Except String (List SItemTief)).map (fun items => items.any fun
        | .fnT sig body => strEq sig.name (instanceName ⟨"visit", ["index into Circles"]⟩) &&
            beqSAnw body (.block [.call "$spec$0$area" [.variable "x"]] none)
        | _ => false) = .ok true := rfl

/-- Full source parsing, instance closure and declaration expansion, with the plan's header.
    The explicit sum is the two-element fold expansion; surface add-fold parsing is separate. -/
def boundedText : String :=
  "table Circles count 4 { slot { r: u64, } } " ++
  "spec Shape[T; effects E] { fn area(s: T) -> u64 " ++
  "ensures result >= 1 effects { E } costs <= 50 ops; } " ++
  "impl Shape[index into Circles; effects { reads Circles }] { " ++
  "fn area(s: index into Circles) -> u64 ensures result >= 1 " ++
  "effects { reads Circles } costs <= 20 ops { return 3 * Circles[s].r * Circles[s].r + 1; } } " ++
  "fn total[T: Shape, N: const u32 in 1 .. 4096](xs: [T; N]) -> u64 " ++
  "effects { Shape[T] } costs <= N * 60 ops { " ++
  "let first = xs[0]; let a = Shape::area(first); let b = Shape::area(xs[1]); return a + b; } " ++
  "fn measure(xs: [index into Circles; 2]) -> u64 { " ++
  "let result_value = total::[index into Circles, 2](xs); return result_value; }"

theorem bounded_source_direct_calls_zeuge :
    ((parsedSource boundedText).bind expand |>.bind exportDeclarationUnit).map
      (fun items => items.any fun
        | .fnT sig body => strEq sig.name (instanceName totalKey) &&
            beqSAnw body (totalBody "$spec$0$area")
        | _ => false) = .ok true := by decide +kernel

end Gabbro.Grammatik.Parser.Generic
