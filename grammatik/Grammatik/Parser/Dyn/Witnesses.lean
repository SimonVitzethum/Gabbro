module

public import Grammatik.Parser.TaggedDispatch.Frontend
import all Grammatik.Parser.Spec.Walk
import all Grammatik.Parser.Spec.Items
import all Grammatik.Parser.Spec.Expand
import all Grammatik.Parser.SourceFolds.Range
import all Grammatik.Parser.SourceFolds.Hoist
import all Grammatik.Parser.Dyn.Frontend
import all Grammatik.Parser.Dyn.Collect
import all Grammatik.Parser.Dyn.Rewrite
import all Grammatik.Parser.Spec.Contract
import all Grammatik.Parser.Spec.Resolve
import all Grammatik.Parser.Elab.Uebersetze.Folds.ConstEvaluation
import all Grammatik.Parser.TaggedDispatch.Frontend

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

namespace Gabbro.Grammatik.Parser.Dyn
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- Keep partial large-fuel callbacks as functions. Only the canonical unfolding
-- equation of a fully applied operation may evaluate its selected AST node.
-- This covers the same visitor, collectors, inference and constant-cost reader
-- in every pass; no constructor, callback context or refusal is bypassed.
attribute [local cbv_opaque]
  Spec.Walk.expr Spec.Walk.type Spec.Walk.statement Spec.Walk.statements
  Spec.Walk.item Spec.Walk.constant Spec.resolveKnownBodies Spec.inferType
  Spec.canonicalType Spec.expandEffects Uebersetze.sErsetze Uebersetze.uKonstEval
  SourceFolds.hasRangeFold SourceFolds.hasRangeFoldList SourceFolds.hasRangeFoldAnw SourceFolds.hasRangeFoldAnwList
  SourceFolds.tagFoldNodes SourceFolds.tagFoldNodesList SourceFolds.expandNested statementProducers
  statementsProducers statementUses statementsUses itemUses
  itemsUses lookup containsDynamic
attribute [local cbv_eval]
  Spec.Walk.expr.eq_def Spec.Walk.type.eq_def Spec.Walk.statement.eq_def
  Spec.Walk.statements.eq_def Spec.Walk.item.eq_def Spec.Walk.constant.eq_def
  Spec.resolveKnownBodies.eq_def Spec.inferType.eq_def Spec.canonicalType.eq_def
  Spec.expandEffects.eq_def Uebersetze.sErsetze.eq_def Uebersetze.uKonstEval.eq_def
  SourceFolds.hasRangeFold.eq_def SourceFolds.hasRangeFoldList.eq_def SourceFolds.hasRangeFoldAnw.eq_def
  SourceFolds.hasRangeFoldAnwList.eq_def SourceFolds.tagFoldNodes.eq_def SourceFolds.tagFoldNodesList.eq_def
  SourceFolds.expandNested.eq_def statementProducers.eq_def statementsProducers.eq_def
  statementUses.eq_def statementsUses.eq_def itemUses.eq_def
  itemsUses.eq_def lookup.eq_def containsDynamic.eq_def
attribute [local cbv_eval] Spec.Walk.expr_literal Spec.Walk.type_atom

-- Fixture data exposed only to retain the public witness propositions.
namespace WitnessData

def area : FnSig :=
  ⟨"spec", "area", [("s", .atom "T")], some (.atom "u64"), none,
    [.gives (.bin ">=" .res (.lit 1)), .effs [.param "E"], .cost (.lit 50)], []⟩

def shape : SItemTief := .specGroupT "Shape" ["T"] ["E"] [area]

def implementation (ty : STyp) (effects : List SEffekt) : SItemTief :=
  .implGroupT "Shape" [ty] [effects]
    [.fnT { area with
      art := "impl"
      params := [("s", ty)]
      klauseln := [.gives (.bin ">=" .res (.lit 1)), .effs effects, .cost (.lit 20)] }
      (.block [] (some (.ret (some (.lit 1)))))]

def circle : SItemTief :=
  implementation (.index false "Circles") [.reads (.variable "Circles")]

def rect : SItemTief :=
  implementation (.index false "Rects") [.reads (.variable "Rects")]

def dynamic : STyp := .dyn "Shape" (some "reads Circles , reads Rects } ")

def scene : SItemTief :=
  .tableT "Scene" none (some (.lit 256)) none none false
    [.tSlot [⟨"s", dynamic, none, none, none, false, false⟩]]

def table (name : String) : SItemTief :=
  .tableT name none (some (.lit 4)) none none false
    [.tSlot [⟨"r", .atom "u64", none, none, none, false, false⟩]]

def sample : FnSig :=
  ⟨"impl", "sample", [("i", .index false "Scene"), ("j", .index false "Scene"),
    ("c", .index false "Circles")], some (.atom "u64"), none, [], []⟩

def fieldAt (n : String) : SExpr :=
  .field (.index (.variable "Scene") (.variable n)) "s"

def body : SAnw :=
  .block [.set (fieldAt "i") "=" (.ext .dyn ["Shape"] [.variable "c"]),
    .bind false "a" none (.call "Shape::area" [fieldAt "j"])]
    (some (.ret (some (.variable "a"))))

def fixture : List SItemTief :=
  [table "Circles", table "Rects", shape, circle, rect, scene, .fnT sample body]

def expanded : Except String (List SItemTief) := exportDeclarationUnit fixture

def functionBody (name : String) : Except String SAnw := do
  let items ← expanded
  let some body := items.findSome? (fun
    | .fnT s b => if strEq s.name name then some b else none
    | _ => none) | throw "witness.function"
  return body

end WitnessData

open WitnessData

-- Compose equations of the existing exporter at abstract phase values. Each
-- concrete proof evaluates one selected pass, never the entire nested bind tree.
private theorem export_from_phases
    {source folded rewritten tagged ordinary validated output : List SItemTief}
    {closed : List Closed} {names : List String}
    (foldStage : SourceFolds.prepare source = .ok folded)
    (closeStage : prepare folded = .ok (closed, rewritten))
    (tagStage : exportTaggedUnitDetailed rewritten = .ok (tagged, names))
    (specStage : Spec.prepare (finish closed tagged) = .ok ordinary)
    (checked : checkedOutput tagged ordinary = .ok validated)
    (libraryStage : exportLibraryUnit validated = .ok output) :
    exportDeclarationUnit source = .ok output := by
  simp only [exportDeclarationUnit, exportDeclarationUnitDetailed, foldStage,
    closeStage, tagStage, specStage, checked, libraryStage, bind, Except.bind,
    pure, Except.pure, Except.map]

private theorem export_refused_at_close
    {source folded : List SItemTief} {error : String}
    (foldStage : SourceFolds.prepare source = .ok folded)
    (refused : prepare folded = .error error) :
    exportDeclarationUnit source = .error error := by
  simp only [exportDeclarationUnit, exportDeclarationUnitDetailed, foldStage,
    refused, bind, Except.bind, Except.map]

-- These are only the three unchanged accepted witness inputs. Each actual pass
-- is checked in its own declaration, before any output metadata is inspected.
private inductive ExportFixture where
  | scene | wide | inferred

private def phase_input : ExportFixture → List SItemTief
  | .scene => fixture
  | .wide => fixture ++ [implementation (.array (.atom "u64") (.lit 2)) []]
  | .inferred => fixture ++
      [.fnT { sample with name := "inferred" }
        (.block [.bind false "s" none (.ext .dyn ["Shape"] [.variable "c"]),
          .bind false "a" none (.call "Shape::area" [.variable "s"])]
          (some (.ret (some (.variable "a")))))]

-- Each data value is inferred only from its own producer equality. Projecting
-- .val later reads the retained constructors, not a new evaluation of a getter.
private def fold_result (fixture : ExportFixture) :
    { actual : List SItemTief // SourceFolds.prepare (phase_input fixture) = .ok actual } := by
  cases fixture
  all_goals
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def fold_value (fixture : ExportFixture) : List SItemTief := (fold_result fixture).val
private theorem fold_success (fixture : ExportFixture) :
    SourceFolds.prepare (phase_input fixture) = .ok (fold_value fixture) := (fold_result fixture).property

private def close_result (fixture : ExportFixture) :
    { actual : List Closed × List SItemTief // prepare (fold_value fixture) = .ok actual } := by
  cases fixture
  all_goals
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def close_value (fixture : ExportFixture) : List Closed × List SItemTief := (close_result fixture).val
private theorem close_success (fixture : ExportFixture) :
    prepare (fold_value fixture) = .ok (close_value fixture) := (close_result fixture).property

private def tagged_result (fixture : ExportFixture) :
    { actual : List SItemTief × List String // exportTaggedUnitDetailed (close_value fixture).2 = .ok actual } := by
  cases fixture
  all_goals
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def tagged_value (fixture : ExportFixture) : List SItemTief × List String := (tagged_result fixture).val
private theorem tagged_success (fixture : ExportFixture) :
    exportTaggedUnitDetailed (close_value fixture).2 = .ok (tagged_value fixture) := (tagged_result fixture).property

private def spec_result (fixture : ExportFixture) :
    { actual : List SItemTief // Spec.prepare (finish (close_value fixture).1 (tagged_value fixture).1) = .ok actual } := by
  cases fixture
  all_goals
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def spec_value (fixture : ExportFixture) : List SItemTief := (spec_result fixture).val
private theorem spec_success (fixture : ExportFixture) :
    Spec.prepare (finish (close_value fixture).1 (tagged_value fixture).1) = .ok (spec_value fixture) := (spec_result fixture).property

private def checked_result (fixture : ExportFixture) :
    { actual : List SItemTief // checkedOutput (tagged_value fixture).1 (spec_value fixture) = .ok actual } := by
  cases fixture
  all_goals
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def checked_value (fixture : ExportFixture) : List SItemTief := (checked_result fixture).val
private theorem checked_success (fixture : ExportFixture) :
    checkedOutput (tagged_value fixture).1 (spec_value fixture) = .ok (checked_value fixture) := (checked_result fixture).property

private def library_result (fixture : ExportFixture) :
    { actual : List SItemTief // exportLibraryUnit (checked_value fixture) = .ok actual } := by
  cases fixture
  all_goals
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def library_value (fixture : ExportFixture) : List SItemTief := (library_result fixture).val
private theorem library_success (fixture : ExportFixture) :
    exportLibraryUnit (checked_value fixture) = .ok (library_value fixture) := (library_result fixture).property

private theorem fixture_exported (fixture : ExportFixture) :
    exportDeclarationUnit (phase_input fixture) = .ok (library_value fixture) := by
  exact export_from_phases (source := phase_input fixture) (folded := fold_value fixture)
    (closed := (close_value fixture).1) (rewritten := (close_value fixture).2)
    (tagged := (tagged_value fixture).1) (names := (tagged_value fixture).2)
    (ordinary := spec_value fixture) (validated := checked_value fixture) (output := library_value fixture)
    (fold_success fixture) (close_success fixture) (tagged_success fixture)
    (spec_success fixture) (checked_success fixture) (library_success fixture)

-- Refusals retain the same actual first two passes. Their folded value is fixed
-- before running the refusing close pass, rather than an output metavariable.
private theorem export_refused_from_fold {source : List SItemTief} {error : String}
    (folded : { actual : List SItemTief // SourceFolds.prepare source = .ok actual })
    (refused : prepare folded.val = .error error) : exportDeclarationUnit source = .error error :=
  export_refused_at_close folded.property refused

-- Compute the whole canonical exporter result once. Every projection below is
-- certified only after its actual output list has been bound.
private theorem scene_phases : ∃ items, expanded = .ok items ∧
    (items.filterMap fun
      | .typeT ["tagged"] n [] [] (some (.raw raw)) => some (n, raw)
      | _ => none) = [("#dyn0", "{ GabbroDyn0Case0(index into Circles), GabbroDyn0Case1(index into Rects) }")] ∧
    (items.findSome? fun
      | .fnT sig body => if strEq sig.name "#tagged-#dyn0::Shape::area" then some body else none
      | _ => none) = some (.block [.cases (.variable "s")
      [.arm "GabbroDyn0Case0" (some "#dispatch")
        (.block [.bind false "#dispatch-result" none (.call "$spec$0$area" [.variable "#dispatch"])]
          (some (.ret (some (.variable "#dispatch-result"))))),
       .arm "GabbroDyn0Case1" (some "#dispatch")
        (.block [.bind false "#dispatch-result" none (.call "$spec$1$area" [.variable "#dispatch"])]
          (some (.ret (some (.variable "#dispatch-result")))))]] none) ∧
    (items.findSome? fun
      | .fnT sig body => if strEq sig.name "sample" then some body else none
      | _ => none) = some (.block
      [.set (.field (.index (.field (.variable "Scene") "slots") (.variable "i")) "s") "="
        (.call "GabbroDyn0Case0" [.variable "c"]),
       .bind false "a" none (.call "#tagged-#dyn0::Shape::area"
         [.field (.index (.field (.variable "Scene") "slots") (.variable "j")) "s"])]
      (some (.ret (some (.variable "a"))))) ∧
    (items.filterMap fun
      | .fnT sig _ => if strEq sig.name "#tagged-#dyn0::Shape::area" then
          some (functionEffects sig, cost items sig) else none
      | _ => none) = [([.reads (.variable "Circles"), .reads (.variable "Rects")], some 51)] := by
  refine ⟨library_value .scene, ?checked, ?sum, ?dispatch, ?producer, ?cost⟩
  case checked => exact fixture_exported .scene
  case sum => cbv
  case dispatch => cbv
  case producer => cbv
  case cost => cbv

private theorem map_from_refusal {α β : Type} {source : Except String α}
    {read : α → β} {error : String} (checked : source = .error error) :
    source.map read = .error error := by
  rw [checked]
  rfl

private theorem functionBody_of_phase {items : List SItemTief} {name : String} {body : SAnw}
    (checked : expanded = .ok items)
    (found : (items.findSome? fun
      | .fnT sig body => if strEq sig.name name then some body else none
      | _ => none) = some body) : functionBody name = .ok body := by
  unfold functionBody
  rw [checked]
  simp only [bind, Except.bind, found, pure, Except.pure]

/-- The real declaration entry point closes both linked implementations into one ordinary sum. -/
public theorem scene_sum_zeuge :
    (expanded.map fun items => items.filterMap fun
      | .typeT ["tagged"] n [] [] (some (.raw raw)) => some (n, raw)
      | _ => none) =
    .ok [("#dyn0", "{ GabbroDyn0Case0(index into Circles), GabbroDyn0Case1(index into Rects) }")] := by
  rcases scene_phases with ⟨items, checked, sum, _⟩
  rw [checked]
  exact congrArg Except.ok sum

/-- Exact dispatch match: both variants call the canonical §5.1 implementation functions. -/
public theorem scene_dispatch_zeuge :
    functionBody "#tagged-#dyn0::Shape::area" =
    .ok (.block [.cases (.variable "s")
      [.arm "GabbroDyn0Case0" (some "#dispatch")
        (.block [.bind false "#dispatch-result" none (.call "$spec$0$area" [.variable "#dispatch"])]
          (some (.ret (some (.variable "#dispatch-result"))))),
       .arm "GabbroDyn0Case1" (some "#dispatch")
        (.block [.bind false "#dispatch-result" none (.call "$spec$1$area" [.variable "#dispatch"])]
          (some (.ret (some (.variable "#dispatch-result")))))]] none) := by
  rcases scene_phases with ⟨items, checked, _, dispatch, _⟩
  exact functionBody_of_phase checked dispatch

/-- Producer and consumer are connected in the same Scene body, including canonical table places. -/
public theorem scene_producer_and_call_zeuge :
    functionBody "sample" =
    .ok (.block
      [.set (.field (.index (.field (.variable "Scene") "slots") (.variable "i")) "s") "="
        (.call "GabbroDyn0Case0" [.variable "c"]),
       .bind false "a" none (.call "#tagged-#dyn0::Shape::area"
         [.field (.index (.field (.variable "Scene") "slots") (.variable "j")) "s"])]
      (some (.ret (some (.variable "a"))))) := by
  rcases scene_phases with ⟨items, checked, _, _, producer, _⟩
  exact functionBody_of_phase checked producer

/-- A wider-than-8-byte payload is carried as a case, not refused: the closed sum
    travels through the existing tagged sum layout. Lowering the multi-word
    payload is the Stage-0 s0-gaps1 premise (`sumPayloadWords`/`sumOff`,
    `encodeWords` sum branch). -/
public theorem scene_wide_payload_closed_zeuge :
    ((close (fixture ++ [implementation (.array (.atom "u64") (.lit 2)) []]) 1 dynamic).map
      (fun c => c.cases.map (·.payload))) =
    .ok [.index false "Circles", .index false "Rects", .array (.atom "u64") (.lit 2)] := rfl

/-- A non-scalar payload behind a type alias is carried as written. -/
public theorem scene_alias_payload_closed_zeuge :
    ((close (fixture ++ [.typeT [] "Handle" [] [] (some (.index false "Circles")),
      implementation (.atom "Handle") []]) 1 dynamic).map
      (fun c => c.cases.map (·.payload))) =
    .ok [.index false "Circles", .index false "Rects", .atom "Handle"] := rfl

/-- The wide payload reaches the ordinary declaration expansion unchanged. -/
public theorem scene_wide_payload_accepted_zeuge :
    (exportDeclarationUnit
      (fixture ++ [implementation (.array (.atom "u64") (.lit 2)) []])).map (fun _ => ()) =
    .ok () := by
  change (exportDeclarationUnit (phase_input .wide)).map (fun _ => ()) = .ok ()
  rw [fixture_exported .wide]
  rfl

public theorem scene_equality_refused_zeuge :
    (exportDeclarationUnit (fixture ++
      [.fnT { sample with name := "equal" }
        (.block [] (some (.ret (some (.bin "==" (fieldAt "i") (fieldAt "j"))))))])).map (fun _ => ()) =
    .error "dyn.equality" := by
  apply map_from_refusal
  refine export_refused_from_fold ?folded ?refused
  case folded =>
    refine ⟨?actual, ?origin⟩
    case origin => cbv <;> exact Eq.refl _
  case refused => cbv

public theorem scene_implementation_test_refused_zeuge :
    (exportDeclarationUnit (fixture ++
      [.fnT { sample with name := "inspect" }
        (.block [.cases (fieldAt "i") []] none)])).map (fun _ => ()) =
    .error "dyn.implementation-test" := by
  apply map_from_refusal
  refine export_refused_from_fold ?folded ?refused
  case folded =>
    refine ⟨?actual, ?origin⟩
    case origin => cbv <;> exact Eq.refl _
  case refused => cbv

public theorem scene_bound_required_zeuge :
    (close [shape, circle] 0 (.dyn "Shape" none)).map (fun _ => ()) =
    .error "dyn.effects.required: Shape" := rfl

public theorem scene_dispatch_bound_and_cost_zeuge :
    (expanded.map fun items => items.filterMap fun
      | .fnT sig _ => if strEq sig.name "#tagged-#dyn0::Shape::area" then
          some (functionEffects sig, cost items sig) else none
      | _ => none) =
    .ok [([.reads (.variable "Circles"), .reads (.variable "Rects")], some 51)] := by
  rcases scene_phases with ⟨items, checked, _, _, _, cost⟩
  rw [checked]
  exact congrArg Except.ok cost

/-- Excluding Rects excludes that implementation from the linked sum. -/
public theorem scene_effect_filter_zeuge :
    ((close fixture 0 (.dyn "Shape" (some "reads Circles } "))).map
      (fun c => c.cases.map (·.implementation))) = .ok [0] := rfl

/-- An excluded oversized implementation is irrelevant to a read-only bound. -/
public theorem scene_excluded_large_payload_zeuge :
    ((close (fixture ++ [implementation (.array (.atom "u64") (.lit 2))
      [.writes (.variable "Rects")]]) 0 dynamic).map (fun c => c.cases.length)) = .ok 2 := rfl

public theorem scene_downcast_refused_zeuge :
    (exportDeclarationUnit (fixture ++
      [.fnT { sample with name := "narrow" }
        (.block [.trim (fieldAt "i") "u64" (.block [] none)] none)])).map (fun _ => ()) =
    .error "dyn.downcast" := by
  apply map_from_refusal
  refine export_refused_from_fold ?folded ?refused
  case folded =>
    refine ⟨?actual, ?origin⟩
    case origin => cbv <;> exact Eq.refl _
  case refused => cbv

-- Inspect the final checked value only after the six named success boundaries.
private theorem inferred_metadata :
    ((library_value .inferred).filterMap fun
      | .fnT sig body => if strEq sig.name "inferred" then some body else none
      | _ => none) = [.block [.bind false "s" none (.call "GabbroDyn0Case0" [.variable "c"]),
      .bind false "a" none (.call "#tagged-#dyn0::Shape::area" [.variable "s"])]
      (some (.ret (some (.variable "a"))))] := by cbv

/-- A producer in an unannotated let retains enough type information for a later abstract call. -/
public theorem scene_inferred_let_zeuge :
    ((exportDeclarationUnit (fixture ++
      [.fnT { sample with name := "inferred" }
        (.block [.bind false "s" none (.ext .dyn ["Shape"] [.variable "c"]),
          .bind false "a" none (.call "Shape::area" [.variable "s"])]
          (some (.ret (some (.variable "a")))))]))
      .map fun items => items.filterMap fun
        | .fnT sig body => if strEq sig.name "inferred" then some body else none
        | _ => none) =
    .ok [.block [.bind false "s" none (.call "GabbroDyn0Case0" [.variable "c"]),
      .bind false "a" none (.call "#tagged-#dyn0::Shape::area" [.variable "s"])]
      (some (.ret (some (.variable "a"))))] := by
  change ((exportDeclarationUnit (phase_input .inferred)).map fun items => items.filterMap fun
    | .fnT sig body => if strEq sig.name "inferred" then some body else none
    | _ => none) = _
  rw [fixture_exported .inferred]
  exact congrArg Except.ok inferred_metadata

/-- Reordered bounds denote one generated type, not two incompatible representations. -/
public theorem scene_bound_order_zeuge :
    ((catalog fixture [dynamic, .dyn "Shape" (some "reads Rects , reads Circles } ")])
      .map (fun cs => cs.length)) = .ok 1 := rfl

end Gabbro.Grammatik.Parser.Dyn
