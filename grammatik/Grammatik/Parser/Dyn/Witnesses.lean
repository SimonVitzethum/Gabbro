module

public import Grammatik.Parser.TaggedDispatch.Frontend

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

/-- The real declaration entry point closes both linked implementations into one ordinary sum. -/
public theorem scene_sum_zeuge :
    (expanded.map fun items => items.filterMap fun
      | .typeT ["tagged"] n [] [] (some (.raw raw)) => some (n, raw)
      | _ => none) =
    .ok [("#dyn0", "{ GabbroDyn0Case0(index into Circles), GabbroDyn0Case1(index into Rects) }")] := rfl

/-- Exact dispatch match: both variants call the canonical §5.1 implementation functions. -/
public theorem scene_dispatch_zeuge :
    functionBody "#tagged-#dyn0::Shape::area" =
    .ok (.block [.cases (.variable "s")
      [.arm "GabbroDyn0Case0" (some "#dispatch")
        (.block [.bind false "#dispatch-result" none (.call "$spec$0$area" [.variable "#dispatch"])]
          (some (.ret (some (.variable "#dispatch-result"))))),
       .arm "GabbroDyn0Case1" (some "#dispatch")
        (.block [.bind false "#dispatch-result" none (.call "$spec$1$area" [.variable "#dispatch"])]
          (some (.ret (some (.variable "#dispatch-result")))))]] none) := rfl

/-- Producer and consumer are connected in the same Scene body, including canonical table places. -/
public theorem scene_producer_and_call_zeuge :
    functionBody "sample" =
    .ok (.block
      [.set (.field (.index (.field (.variable "Scene") "slots") (.variable "i")) "s") "="
        (.call "GabbroDyn0Case0" [.variable "c"]),
       .bind false "a" none (.call "#tagged-#dyn0::Shape::area"
         [.field (.index (.field (.variable "Scene") "slots") (.variable "j")) "s"])]
      (some (.ret (some (.variable "a"))))) := rfl

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
    .ok () := rfl

public theorem scene_equality_refused_zeuge :
    (exportDeclarationUnit (fixture ++
      [.fnT { sample with name := "equal" }
        (.block [] (some (.ret (some (.bin "==" (fieldAt "i") (fieldAt "j"))))))])).map (fun _ => ()) =
    .error "dyn.equality" := rfl

public theorem scene_implementation_test_refused_zeuge :
    (exportDeclarationUnit (fixture ++
      [.fnT { sample with name := "inspect" }
        (.block [.cases (fieldAt "i") []] none)])).map (fun _ => ()) =
    .error "dyn.implementation-test" := rfl

public theorem scene_bound_required_zeuge :
    (close [shape, circle] 0 (.dyn "Shape" none)).map (fun _ => ()) =
    .error "dyn.effects.required: Shape" := rfl

public theorem scene_dispatch_bound_and_cost_zeuge :
    (expanded.map fun items => items.filterMap fun
      | .fnT sig _ => if strEq sig.name "#tagged-#dyn0::Shape::area" then
          some (functionEffects sig, cost items sig) else none
      | _ => none) =
    .ok [([.reads (.variable "Circles"), .reads (.variable "Rects")], some 51)] := rfl

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
    .error "dyn.downcast" := rfl

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
      (some (.ret (some (.variable "a"))))] := rfl

/-- Reordered bounds denote one generated type, not two incompatible representations. -/
public theorem scene_bound_order_zeuge :
    ((catalog fixture [dynamic, .dyn "Shape" (some "reads Rects , reads Circles } ")])
      .map (fun cs => cs.length)) = .ok 1 := rfl

end Gabbro.Grammatik.Parser.Dyn
