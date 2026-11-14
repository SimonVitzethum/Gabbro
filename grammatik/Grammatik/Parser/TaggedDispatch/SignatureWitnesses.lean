module

public import Grammatik.Parser.TaggedDispatch.Signature
public import Grammatik.Parser.Spec.Check
import Lean.Elab.Tactic.Cbv

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

namespace Gabbro.Grammatik.Parser

attribute [local cbv_eval] strEq_apply_eq_decide

@[expose] public def dispatchSignature : FnSig :=
  ⟨"spec", "area", [("before", .atom "bool"), ("self", .atom "Self"),
    ("after", .atom "bool")], some (.atom "bool"), none, [], []⟩

@[expose] public def dispatchActual (name : String) (variant : STyp) : FnSig :=
  { dispatchSignature with
    art := "impl"
    name := name
    params := [("a", .atom "bool"), ("value", variant), ("b", .atom "bool")] }

@[expose] public def dispatchImplementations : List TaggedImplementation :=
  [⟨.atom "u8", [("area", dispatchActual "circleArea" (.atom "u8"))]⟩,
   ⟨.atom "bool", [("area", dispatchActual "rectArea" (.atom "bool"))]⟩]

/-- An otherwise dispatchable member returning Self does not block either case. -/
public theorem tagged_group_static_ignored_zeuge :
    (checkTaggedGroup [dispatchSignature,
      ⟨"spec", "copy", [("self", .atom "Self")], some (.atom "Self"), none, [], []⟩]
      [("Circle", some (.atom "u8")), ("Rect", some (.atom "bool"))]
      dispatchImplementations).map (fun fs => fs.map (fun f => f.2.map (·.implementation))) =
    .ok [[some "circleArea", some "rectArea"]] := by cbv

/-- Lookup covers the second member and second case, rather than stopping after
    the first complete member or the first variant implementation. -/
public theorem tagged_group_every_member_zeuge :
    (checkTaggedGroup [dispatchSignature, { dispatchSignature with name := "perimeter" }]
      [("Circle", some (.atom "u8")), ("Rect", some (.atom "bool"))]
      [⟨.atom "u8", [("area", dispatchActual "circleArea" (.atom "u8")),
        ("perimeter", dispatchActual "circlePerimeter" (.atom "u8"))]⟩,
       ⟨.atom "bool", [("area", dispatchActual "rectArea" (.atom "bool"))]⟩]).map (fun _ => ()) =
      .error "tagged-dispatch-missing-implementation: Rect::perimeter" := by cbv

public theorem tagged_group_missing_member_zeuge :
    (checkTaggedGroup [dispatchSignature]
      [("Circle", some (.atom "u8")), ("Rect", some (.atom "bool"))]
      [⟨.atom "u8", [("area", dispatchActual "circleArea" (.atom "u8"))]⟩]).toOption.isSome = false := by cbv

public theorem tagged_wrong_parameter_refused_zeuge :
    checkTaggedSignature (.atom "u8") dispatchSignature
      (dispatchActual "wrongReceiver" (.atom "bool")) =
      .error "tagged-dispatch-signature-mismatch: wrongReceiver" := by cbv

public theorem tagged_wrong_channel_refused_zeuge :
    checkTaggedSignature (.atom "u8") dispatchSignature
      { dispatchActual "wrongChannel" (.atom "u8") with fehler := some "Failure" } =
      .error "tagged-dispatch-signature-mismatch: wrongChannel" := by cbv

public theorem tagged_multiple_receivers_not_dispatched_zeuge :
    taggedDispatchable { dispatchSignature with
      params := [("x", .atom "Self"), ("y", .atom "Self")] } = false := by cbv

public theorem tagged_nested_receiver_not_dispatched_zeuge :
    taggedDispatchable { dispatchSignature with
      params := [("x", .atom "Self"), ("ys", .array (.atom "Self") (.lit 2))] } = false := by cbv

public theorem tagged_held_refused_zeuge :
    (checkTaggedGroup [{ dispatchSignature with klauseln := [.needs (.call "Held" [.variable "L"])] }]
      [("Circle", some (.atom "u8"))] dispatchImplementations).toOption.isSome = false := by cbv

@[expose] public def dispatchConformanceSignature : FnSig :=
  { dispatchSignature with klauseln := [.effs [], .cost (.lit 1)] }

@[expose] public def dispatchConformanceActual (variant : STyp) : FnSig :=
  { dispatchActual "area" variant with klauseln := dispatchConformanceSignature.klauseln }

@[expose] public def dispatchConformanceItems (second : FnSig) : List SItemTief :=
  [.specGroupT "Shape" ["Self"] [] [dispatchConformanceSignature],
   .implGroupT "Shape" [.atom "u8"] []
     [.fnT (dispatchConformanceActual (.atom "u8")) (.block [] none)],
   .implGroupT "Shape" [.atom "bool"] [] [.fnT second (.block [] none)]]

set_option maxRecDepth 100000 in
/-- The unified spec gate accepts both variant signatures, with a receiver between arguments. -/
public theorem tagged_unified_signature_accepted_zeuge :
    Spec.check (dispatchConformanceItems (dispatchConformanceActual (.atom "bool"))) =
      .ok () := by cbv

set_option maxRecDepth 100000 in
/-- The unified gate names signature failures in the second variant, covering the receiver,
    result and reason channel before any dispatcher is admitted. -/
public theorem tagged_unified_signature_refused_zeuge :
    Spec.check (dispatchConformanceItems (dispatchConformanceActual (.atom "u8"))) =
      .error "spec.signature" ∧
    Spec.check (dispatchConformanceItems
      { dispatchConformanceActual (.atom "bool") with res := some (.atom "u8") }) =
      .error "spec.signature" ∧
    Spec.check (dispatchConformanceItems
      { dispatchConformanceActual (.atom "bool") with fehler := some "Failure" }) =
      .error "spec.signature" := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

end Gabbro.Grammatik.Parser
