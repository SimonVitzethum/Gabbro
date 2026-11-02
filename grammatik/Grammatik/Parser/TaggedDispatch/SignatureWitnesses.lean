module

import Grammatik.Parser.TaggedDispatch.Signature

namespace Gabbro.Grammatik.Parser

private def dispatchSignature : FnSig :=
  ⟨"spec", "area", [("before", .atom "bool"), ("self", .atom "Self"),
    ("after", .atom "bool")], some (.atom "bool"), none, []⟩

private def dispatchActual (name : String) (variant : STyp) : FnSig :=
  { dispatchSignature with art := "impl", name,
    params := [("a", .atom "bool"), ("value", variant), ("b", .atom "bool")] }

private def dispatchImplementations : List TaggedImplementation :=
  [⟨.atom "u8", [("area", dispatchActual "circleArea" (.atom "u8"))]⟩,
   ⟨.atom "bool", [("area", dispatchActual "rectArea" (.atom "bool"))]⟩]

/-- An otherwise dispatchable member returning Self does not block either case. -/
public theorem tagged_group_static_ignored_zeuge :
    (checkTaggedGroup [dispatchSignature,
      ⟨"spec", "copy", [("self", .atom "Self")], some (.atom "Self"), none, []⟩]
      [("Circle", some (.atom "u8")), ("Rect", some (.atom "bool"))]
      dispatchImplementations).map (fun fs => fs.map (fun f => f.2.map (·.implementation))) =
    .ok [[some "circleArea", some "rectArea"]] := rfl

/-- Lookup covers the second member and second case, rather than stopping after
    the first complete member or the first variant implementation. -/
public theorem tagged_group_every_member_zeuge :
    (checkTaggedGroup [dispatchSignature, { dispatchSignature with name := "perimeter" }]
      [("Circle", some (.atom "u8")), ("Rect", some (.atom "bool"))]
      [⟨.atom "u8", [("area", dispatchActual "circleArea" (.atom "u8")),
        ("perimeter", dispatchActual "circlePerimeter" (.atom "u8"))]⟩,
       ⟨.atom "bool", [("area", dispatchActual "rectArea" (.atom "bool"))]⟩]).map (fun _ => ()) =
      .error "tagged-dispatch-missing-implementation: Rect::perimeter" := rfl

public theorem tagged_group_missing_member_zeuge :
    (checkTaggedGroup [dispatchSignature]
      [("Circle", some (.atom "u8")), ("Rect", some (.atom "bool"))]
      [⟨.atom "u8", [("area", dispatchActual "circleArea" (.atom "u8"))]⟩]).toOption.isSome = false := by decide

public theorem tagged_wrong_parameter_refused_zeuge :
    checkTaggedSignature (.atom "u8") dispatchSignature
      (dispatchActual "wrongReceiver" (.atom "bool")) =
      .error "tagged-dispatch-signature-mismatch: wrongReceiver" := rfl

public theorem tagged_wrong_channel_refused_zeuge :
    checkTaggedSignature (.atom "u8") dispatchSignature
      { dispatchActual "wrongChannel" (.atom "u8") with fehler := some "Failure" } =
      .error "tagged-dispatch-signature-mismatch: wrongChannel" := rfl

public theorem tagged_multiple_receivers_not_dispatched_zeuge :
    taggedDispatchable { dispatchSignature with
      params := [("x", .atom "Self"), ("y", .atom "Self")] } = false := rfl

public theorem tagged_nested_receiver_not_dispatched_zeuge :
    taggedDispatchable { dispatchSignature with
      params := [("x", .atom "Self"), ("ys", .array (.atom "Self") (.lit 2))] } = false := rfl

public theorem tagged_held_refused_zeuge :
    (checkTaggedGroup [{ dispatchSignature with klauseln := [.needs (.call "Held" [.variable "L"])] }]
      [("Circle", some (.atom "u8"))] dispatchImplementations).toOption.isSome = false := by decide

end Gabbro.Grammatik.Parser
