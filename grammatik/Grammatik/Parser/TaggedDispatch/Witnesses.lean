module

public import Grammatik.Parser.TaggedDispatch.Expansion

namespace Gabbro.Grammatik.Parser

public theorem tagged_dispatch_two_cases_zeuge :
    expandTaggedDispatch (.variable "shape") [] []
      [⟨"Circle", some "circleArea"⟩, ⟨"Rect", some "rectArea"⟩]
      (fun e => .ret (some e)) =
    .ok (.cases (.variable "shape")
      [.arm "Circle" (some "#dispatch")
        (.ret (some (.call "circleArea" [.variable "#dispatch"]))),
       .arm "Rect" (some "#dispatch")
        (.ret (some (.call "rectArea" [.variable "#dispatch"])))]) := rfl

public theorem tagged_dispatch_missing_zeuge :
    expandTaggedDispatch (.variable "shape") [] []
      [⟨"Circle", some "circleArea"⟩, ⟨"Rect", none⟩]
      (fun e => .ret (some e)) =
    .error "tagged-dispatch-missing-implementation: Rect" := rfl

end Gabbro.Grammatik.Parser
