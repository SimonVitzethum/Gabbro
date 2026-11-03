module

import Grammatik.Parser.TaggedDispatch.Frontend
import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic

namespace Gabbro.Grammatik.Parser
open Uebersetze UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- Two distinct payload types, a receiver between ordinary arguments, and a
    static member with complete conforming implementations in the same group. -/
private def taggedSource (rectResult : String) : String :=
  "spec Shape[T] { " ++
  "fn area(prefix: bool, s: T, suffix: bool) -> bool effects {} costs <= 50 ops; " ++
  "fn copy(s: T) -> T effects {} costs <= 50 ops; } " ++
  "impl Shape[u8] { fn area(prefix: bool, s: u8, suffix: bool) -> bool " ++
  "effects {} costs <= 20 ops { return prefix; } fn copy(s: u8) -> u8 effects {} costs <= 20 ops { return s; } } " ++
  "impl Shape[bool] { fn area(prefix: bool, s: bool, suffix: bool) -> " ++ rectResult ++
  " effects {} costs <= 20 ops { return suffix; } fn copy(s: bool) -> bool effects {} costs <= 20 ops { return s; } } " ++
  "tagged type AnyShape = { Circle(u8), Rect(bool) } by Shape; " ++
  "impl fn sample(s: AnyShape) -> bool effects {} costs <= 20 ops { " ++
  "let answer = Shape::area(false, s, true); return answer; }"

private def taggedSourceItems (rectResult : String) : Except String (List SItemTief) := do
  parseTopTief (← lex (taggedSource rectResult))

private def taggedSourceExpanded (rectResult : String) : Except String (List SItemTief) := do
  exportDeclarationUnit (uMembers (pre108 (← taggedSourceItems rectResult)))

private def taggedSourceBody (name : String) : Except String SAnw := do
  let items ← taggedSourceExpanded "bool"
  let bodies := items.filterMap fun
    | .fnT sig body => if strEq sig.name name then some body else none
    | _ => none
  match bodies with
  | [body] => pure body
  | _ => throw "witness: generated function not unique"

private def taggedExpectedMatch : SAnw :=
  .block [.cases (.variable "s")
    [.arm "Circle" (some "#dispatch")
      (.block [.bind false "#dispatch-result" none
        (.call "$spec$0$area"
          [.variable "prefix", .variable "#dispatch", .variable "suffix"])]
        (some (.ret (some (.variable "#dispatch-result"))))),
     .arm "Rect" (some "#dispatch")
      (.block [.bind false "#dispatch-result" none
        (.call "$spec$1$area"
          [.variable "prefix", .variable "#dispatch", .variable "suffix"])]
        (some (.ret (some (.variable "#dispatch-result")))))]] none

/-- Source text → lexer → group/by parser → pre108 → checked declaration
    expansion → the exact generated match, with both case implementations. -/
public theorem tagged_source_match_zeuge :
    taggedSourceBody "#tagged-AnyShape::Shape::area" = .ok taggedExpectedMatch := rfl

/-- The source call is connected to that generated function in the same pass. -/
public theorem tagged_source_call_zeuge :
    taggedSourceBody "sample" =
      .ok (.block [.bind false "answer" none
        (.call "#tagged-AnyShape::Shape::area" [.fls, .variable "s", .tru])]
        (some (.ret (some (.variable "answer"))))) := rfl

/-- This also runs through the actual elaborator, beyond the expansion witness. -/
public theorem tagged_source_elaborated_zeuge :
    ((taggedSourceItems "bool").bind (fun items => elabU (pre108 items))).toOption.isSome = true := by
  decide +kernel

/-- A parsed implementation with the wrong result type is refused by name
    before any dispatcher is admitted. -/
public theorem tagged_source_signature_refused_zeuge :
    beqTopTief (taggedSourceExpanded "u8")
      (.error "spec.signature") = true := by
  decide +kernel

end Gabbro.Grammatik.Parser
