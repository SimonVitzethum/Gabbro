module

public import Grammatik.Parser.SourceFolds.Range

@[expose] public section
namespace Gabbro.Grammatik.Parser.SourceFolds

/-- The parser shape is recognized as a range fold node. -/
theorem matchFoldNode_add_zeuge :
    matchFoldNode (.ext .foldAdd ["i", "range"]
      [.lit 0, .lit 2, .tru, .variable "x"]) =
      some (.foldAdd, "i", [.lit 0, .lit 2, .tru, .variable "x"]) := rfl

theorem isRangeFold_add_zeuge :
    isRangeFold (.ext .foldAdd ["i", "range"]
      [.lit 0, .lit 2, .tru, .variable "x"]) = true := rfl

theorem isRangeFold_plain_zeuge : isRangeFold (.variable "x") = false := rfl

/-- Bound tests vanish for the trivial `0 ..< length` range. -/
theorem boundTests_trivial_zeuge :
    boundTests (.lit 0) (.lit 2) (.lit 2) "i" = [] ∧
    effFilter (boundTests (.lit 0) (.lit 2) (.lit 2) "i") .tru = .tru := ⟨rfl, rfl⟩

/-- A nonzero lower bound and a short upper bound become filter tests. -/
theorem boundTests_general_zeuge :
    boundTests (.lit 2) (.lit 3) (.lit 4) "i" =
      [.bin "<=" (.lit 2) (.variable "i"), .bin "<" (.variable "i") (.lit 3)] ∧
    effFilter (boundTests (.lit 2) (.lit 3) (.lit 4) "i") .tru =
      .bin "&&" (.bin "<=" (.lit 2) (.variable "i")) (.bin "<" (.variable "i") (.lit 3)) := by
  exact ⟨rfl, rfl⟩

theorem foldInit_add_zeuge : foldInit .foldAdd none = .lit 0 := rfl

theorem foldInit_and_zeuge : foldInit .foldAnd none = .tru := rfl

theorem reservedNames_one_zeuge :
    reservedNames 1 =
      ["$rangeFold$acc$0", "$rangeFold$value$0", "$rangeFold$result$0"] := rfl

theorem tagFoldNodes_single_zeuge :
    (tagFoldNodes (.ext .foldAdd ["i", "range"]
      [.lit 0, .lit 2, .tru, .variable "x"]) 0).1 =
      [((.ext .foldAdd ["i", "range"]
        [.lit 0, .lit 2, .tru, .variable "x"]), 0)] := rfl

theorem boundArgs_fold_zeuge :
    boundArgs (.ext .foldAdd ["i", "range"]
      [.lit 0, .lit 2, .tru, .variable "x"]) =
      some (.lit 0, .lit 2) := rfl

theorem boundArgs_plain_zeuge : boundArgs (.variable "x") = none := rfl

/-- A non-indexed value has no indexed array. -/
theorem parseFoldNode_no_array_zeuge :
    parseFoldNode [] [] (some (.atom "u16")) []
      (.ext .foldAdd ["i", "range"] [.lit 0, .lit 2, .tru, .variable "x"]) =
      .error "fold range: indexed array required" := rfl

private def tableSource : List SItemTief :=
  [.tableT "T" none (some (.lit 2)) none none false
    [.tSlot [⟨"v", .atom "u8", none, none, none, false, false⟩]]]

private def rowProjection : SExpr :=
  .field (.index (.variable "T") (.variable "k")) "v"

/-- A fold over a table reads row projections and accumulates in `u64`. -/
theorem parseFoldNode_table_zeuge :
    parseFoldNode tableSource [] none []
      (.ext .foldAdd ["k", "range"] [.lit 0, .lit 2, .tru, rowProjection]) =
      .ok ⟨.foldAdd, "k", .lit 0, .lit 2, .tru, rowProjection,
        none, .atom "u64", "T", .lit 2, true⟩ := rfl

private def nestedRowFold : SExpr :=
  .ext .foldAdd ["i", "range"]
    [.lit 0, .lit 2, .tru,
      .bin "+" (.index (.variable "xs") (.variable "i"))
        (.ext .foldAdd ["k", "range"] [.lit 0, .lit 2, .tru, rowProjection])]

/-- An inner fold over table rows nests inside an outer fold over an array:
    the inner loop traverses the table domain, the outer loop the array. -/
theorem returnFold_nested_row_zeuge :
    returnFold tableSource [("xs", .array (.atom "u8") (.lit 2))]
      (some (.atom "u16")) (.ret (some nestedRowFold)) =
    .ok (.block
      [.bind true "$rangeFold$acc$0" (some (.atom "u16")) (.lit 0),
       .each "i" none "elems" (.variable "xs") "unvisited" "" none
         (.block
           [.bind true "$rangeFold$acc$1" (some (.atom "u64")) (.lit 0),
            .each "k" none "slots" (.variable "T") "unvisited" "" none
              (.block
                [.bind false "$rangeFold$value$1" none rowProjection,
                 .set (.variable "$rangeFold$acc$1") "+="
                   (.variable "$rangeFold$value$1")] none),
            .bind false "$rangeFold$result$1" none (.variable "$rangeFold$acc$1"),
            .bind false "$rangeFold$value$0" none
              (.bin "+" (.index (.variable "xs") (.variable "i"))
                (.variable "$rangeFold$result$1")),
            .set (.variable "$rangeFold$acc$0") "+="
              (.variable "$rangeFold$value$0")] none)]
      (some (.ret (some (.variable "$rangeFold$acc$0"))))) := rfl

end Gabbro.Grammatik.Parser.SourceFolds
