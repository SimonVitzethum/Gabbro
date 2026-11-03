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

end Gabbro.Grammatik.Parser.SourceFolds
