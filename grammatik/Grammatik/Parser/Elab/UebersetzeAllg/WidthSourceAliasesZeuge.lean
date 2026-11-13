module

public import Grammatik.Parser.Elab.UebersetzeAllg.WidthSourcesZeuge
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

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg.WidthSources
open Gabbro.Grammatik.Parser.Uebersetze

attribute [local cbv_eval] strEq_decide

/- Keep the resolver's input folded. Only the outer collection and the small lookup
   premises inspect its constructors; no proof evaluates a complete width search. -/
@[irreducible] def sourceAliases : List SItemTief :=
  [.typeT [] "Word" [] [] (some (.atom "u32")),
   .typeT [] "Next" [] [] (some (.atom "Word")),
   .typeT [] "Small" [] [] (some (.range (.atom "Next") (.lit 0) (.lit 15) false))]

private theorem sourceAliases_eq : sourceAliases =
    [.typeT [] "Word" [] [] (some (.atom "u32")),
     .typeT [] "Next" [] [] (some (.atom "Word")),
     .typeT [] "Small" [] [] (some (.range (.atom "Next") (.lit 0) (.lit 15) false))] := by
  unfold sourceAliases
  rfl

private theorem sourceAliases_reverse : sourceAliases.reverse =
    [.typeT [] "Small" [] [] (some (.range (.atom "Next") (.lit 0) (.lit 15) false)),
     .typeT [] "Next" [] [] (some (.atom "Word")),
     .typeT [] "Word" [] [] (some (.atom "u32"))] := by
  rewrite [sourceAliases_eq]
  rfl

private theorem sourceAliases_length : sourceAliases.length = 3 := by
  rewrite [sourceAliases_eq]
  rfl

private theorem word_next : strEq "Word" "Next" = false := by decide
private theorem next_word : strEq "Next" "Word" = false := by decide
private theorem small_word : strEq "Small" "Word" = false := by decide
private theorem small_next : strEq "Small" "Next" = false := by decide
private theorem word_bits : "Word" ++ "#bits" = "Word#bits" := rfl
private theorem next_bits : "Next" ++ "#bits" = "Next#bits" := rfl
private theorem small_bits : "Small" ++ "#bits" = "Small#bits" := rfl

private theorem source_word : sourceAliases.find? (uTypeDeclNamed "Word") =
    some (.typeT [] "Word" [] [] (some (.atom "u32"))) := by
  simp only [sourceAliases_eq, List.find?_cons, uTypeDeclNamed, strEq_self]

private theorem source_next : sourceAliases.find? (uTypeDeclNamed "Next") =
    some (.typeT [] "Next" [] [] (some (.atom "Word"))) := by
  simp only [sourceAliases_eq, List.find?_cons, uTypeDeclNamed, word_next, strEq_self]

private theorem reverse_word : sourceAliases.reverse.find? (uTypeDeclNamed "Word") =
    some (.typeT [] "Word" [] [] (some (.atom "u32"))) := by
  simp only [sourceAliases_reverse, List.find?_cons, uTypeDeclNamed, small_word, next_word, strEq_self]

private theorem reverse_next : sourceAliases.reverse.find? (uTypeDeclNamed "Next") =
    some (.typeT [] "Next" [] [] (some (.atom "Word"))) := by
  simp only [sourceAliases_reverse, List.find?_cons, uTypeDeclNamed, small_next, strEq_self]

private theorem builtin_width (items : List SItemTief) (fuel : Nat) :
    uAliasWordWidth items (fuel + 1) "u32" = 32 := by
  simp only [uAliasWordWidth, show uAtomBreite "u32" = 32 from by cbv,
    show 0 < (32 : Nat) from by decide, ↓reduceIte]

private theorem chain_widths (items : List SItemTief)
    (word : items.find? (uTypeDeclNamed "Word") =
      some (.typeT [] "Word" [] [] (some (.atom "u32"))))
    (next : items.find? (uTypeDeclNamed "Next") =
      some (.typeT [] "Next" [] [] (some (.atom "Word")))) :
    uAliasWordWidth items 4 "Word" = 32 ∧ uAliasWordWidth items 4 "Next" = 32 := by
  have wordWidth (fuel : Nat) : uAliasWordWidth items (fuel + 2) "Word" = 32 := by
    rw [alias_chain_width items (fuel + 1) "Word" "u32" [] [] [] (.atom "u32")
      (by cbv) word rfl]
    exact builtin_width items fuel
  refine ⟨wordWidth 2, ?_⟩
  rw [alias_chain_width items 3 "Next" "Word" [] [] [] (.atom "Word") (by cbv) next rfl]
  exact wordWidth 1

/-- A real source declaration satisfies the collector law at its exact fuel bound. -/
theorem alias_source_collected_zeuge :
    ("Word#bits", ((32 : Int), (32 : Int))) ∈ uAliasBreiten sourceAliases := by
  apply alias_source_collected sourceAliases "Word" "u32" [] [] [] (.atom "u32") 32
  · rw [sourceAliases_eq]
    exact List.mem_cons_self
  · rfl
  · rw [sourceAliases_length]
    exact builtin_width sourceAliases 3
  · decide

theorem source_alias_widths : uAliasBreiten sourceAliases =
    [("Word#bits", (32, 32)), ("Next#bits", (32, 32)), ("Small#bits", (32, 32))] := by
  obtain ⟨word, next⟩ := chain_widths sourceAliases source_word source_next
  rw [uAliasBreiten]
  conv => lhs; arg 2; rw [sourceAliases_eq]
  simp only [List.filterMap_cons, List.filterMap_nil, uStorageName, sourceAliases_length,
    builtin_width, word, next, show 0 < (32 : Nat) from by decide, Int.natCast_pos, ↓reduceIte,
    word_bits, next_bits, small_bits]
  rfl

private theorem reverse_widths : uAliasBreiten sourceAliases.reverse =
    [("Small#bits", (32, 32)), ("Next#bits", (32, 32)), ("Word#bits", (32, 32))] := by
  obtain ⟨word, next⟩ := chain_widths sourceAliases.reverse reverse_word reverse_next
  rw [uAliasBreiten]
  conv => lhs; arg 2; rw [sourceAliases_reverse]
  simp only [List.filterMap_cons, List.filterMap_nil, uStorageName, List.length_reverse,
    sourceAliases_length, builtin_width, word, next, show 0 < (32 : Nat) from by decide, Int.natCast_pos,
    ↓reduceIte, word_bits, next_bits, small_bits]
  rfl

theorem source_alias_chain_zeuge :
    uAliasBreiten sourceAliases =
      [("Word#bits", (32, 32)), ("Next#bits", (32, 32)), ("Small#bits", (32, 32))] ∧
    uAliasBreiten sourceAliases.reverse =
      [("Small#bits", (32, 32)), ("Next#bits", (32, 32)), ("Word#bits", (32, 32))] ∧
    uAliasBreiten [.typeT [] "Cycle" [] [] (some (.atom "Cycle"))] = [] ∧
    uAliasBreiten [.typeT [] "Unknown" [] [] (some (.atom "Missing"))] = [] := by
  refine ⟨source_alias_widths, reverse_widths, ?_, ?_⟩
  · have cycle (fuel : Nat) :
        uAliasWordWidth [.typeT [] "Cycle" [] [] (some (.atom "Cycle"))] fuel "Cycle" = 0 := by
      induction fuel with
      | zero => rfl
      | succ fuel ih =>
        rw [alias_chain_width _ fuel "Cycle" "Cycle" [] [] [] (.atom "Cycle") (by cbv)
          (by simp only [List.find?_cons, uTypeDeclNamed, strEq_self]) rfl]
        exact ih
    simp only [uAliasBreiten, List.filterMap_cons, List.filterMap_nil, uStorageName, cycle,
      Nat.lt_irrefl, Int.natCast_pos, Int.lt_irrefl, ↓reduceIte]
  · have missing (fuel : Nat) :
        uAliasWordWidth [.typeT [] "Unknown" [] [] (some (.atom "Missing"))]
          (fuel + 1) "Missing" = 0 := by
      simp only [uAliasWordWidth, show uAtomBreite "Missing" = 0 from by cbv,
        Nat.lt_irrefl, ↓reduceIte, List.find?_cons, List.find?_nil, uTypeDeclNamed,
        show strEq "Unknown" "Missing" = false from by decide]
    simp only [uAliasBreiten, List.filterMap_cons, List.filterMap_nil, uStorageName, missing,
      Nat.lt_irrefl, Int.natCast_pos, Int.lt_irrefl, ↓reduceIte]

/-- Internal syntax permits arbitrary strings even though source identifiers exclude `#`.
    A scalar at the metadata spelling must keep its value in the range environment. -/
@[irreducible] def sourceRangeItems : List SItemTief :=
  [.typeT [] "Word" [] [] (some (.atom "u32")),
   .constT "Word#bits" (.atom "u8") (.one (.lit 7))]

theorem source_range_widths : uAliasBreiten sourceRangeItems = [("Word#bits", (32, 32))] := by
  rw [uAliasBreiten]
  conv => lhs; arg 2; unfold sourceRangeItems
  have length : sourceRangeItems.length = 2 := by unfold sourceRangeItems; rfl
  simp only [List.filterMap_cons, List.filterMap_nil, uStorageName, length, builtin_width,
    show 0 < (32 : Nat) from by decide, Int.natCast_pos, ↓reduceIte, word_bits]
  rfl

end Gabbro.Grammatik.Parser.UebersetzeAllg.WidthSources
