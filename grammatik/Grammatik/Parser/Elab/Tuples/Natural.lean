module
import all Init.Data.String.Search
import all Init.Data.String.Slice
import Init.Data.String.Lemmas.Iterate
@[expose] public section

namespace Gabbro.Grammatik.Parser.Tuples

/-- The standard decimal parser over a structural character list. Slice iteration reaches
    `WellFounded.extrinsicFix`, whose classical well-foundedness test blocks kernel reduction,
    even when an ordinary field such as `slots` is rejected at its first character. Keep the
    standard digit separator rules: underscores occur only singly, between digits. -/
def natural? (text : String) : Option Nat :=
  let chars := text.toList
  let isNat := Id.run do
    let mut lastWasDigit := false
    for c in chars do
      if c = '_' then
        if !lastWasDigit then
          return false
        lastWasDigit := false
      else if c.isDigit then
        lastWasDigit := true
      else
        return false
    return lastWasDigit
  if isNat then
    some <| chars.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0
  else
    none

/-- Changing the iteration representation preserves every accepted and refused spelling,
    including empty strings, leading zeros, separators and non-ASCII characters. -/
theorem natural?_eq_toNat? (text : String) : natural? text = text.toNat? := by
  unfold natural? String.toNat? String.Slice.toNat? String.Slice.isNat
  simp only [String.Slice.forIn_eq_forIn_toList, String.Slice.foldl_eq_foldl_toList,
    String.copy_toSlice]

end Gabbro.Grammatik.Parser.Tuples
