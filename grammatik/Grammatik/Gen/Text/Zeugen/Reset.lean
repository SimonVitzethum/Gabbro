/-
  File:      Grammatik/Gen/Text/Zeugen/Reset.lean
  Subject:   The two reset witnesses at the text level: their printed texts read back with their cells and verdicts.
             The static of an array type lies outside the proved print/read round trip, so the texts are lexed:
             the kernel runs the whole front end on them.
-/
module
public import Grammatik.Gen.Text.Pruefung
public import Grammatik.Gen.Zeugen.Reset
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

namespace Gabbro.Grammatik.Gen.Text.Zeugen.Reset

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Gen.Zeugen

namespace Good

/-- The source text of the accepted reset witness. -/
def text : String := textVon Reset.Good.z Reset.Good.P Reset.Good.ws

theorem gelesen : textGelesenB text Reset.Good.e.zellen Reset.Good.e.gueltig = true := by decide +kernel

theorem text_reads : ∃ e', ausText text = .ok e' ∧ e'.zellen = Reset.Good.e.zellen ∧
    e'.gueltig = Reset.Good.e.gueltig :=
  textGelesenB_sound _ _ _ gelesen

end Good

namespace Bad

/-- The source text of the refused reset witness. -/
def text : String := textVon Reset.Bad.z Reset.Bad.P Reset.Bad.ws

theorem gelesen : textGelesenB text Reset.Bad.e.zellen Reset.Bad.e.gueltig = true := by decide +kernel

theorem text_reads : ∃ e', ausText text = .ok e' ∧ e'.zellen = Reset.Bad.e.zellen ∧
    e'.gueltig = Reset.Bad.e.gueltig :=
  textGelesenB_sound _ _ _ gelesen

end Bad

end Gabbro.Grammatik.Gen.Text.Zeugen.Reset
