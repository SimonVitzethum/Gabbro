/-
  File:      Grammatik/Gen/Text/Zeugen/N47_45.lean
  Subject:   The witness `N47_45` at the text level: its printed text reads back as a program with its cells and its
             verdict. Decided by the kernel (the text is never lexed: `ausText_druckB`).
-/
module
public import Grammatik.Gen.Text.Pruefung
public import Grammatik.Gen.Zeugen.N.N47_45
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


namespace Gabbro.Grammatik.Gen.Text.Zeugen.N47_45

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Gen.Zeugen.N47_45

theorem check : textCheck z P ws e.zellen e.gueltig = true := by decide +kernel

/-- **The text of the witness reads back as the witness**, up to cells and verdict. -/
theorem text : ∃ e', ausText (textVon z P ws) = .ok e' ∧ e'.zellen = e.zellen ∧ e'.gueltig = e.gueltig :=
  textCheck_sound z P ws e.zellen e.gueltig check

end Gabbro.Grammatik.Gen.Text.Zeugen.N47_45
