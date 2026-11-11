/-
  File:      Grammatik/Gen/Text/Zeugen/N47_P.lean
  Subject:   The witness `N47_P` at the text level. Its source text is the printed program with ONE change: the
             pointer is bound at a written pointer type without a contract (`let p0 : fn ( ) costs <= 1 ops = & fn0`).
             `fn0` conforms to that type (it ensures more), the pointer contract is empty, and the text reads back
             with the cells and the verdict of the witness. The round-trip theory does not cover a written pointer
             type, so this text IS lexed: the kernel runs the whole front end on it.
-/
module
public import Grammatik.Gen.Text.Pruefung
public import Grammatik.Gen.Zeugen.N.N47_P
import all Init.Data.Int.Repr
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


namespace Gabbro.Grammatik.Gen.Text.Zeugen.N47_P

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Gen.Zeugen.N47_P Gabbro.Grammatik.Parser

def mitTyp (ty : STyp) : SAnw → SAnw
  | .block ss ende => .block (ss.map fun
      | .bind m n none (.fnref f) => .bind m n (some ty) (.fnref f)
      | s => s) ende
  | s => s

def items (ty : STyp) : Except String (List SItemTief) :=
  (delab z P ws).map fun its => its.map fun
    | .modT n ms => .modT n (ms.map fun
        | .fnT sig body => .fnT sig (mitTyp ty body)
        | it => it)
    | it => it

/-- The written pointer type: no parameters, no contract. -/
def zeigerTyp : STyp := .raw "fn ( ) costs <= 1 ops"

/-- The source text of the witness. -/
def text : String :=
  match items zeigerTyp with
  | .ok its => renderText (druckItems its)
  | .error _ => ""

theorem gelesen : textGelesenB text e.zellen e.gueltig = true := by decide +kernel

/-- **The text of the witness reads back with its cells and its verdict.** -/
theorem text_reads : ∃ e', ausText text = .ok e' ∧ e'.zellen = e.zellen ∧ e'.gueltig = e.gueltig :=
  textGelesenB_sound _ _ _ gelesen

end Gabbro.Grammatik.Gen.Text.Zeugen.N47_P
