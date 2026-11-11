/-
  File:      Grammatik/Gen/Text/Zeugen/N47_20.lean
  Subject:   The witness `N47_20` at the text level. OPEN FINDING: its printed text does not read back as the
             witness; the program read back is accepted, the model program is refused. Decided by the kernel.
-/
module
public import Grammatik.Gen.Text.Pruefung
public import Grammatik.Gen.Zeugen.N.N47_20
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


namespace Gabbro.Grammatik.Gen.Text.Zeugen.N47_20

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Gen.Zeugen.N47_20

/-- **FINDING (open): the text of this witness does not read back as the witness.** The model
    program is refused (`Zeugen.N47_20.e_gueltig`): function 0 carries the planted contract
    `requires g0` and function 1 calls it through `&fn0`. Its printed text elaborates and lowers,
    and the program read back is ACCEPTED, with other cells. The round trip therefore loses the
    fault; which side is wrong is not settled. The other nineteen text witnesses read back. -/
theorem check_fails : textCheck z P ws e.zellen e.gueltig = false := by decide +kernel

/-- The program read back from the text is accepted, the model program is not. -/
theorem verdict_differs :
    (match delab z P ws with
    | .error _ => false
    | .ok its => match ausItems its with
      | .error _ => false
      | .ok e' => e'.gueltig) = true ∧ e.gueltig = false := by
  constructor <;> decide +kernel

end Gabbro.Grammatik.Gen.Text.Zeugen.N47_20
