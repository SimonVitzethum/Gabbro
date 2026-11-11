module
public import Stage0.Compiler
import Grammatik.Kern.Taktik.KernelRfl
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

namespace Gabbro.Stage0.Frontend.MeasureWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

def characters : List Char :=
  ("type Small = u8 in 0 .. 1; ".toList ++
   "impl fn countdown(n : Small) decreases n ".toList ++
   "{ if n > 0 { countdown(0); } else { } return; } ".toList ++
   "impl fn main() { countdown(1); return; }".toList)

def text : String := String.ofList characters

theorem compiled : (compile text).toOption.isSome = true := by kernel_rfl

def result : Compiled text := (compile text).toOption.get compiled

/-- The actual frontend and generic compiler carry the exact source measure through restoration. -/
theorem compile_source_program_zeuge :
    compile text = .ok result ∧ CanonicalSourceProgram result ∧
    Measures.lowerMeasures result.unit = .ok result.measures.val ∧
    Measures.cycleLengths result.unit result.program result.measures.val.mass = true :=
  ⟨except_ok_get compiled, compile_source_program text result,
    result.measures.property, result.measureLengths⟩

/-- The recursive function has the source singleton, while the entry without a clause stays empty. -/
theorem exact_measures_zeuge :
    result.unit.fns.map (·.decreases) = [some (.variable "n"), none] := by kernel_rfl

end Gabbro.Stage0.Frontend.MeasureWitness
