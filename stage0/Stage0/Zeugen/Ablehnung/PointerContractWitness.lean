module
public import Stage0.SourceWitness
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

namespace Gabbro.Stage0.PointerContractWitness

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

def text : String :=
  "module pointer_probe { impl fn identity(a : u64 in 0 .. 9) -> u64 in 0 .. 9 requires a > 0 ensures result == a { return a; } impl fn main() -> u64 in 0 .. 9 { let p : fn(a : u64 in 0 .. 9) -> u64 in 0 .. 9 requires a > 0 ensures result == a effects { } costs <= 8 ops = &identity; let value = p(3); return value; } }"

/-- A written function-pointer type with a contract and a cost passes the export gate; its cost is
    checked. Here the function behind it declares no cost, so the unit is refused. -/
theorem candidate_refused :
    emit text 64 = .error
      "declared costs do not hold: a pointer type declares a cost and admits a function without a declared cost within it" := by
  kernel_rfl


end Gabbro.Stage0.PointerContractWitness
