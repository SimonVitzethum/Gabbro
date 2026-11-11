module
public import Stage0.SourceWitness
import Grammatik.Kern.Taktik.KernelRfl
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

namespace Gabbro.Stage0.AccWitness

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

def text : String :=
  "module acc_probe { accumulates c : u32 merge add per cpu 2; impl fn main() -> u64 in 0 .. 100 { return 23; } }"

/-- Stage 0 does not lower the generated accumulator update yet: the unit elaborates and is accepted, the IR lowering refuses the update function.
    The evaluated diagnostic is "ir: the function c#aktualisiere uses a form outside the IR fragment"; the kernel
    checks the refusal itself. -/
theorem candidate_refused : (emit text 64).toOption.isSome = false := by
  kernel_rfl

end Gabbro.Stage0.AccWitness
