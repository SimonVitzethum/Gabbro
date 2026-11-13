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

namespace Gabbro.Stage0.ReturnCleanupWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def text : String :=
  "module cleanup_probe { lock L protects { } rank 0; impl fn main() -> u64 in 0 .. 100 effects { locks L } { locks L { return 23; } return 0; } }"

/-- A return from inside a lock scope elaborates to a scoped return and is lowered: the release of `L` runs at the
    return site (`retScopedC`), proved by the `locks` case of the statement simulation (`locks_okT_zurueck`). The
    kernel checks the emission itself. -/
theorem candidate_accepted : (emit text 256).toOption.isSome = true := by
  kernel_rfl

end Gabbro.Stage0.ReturnCleanupWitness
