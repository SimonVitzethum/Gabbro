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

namespace Gabbro.Stage0.OptionalAxiomVoidWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Optional void binding introduces no local and reaches an accepted image. -/
def text : String :=
  "module optional_void_probe { axiom ax() effects { pure } unfalsifiable \"probe\"; impl fn main() -> u8 { let x? = ax(); return 23; } }"

/-- The export gate refuses every axiom item: its proof duty has no checked source binding yet. -/
theorem candidate_refused :
    emit text 64 = .error
      "source export: SItemTief.axiomT: type/provider/proof duties lack a checked source binding" := by
  kernel_rfl


end Gabbro.Stage0.OptionalAxiomVoidWitness
