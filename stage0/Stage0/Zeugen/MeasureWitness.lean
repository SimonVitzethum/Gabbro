module
public import Stage0.SourceWitness
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

namespace Gabbro.Stage0.MeasureWitness

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

def text : String :=
  "module measure_probe { type Small = u8 in 0 .. 1; impl fn countdown(n : Small) decreases n { if n > 0 { countdown(0); } else { } return; } impl fn main() -> u64 in 0 .. 100 { countdown(1); return 23; } }"

def candidate : Except String (Emitted text 64) := emit text 64

/-- The export gate refuses the unbound decreases proof duty. -/
theorem candidate_refused :
    emit text 64 = .error "source export: function type/proof/header duties lack a checked source binding: countdown" := by decide +kernel

end Gabbro.Stage0.MeasureWitness
