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

namespace Gabbro.Stage0.ConstControlWitness

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

def text : String :=
  "module const_probe { const fn choose(n : u64 in 0 .. 9) -> u64 in 0 .. 9 requires n > 0 { if n > 1 { return 3; } else { return 1; } } const K : u64 = choose(2); impl fn main() -> u64 in 0 .. 9 { return K; } }"

def candidate : Except String (Emitted text 64) := emit text 64

/-- The runtime exporter omits const bodies; certified substitution of all call sites is still missing. -/
theorem candidate_refused :
    emit text 64 = .error "source export: const function requires certified call-site substitution before runtime export: choose" := by decide +kernel

end Gabbro.Stage0.ConstControlWitness
