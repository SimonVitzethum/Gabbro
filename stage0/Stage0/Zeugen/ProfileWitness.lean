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

namespace Gabbro.Stage0.ProfileWitness

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

def text : String :=
  "module profile_probe { profile { arch x86_64; }; impl fn main() -> u64 in 0 .. 100 { return 23; } }"

def candidate : Except String (Emitted text 64) := emit text 64

/-- Profile binding exists in `Parser.Profil`, but Stage0 has no certificate transport
    from that binding to the selected image and its named hardware assumptions. -/
theorem candidate_refused : candidate.toOption.isSome = false := by decide +kernel

end Gabbro.Stage0.ProfileWitness
