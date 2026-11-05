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

namespace Gabbro.Stage0.ProfileMismatchWitness

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

def text : String :=
  "module profile_mismatch_probe { profile { arch x86_64; arch aarch64; }; impl fn main() -> u64 in 0 .. 100 { return 23; } }"

def candidate : Except String (Emitted text 64) := emit text 64

/-- Conflicting profile modes are refused by name: the checked binding is
    inconsistent, so no image is built for it. -/
theorem candidate_refused :
    (match candidate with | .error message => some message | .ok _ => none) =
      some "ir: profile binding refused: modes, assumptions or library requirements are not consistent" := by decide +kernel

end Gabbro.Stage0.ProfileMismatchWitness
