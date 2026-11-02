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

namespace Gabbro.Stage0.CapacityRequiredWitness

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

/-- A required allocation: the success path of the `else` form, with `stopC 107`
    on capacity exhaustion (the Stage-0 shape of `narrowRequired`, which
    `Block.arenaAllocRequired` unfolds to). A full arena is `Logik.kapazitaet`,
    excluded by the caller's `KoerperGutS/SA` duty; the static arena commits
    all its slots. -/
def text : String :=
  "module capacity_probe { arena A capacity 1 .. 2 of u32; impl fn main() -> u64 in 0 .. 100 effects { writes A } { let i = alloc A (0); return 23; } }"

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_present : candidate.toOption.isSome = true := by decide +kernel

def output : Emitted text 64 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 64 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

end Gabbro.Stage0.CapacityRequiredWitness
