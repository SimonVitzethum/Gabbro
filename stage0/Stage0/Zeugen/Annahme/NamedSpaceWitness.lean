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

namespace Gabbro.Stage0.NamedSpaceWitness

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

def text : String :=
  "module named_space_probe { table T count 2 owner sharedData { slot { v : u32 in 0 .. 100, } } impl fn main() -> u32 in 0 .. 100 effects { reads T.slots } { return T.slots[0].v; } }"

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_present : candidate.toOption.isSome = true := by decide +kernel

def output : Emitted text 64 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 64 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

def pointerText : String :=
  "module named_space_pointer_probe { table T count 2 owner sharedData { slot { v : u32 in 0 .. 100, } } impl fn main(p : ptr<sharedData, r> T) -> u32 in 0 .. 100 effects { reads p.slots } { return p.slots[0].v; } }"

def pointerCandidate : Except String (Emitted pointerText 64) := emit pointerText 64

theorem pointer_candidate_present : pointerCandidate.toOption.isSome = true := by decide +kernel

def pointerOutput : Emitted pointerText 64 :=
  pointerCandidate.toOption.get pointer_candidate_present

theorem pointer_accepted_image : emit pointerText 64 = .ok pointerOutput :=
  Gabbro.Grammatik.except_ok_get pointer_candidate_present

end Gabbro.Stage0.NamedSpaceWitness
