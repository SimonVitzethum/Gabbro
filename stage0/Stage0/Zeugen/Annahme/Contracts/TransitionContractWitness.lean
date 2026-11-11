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

namespace Gabbro.Stage0.TransitionContractWitness

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

def text : String :=
  "module transition_probe { table T count 2 { slot { s : u32 in 0 .. 2, } } state S { transition a { s : Idle -> Busy } requires true effects { writes T.slots } } impl fn main() -> u64 in 0 .. 100 effects { writes T.slots } { transition T.slots[0].s : Idle -> Busy; return 23; } }"

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_present : candidate.toOption.isSome = true := by kernel_rfl

def output : Emitted text 64 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 64 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

namespace Ordered

def text : String :=
  "module ordered_transition_probe { table T count 2 { slot { s : u32 in 0 .. 2, } } state S { transition cycle { T.slots[0].s : 0 -> 1, T.slots[1].s : 0 -> T.slots[0].s } requires true effects { writes T.slots } } impl fn main() -> u64 in 0 .. 100 effects { writes T.slots } { cycle(); return 23; } }"

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_present : candidate.toOption.isSome = true := by kernel_rfl

def output : Emitted text 64 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 64 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

end Ordered

end Gabbro.Stage0.TransitionContractWitness
