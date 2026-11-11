module
public import Stage0.IRBild
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


namespace Gabbro.Stage0.Pipeline.TaggedDispatchWitness
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Both closed cases have distinct payload types and implementations. Main dispatches
    both values and makes its numeric answer depend on both Boolean results. -/
def text : String :=
  "module tagged_dispatch_probe { spec Select[T] { fn choose(value : T) -> bool effects {} costs <= 8 ops; } impl Select[u8] { fn choose(value : u8) -> bool effects {} costs <= 3 ops { return value == 7; } } impl Select[bool] { fn choose(value : bool) -> bool effects {} costs <= 3 ops { return value; } } tagged type Choice = { Number(u8), Truth(bool) } by Select; impl fn main() -> u8 { let left : Choice = Number(7); let a = Select::choose(left); let right : Choice = Truth(false); let b = Select::choose(right); if a && !b { return 23; } return 0; } }"

/-- A spec function must declare its cost, and the export gate refuses every declared cost of
    a spec group: no checked binding carries it to the generated dispatcher. The closed
    dispatch therefore stops at source loading, before its dispatcher is generated. -/
theorem source_refused : Frontend.source text = .error
    "source export: SItemTief.specGroupT: type/provider/proof duties lack a checked source binding" := by
  kernel_rfl

/-- This is a source-to-image refusal, not an isolated declaration-expansion probe. -/
theorem compilation_refused : (compile text).toOption.isNone = true ∧
    emit text 256 = .error
      "source export: SItemTief.specGroupT: type/provider/proof duties lack a checked source binding" :=
  ⟨by kernel_rfl, by kernel_rfl⟩

end Gabbro.Stage0.Pipeline.TaggedDispatchWitness
