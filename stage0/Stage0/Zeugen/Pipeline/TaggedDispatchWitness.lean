module
public import Stage0.IRBild
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

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Both closed cases have distinct payload types and implementations. Main dispatches
    both values and makes its numeric answer depend on both Boolean results. -/
def text : String :=
  "module tagged_dispatch_probe { spec Select[T] { fn choose(value : T) -> bool effects {}; } impl Select[u8] { fn choose(value : u8) -> bool effects {} { return value == 7; } } impl Select[bool] { fn choose(value : bool) -> bool effects {} { return value; } } tagged type Choice = { Number(u8), Truth(bool) } by Select; impl fn main() -> u8 { let left : Choice = Number(7); let a = Select::choose(left); let right : Choice = Truth(false); let b = Select::choose(right); if a && !b { return 23; } return 0; } }"

/-- The actual source frontend retains the parsed closed-dispatch declarations. -/
theorem source_present : (Frontend.source text).toOption.isSome = true := by
  decide +kernel

/-- Scoped Stage-0 elaboration calls item admission before `exportDeclarationUnit`.
    Consequently the spec group is refused before its dispatcher can be generated. -/
theorem compilation_refused : compile text = .error "item without G form" := by
  decide +kernel

/-- This is a source-to-image refusal, not an isolated declaration-expansion probe. -/
theorem image_refused : emit text 64 = .error "item without G form" := by
  decide +kernel

end Gabbro.Stage0.Pipeline.TaggedDispatchWitness
