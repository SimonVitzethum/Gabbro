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


namespace Gabbro.Stage0.Pipeline.AdapterReasonWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The adapter keeps the fallible source signature; main handles the propagated reason.
    Both the adapter's call and the explicit `?` binding contribute to the returned value. -/
def text : String :=
  "module adapter_reason_probe { reason R { Empty = 1 \"empty\" exhaustive } impl fn original(x : u8) -> u8 or R { if x == 0 { return R::Empty; } return x; } impl fn adapted(..) -> u8 or R from original; impl fn propagate(x : u8) -> u8 or R { let y = adapted(x) ?; return y; } impl fn main() -> u8 { let answer = propagate(0) else (e) { match e { Empty => { return 23; } } return 0; } return answer; } }"

/-- Lexing, parsing, profile selection and source-scope collection all succeed. -/
theorem source_present : (Frontend.source text).toOption.isSome = true := by
  decide +kernel

/-- The actual compiler's scoped elaborator does not run `entzuckere` before `uRestFehler`. -/
theorem compilation_refused : compile text = .error "item without G form" := by
  decide +kernel

/-- The real image endpoint preserves that elaboration refusal. -/
theorem image_refused : emit text 64 = .error "item without G form" := by
  decide +kernel

/-- Isolate `?` from the earlier adapter refusal, retaining a live reason return and handler. -/
def propagationText : String :=
  "module reason_propagation_probe { reason R { Empty = 1 \"empty\" exhaustive } impl fn original(x : u8) -> u8 or R { if x == 0 { return R::Empty; } return x; } impl fn propagate(x : u8) -> u8 or R { let y = original(x) ?; return y; } impl fn main() -> u8 { let answer = propagate(0) else (e) { match e { Empty => { return 23; } } return 0; } return answer; } }"

/-- The same scoped elaborator reaches the unexpanded query statement when no adapter precedes it. -/
theorem propagation_compilation_refused :
    compile propagationText = .error "stmt without G form: let query" := by
  decide +kernel

theorem propagation_image_refused :
    emit propagationText 64 = .error "stmt without G form: let query" := by
  decide +kernel

end Gabbro.Stage0.Pipeline.AdapterReasonWitness
