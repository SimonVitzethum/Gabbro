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


namespace Gabbro.Stage0.Pipeline.ProductRecordWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Labelled construction has two different fields. The update copies the second field
    into the first, and the result reads that changed first field. -/
def text : String :=
  "module product_record_probe { type Pair = { first : u8, second : u8, }; impl fn main() -> u8 { let mut pair : Pair = Pair(first: 7, second: 11); pair.first = pair.second; return pair.first; } }"

/-- The canonical parser accepts the labelled constructor, field read and field assignment. -/
theorem source_present : (Frontend.source text).toOption.isSome = true := by
  decide +kernel

/-- The scoped elaborator does not collect `uTypes`/`records`. Construction therefore
    reaches the ordinary value reader with an empty record schema scope. -/
theorem compilation_refused : compile text = .error "value without G form" := by
  decide +kernel

/-- No `prod`, `prodGet` or `prodSet` IR claim is made for this refused source. -/
theorem image_refused : emit text 64 = .error "value without G form" := by
  decide +kernel

end Gabbro.Stage0.Pipeline.ProductRecordWitness
