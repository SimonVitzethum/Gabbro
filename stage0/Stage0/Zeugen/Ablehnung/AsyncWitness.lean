module

public import Stage0.Frontend.Source

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

namespace Gabbro.Stage0.Frontend

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual source entry point still refuses async, including a child
    await. Recognition cannot silently expose a synchronous substitute. -/
public theorem source_async_refused_zeuge :
    (source "async fn work() -> u64 { let x: u64 = child_task().await; return x; }").map
      (fun _ => ()) =
      .error "async lowering: typed reachable-state representation and G/GX segment simulation are not implemented" := by
  decide +kernel

/-- A malformed async declaration remains a syntax error, not a success
    manufactured by stripping the async keyword. -/
public theorem source_malformed_async_refused_zeuge :
    (source "async fn work() -> u64;").toOption.isSome = false := by
  decide +kernel

public theorem source_nested_async_refused_zeuge :
    (source "module tasks { pub async fn work() -> u64 { return child_task().await; } }").map
      (fun _ => ()) =
      .error "async lowering: typed reachable-state representation and G/GX segment simulation are not implemented" := by
  decide +kernel

end Gabbro.Stage0.Frontend
