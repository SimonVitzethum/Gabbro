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

namespace Gabbro.Stage0.PointerContractWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

def text : String :=
  "module pointer_probe { impl fn identity(a : u64 in 0 .. 9) -> u64 in 0 .. 9 requires a > 0 ensures result == a { return a; } impl fn main() -> u64 in 0 .. 9 { let p : fn(a : u64 in 0 .. 9) -> u64 in 0 .. 9 requires a > 0 ensures result == a effects { } costs <= 8 ops = &identity; let value = p(3); return value; } }"

/-- The concrete function reference passes local selection; the checked contract
    control fragment still refuses before the later cost gate. -/
theorem candidate_refused :
    emit text 64 = .error
      "unsupported invariant constructor: contract end block is outside the checked control fragment" := by
  kernel_rfl

/-- Run the original cost checker independently on the actual scoped, lowered
    and restored source; its negative cost coverage must not disappear. -/
def pointerCostVerdict : Except String (Bool × Option String) := do
  let parsed ← Frontend.source text {}
  let declarations := pre108 parsed.prepared.elaborierbar
  let unit ← (Frontend.elabWithScopes declarations
    parsed.scopes.values parsed.scopes.types parsed.scopes.functions
    (Frontend.tableWithEmpty parsed.scopes.values parsed.scopes.types)
    (widths := parsed.scopes.widths)).bind (Profil.selectUnit {})
  let (raw, _) ← lowerAllg unit
  let program ← OldSource.restore declarations unit raw
  let costs := CostBinding.declared (uMembers declarations)
  return (CostBinding.holds costs unit program irDurchlaeufe,
    CostBinding.failing costs unit program irDurchlaeufe)

/-- The original written pointer budget still refuses an admitted function with no cost. -/
theorem pointer_cost_refused_zeuge : pointerCostVerdict = .ok
    (false, some "a pointer type declares a cost and admits a function without a declared cost within it") := by
  kernel_rfl

end Gabbro.Stage0.PointerContractWitness
