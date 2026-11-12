/- Witnesses of the spec-argument check (`uSpecArgs`, `uSpecArgument`): each claim is decided by the kernel. -/
module
public import Grammatik.Parser.Elab.Uebersetze.Folds.SpecArguments
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

namespace Gabbro.Grammatik.Parser.Uebersetze

set_option maxRecDepth 100000

def argumentContext : UCtx :=
  { names := ["value"], kinds := [.int], types := [.int 0 9], tabs := [], locks := [],
    held := [], res := none, fname := "fixture", alias := [], lits := [],
    specs := [("small", ["x"], .tru), ("outer", [], .call "small" [.lit 101])],
    specTypen := [("small", [.range (.atom "u32") (.lit 0) (.lit 100) false]),
      ("outer", [])] }

/-- Even a helper that ignores its parameter checks the caller's complete declared range. -/
theorem spec_argument_range_zeuge :
    uSpecArgs 20 argumentContext (.call "small" [.variable "value"]) = .ok () ∧
    uSpecArgs 20 {argumentContext with types := [.int 0 101]}
      (.call "small" [.variable "value"]) =
      .error "spec small: argument 1 does not fit its parameter type" ∧
    uSpecArgs 20 argumentContext (.call "outer" []) =
      .error "spec small: argument 1 does not fit its parameter type" := by
  decide +kernel

/-- Boolean arguments use the Boolean reader; aggregates and missing arguments refuse. -/
theorem spec_argument_types_zeuge :
    uSpecArgument argumentContext "flag" 1 (.atom "bool") .tru = .ok () ∧
    uSpecArgument argumentContext "flag" 1 (.atom "bool") (.lit 1) =
      .error "spec flag: argument 1 does not fit its parameter type" ∧
    uSpecArgument argumentContext "array" 1 (.array (.atom "u32") (.lit 1)) (.lit 1) =
      .error "spec array: argument 1 does not fit its parameter type" ∧
    uSpecArgs 20 argumentContext (.call "small" []) =
      .error "spec small: argument 1 does not fit its parameter type" := by
  decide +kernel

/-- A narrowing conversion cannot manufacture a parameter interval for an ignored argument. -/
theorem spec_argument_conversion_zeuge :
    uSpecArgument argumentContext "small" 1 (.atom "u32") (.call "u8" [.lit 1000]) =
      .error "spec small: argument 1 does not fit its parameter type" ∧
    uSpecArgument argumentContext "small" 1 (.atom "u32") (.call "u8" [.lit 7]) = .ok () := by
  decide +kernel

end Gabbro.Grammatik.Parser.Uebersetze
