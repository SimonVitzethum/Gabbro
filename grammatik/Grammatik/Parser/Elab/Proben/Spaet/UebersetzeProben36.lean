/-
  File:      Grammatik/Parser/Elab/Proben/Spaet/UebersetzeProben36.lean
  Subject:   Track P, every model form readable (Simon, 2026-10-21; the language follows the model):
             * an index of a table of the SAME count is an index into the table (the model's `Ty.index` is the
               count): accepted; of a table of another count: refused.
             * `result` of a `bool` function in its `ensures` (`Expr.var` of the head of `ErgCtx`): read as a truth
               value, and the parameters beside it shift by one; `result` of a number as a truth value: refused.
             * reason types `R` as parameters and results (`Ty.why n`): a case `R::C` or a variable passed, returned,
               bound from a call; a case of another reason: refused.
             * `-3` is the literal `-3` (`USide.lit (-3)`), `-(3)` the negation of `3` (`USide.neg`): one tree each.
-/
module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3
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


namespace Gabbro.Grammatik.Parser.UebersetzeProben36

open Gabbro.Grammatik Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- The binder of `traverse` over `T` indexes `U` of the same count. -/
def idx_gleich : String :=
  "module m { table T count 2 { slot { v : bool, } } table U count 2 { slot { w : bool, } } impl fn f() effects { writes U.slots } { traverse k over slots of T by unvisited { U.slots[k].w = true; } } }"
theorem idx_gleich_stufe : stufe idx_gleich = "OK" := by decide +kernel

/-- Negative twin: `U` has another count. -/
def idx_fremd : String :=
  "module m { table T count 2 { slot { v : bool, } } table U count 3 { slot { w : bool, } } impl fn f() effects { writes U.slots } { traverse k over slots of T by unvisited { U.slots[k].w = true; } } }"
theorem idx_fremd_stufe : stufe idx_fremd = "elab: index of foreign table" := by decide +kernel

/-- A `bool` result in its `ensures`. -/
def erg_bool : String :=
  "module m { impl fn f(c : bool) -> bool ensures result || !c { return true; } }"
theorem erg_bool_stufe : stufe erg_bool = "OK" := by decide +kernel

/-- A parameter beside a `bool` result (the result rides first in the `ensures` context). -/
def erg_bool_param : String :=
  "module m { impl fn f(c : u32 in 0 .. 3) -> bool ensures result || c == 2 { return true; } }"
theorem erg_bool_param_stufe : stufe erg_bool_param = "OK" := by decide +kernel

/-- Negative twin: a number result read as a truth value. -/
def erg_zahl_als_bool : String :=
  "module m { impl fn f(c : bool) -> u32 in 0 .. 3 ensures result { return 1; } }"
theorem erg_zahl_als_bool_stufe : stufe erg_zahl_als_bool = "elab: ensures clause without G form" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben36
