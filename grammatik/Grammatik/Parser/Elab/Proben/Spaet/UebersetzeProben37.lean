/-
  File:      Grammatik/Parser/Elab/Proben/Spaet/UebersetzeProben37.lean
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


namespace Gabbro.Grammatik.Parser.UebersetzeProben37

open Gabbro.Grammatik Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- A reason as parameter, result and bound value. -/
def grund_typ : String :=
  "module m { reason R { A = 1 \"a\", B = 2 \"b\" exhaustive } impl fn g(r : R) { } impl fn h() -> R { return R::B; } impl fn f() { g(R::A); let x = h(); g(x); } }"
theorem grund_typ_stufe : stufe grund_typ = "OK" := by decide +kernel

/-- A reason parameter returned. -/
def grund_durch : String :=
  "module m { reason R { A = 1 \"a\", B = 2 \"b\" exhaustive } impl fn h(r : R) -> R { return r; } }"
theorem grund_durch_stufe : stufe grund_durch = "OK" := by decide +kernel

/-- Negative twin: a case of another reason. -/
def grund_fremd : String :=
  "module m { reason R { A = 1 \"a\", B = 2 \"b\" exhaustive } reason S { X = 1 \"x\" exhaustive } impl fn g(r : R) { } impl fn f() { g(S::X); } }"
theorem grund_fremd_stufe : stufe grund_fremd = "elab: argument of a foreign reason" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben37
