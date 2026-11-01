/-
  File:      Grammatik/Parser/Elab/UebersetzeProben4.lean
  Subject:   Track P: witnesses and planted defects of `let` of a number (`UStmt.bind`, `Block.bind`,
             `Endblock.bind`): the binding carries the COMPUTED range of its value (as the exporter
             pushes it), the annotation is a check, the scope ends with the block, and a body read
             after a `let` sees the extended context. Sources are short on purpose (kernel memory).
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


namespace Gabbro.Grammatik.Parser.UebersetzeProben4

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- Operands widened first: the sum has room because `x` and `y` keep the range of `a` and `b`. -/
def widen_ok : String :=
  "module m { impl fn s(a : u32, b : u32) -> u64 { let x : u64 = a; let y : u64 = b; return x + y; } }"
theorem widen_ok_stufe : stufe widen_ok = "OK" := by decide +kernel

/-- A product bound in between. -/
def prod_ok : String :=
  "module m { impl fn p(a : u32, b : u32) -> u64 { let x : u64 = a; let y : u64 = b; let q : u64 = x * y; return q; } }"
theorem prod_ok_stufe : stufe prod_ok = "OK" := by decide +kernel

/-- The same sum into a `u32` result does not fit: the lowering refuses, the `let`s are no escape. -/
def widen_narrow : String :=
  "module m { impl fn s(a : u32, b : u32) -> u32 { let x : u64 = a; let y : u64 = b; return x + y; } }"
theorem widen_narrow_stufe : stufe widen_narrow = "lower: value outside range" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben4
