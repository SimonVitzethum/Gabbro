/-
  File:      Grammatik/Parser/Elab/UebersetzeProben6.lean
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


namespace Gabbro.Grammatik.Parser.UebersetzeProben6

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- A later `let` shadows an earlier name (and a parameter): the first name in the scope wins. -/
def shadow_ok : String :=
  "module m { impl fn s(a : u8) -> u16 { let a : u16 = a; let a : u16 = a; return a; } }"
theorem shadow_ok_stufe : stufe shadow_ok = "OK" := by decide +kernel

/-- An unbound name stays an elaboration error. -/
def unbound_refused : String :=
  "module m { impl fn s(a : u32) -> u32 { let x : u32 = a; return y; } }"
theorem unbound_refused_stufe : stufe unbound_refused = "elab: name unknown: y" := by decide +kernel

/-- WITNESS (was a planted defect until `let mut` got its G form, `Stmt.assignVar`): `let mut` with a type. -/
def mut_typed_ok : String :=
  "module m { impl fn s(a : u32) -> u32 { let mut x : u32 = a; return x; } }"
theorem mut_typed_ok_stufe : stufe mut_typed_ok = "OK" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben6
