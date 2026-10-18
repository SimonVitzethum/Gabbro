/-
  File:      Grammatik/Parser/Elab/UebersetzeProben5.lean
  Subject:   Track P: witnesses and planted defects of `let` of a number (`UStmt.bind`, `Block.bind`,
             `Endblock.bind`): the binding carries the COMPUTED range of its value (as the exporter
             pushes it), the annotation is a check, the scope ends with the block, and a body read
             after a `let` sees the extended context. Sources are short on purpose (kernel memory).
-/
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben5

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- The annotation is a check: a `u32` value does not fit `u8`. -/
def annot_refused : String :=
  "module m { impl fn s(a : u32) -> u32 { let x : u8 = a; return x; } }"
theorem annot_refused_stufe : stufe annot_refused = "lower: let: value outside the annotated range" := by
  decide +kernel

/-- No annotation: the binding is the value's own range. -/
def plain_let : String :=
  "module m { impl fn s(a : u32) -> u64 { let x = a; return x; } }"
theorem plain_let_stufe : stufe plain_let = "OK" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben5
