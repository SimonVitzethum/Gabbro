/-
  File:      Grammatik/Parser/Elab/UebersetzeProben18.lean
  Subject:   Track P: `narrow x to lo .. hi else { .. }` (`Block.narrow`, the `else` branch an `Endblock` that
             must not fall through; the rest of the block reads `x` at the narrowed range). In a nested block
             only: a body is an `Endblock`, which has no `narrow` former (recorded as a model gap).
-/
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben18

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- A narrowing in a nested block; the result range is the narrowed one. -/
def narrow_ok : String :=
  "module m { impl fn f(a : u32 in 0 .. 9, c : bool) -> u32 in 0 .. 5 { if c { narrow a to 0 .. 5 else { return 0; } return a; } return 1; } }"
theorem narrow_ok_stufe : stufe narrow_ok = "OK" := by decide +kernel

/-- The rest of the block reads the NARROWED range: returning the value against a smaller result range is refused. -/
def narrow_range_refused : String :=
  "module m { impl fn f(a : u32 in 0 .. 9, c : bool) -> u32 in 0 .. 4 { if c { narrow a to 0 .. 5 else { return 0; } return a; } return 1; } }"
theorem narrow_range_refused_stufe : stufe narrow_range_refused = "lower: value outside range" := by decide +kernel

/-- An `else` that falls through is no narrowing. -/
def narrow_falls_refused : String :=
  "module m { impl fn f(a : u32 in 0 .. 9, c : bool) -> u32 in 0 .. 5 { if c { narrow a to 0 .. 5 else { } return a; } return 1; } }"
theorem narrow_falls_refused_stufe : stufe narrow_falls_refused = "elab: narrow else falls through" := by decide +kernel

/-- A type word names the range (`u8`), and `..<` excludes the upper bound. -/
def narrow_word_ok : String :=
  "module m { impl fn f(a : u32 in 0 .. 999, c : bool) -> u32 in 0 .. 255 { if c { narrow a to u8 else { return 0; } return a; } return 1; } }"
theorem narrow_word_ok_stufe : stufe narrow_word_ok = "OK" := by decide +kernel

def narrow_excl_ok : String :=
  "module m { impl fn f(a : u32 in 0 .. 99, c : bool) -> u32 in 0 .. 63 { if c { narrow a to 0 ..< 64 else { return 0; } return a; } return 1; } }"
theorem narrow_excl_ok_stufe : stufe narrow_excl_ok = "OK" := by decide +kernel

/-- At the top level of a body the model has no former: recorded, not worked around. -/
def narrow_top_refused : String :=
  "module m { impl fn f(a : u32 in 0 .. 9) -> u32 in 0 .. 5 { narrow a to 0 .. 5 else { return 0; } return a; } }"
theorem narrow_top_refused_stufe : stufe narrow_top_refused = "lower: lower: a narrow at the top level of a body has no G form (Endblock lacks narrow)" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben18
