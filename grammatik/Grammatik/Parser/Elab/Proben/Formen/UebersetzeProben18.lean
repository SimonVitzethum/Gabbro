/-
  File:      Grammatik/Parser/Elab/UebersetzeProben18.lean
  Subject:   Track P: `narrow x to lo .. hi else { .. }` (`Block.narrow`, the `else` branch an `Endblock` that
             must not fall through; the rest of the block reads `x` at the narrowed range); at the top level of a body
             `Endblock.narrow`. Also `let x = A exchange update(v) { e } …` (`Block.exchange`/`Endblock.exchange`) and
             a terminal `if`/`else` whose arms both end (`Endblock.ite`): the end-block forms of THEOREM-MAP 102.
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

/-- At the top level of a body: `Endblock.narrow` (THEOREM-MAP 102). -/
def narrow_top_ok : String :=
  "module m { impl fn f(a : u32 in 0 .. 9) -> u32 in 0 .. 5 { narrow a to 0 .. 5 else { return 0; } return a; } }"
theorem narrow_top_ok_stufe : stufe narrow_top_ok = "OK" := by decide +kernel

/-- The rest of the body reads the NARROWED range there too. -/
def narrow_top_range_refused : String :=
  "module m { impl fn f(a : u32 in 0 .. 9) -> u32 in 0 .. 4 { narrow a to 0 .. 5 else { return 0; } return a; } }"
theorem narrow_top_range_refused_stufe : stufe narrow_top_range_refused = "lower: value outside range" := by decide +kernel

/-! ## `exchange update` -/

/-- The update form at the top level of a body; the binder is the old value, `bounded`/`on_exceeded` belong to
    the lowering. -/
def tausch_ok : String :=
  "module m { static Z : u32 in 0 .. 100 = 0; impl fn f() -> u32 in 0 .. 100 effects { reads Z, writes Z } { let alt = Z exchange update(v) bounded 4 ops on_exceeded k { v / 2 }; return alt; } }"
theorem tausch_ok_stufe : stufe tausch_ok = "OK" := by decide +kernel

/-- In a nested block, with `publishes nothing`. -/
def tausch_block_ok : String :=
  "module m { static Z : u32 in 0 .. 100 = 0; impl fn f(c : bool) -> u32 in 0 .. 100 effects { reads Z, writes Z } { if c { let alt = Z exchange update(v) { return v / 2; } publishes nothing; return alt; } return 0; } }"
theorem tausch_block_ok_stufe : stufe tausch_block_ok = "OK" := by decide +kernel

/-- The new value must stay in the static's range (an overflow in the update is refused). -/
def tausch_range_refused : String :=
  "module m { static Z : u32 in 0 .. 100 = 0; impl fn f() -> u32 in 0 .. 100 effects { reads Z, writes Z } { let alt = Z exchange update(v) { return v + 1; } publishes nothing; return alt; } }"
theorem tausch_range_refused_stufe : stufe tausch_range_refused = "lower: value outside range" := by decide +kernel

/-- Without `writes Z` there is no exchange. -/
def tausch_writes_refused : String :=
  "module m { static Z : u32 in 0 .. 100 = 0; impl fn f() -> u32 in 0 .. 100 effects { reads Z } { let alt = Z exchange update(v) { return v / 2; } publishes nothing; return alt; } }"
theorem tausch_writes_refused_stufe : stufe tausch_writes_refused = "lower: exchange of a static the function does not write" := by decide +kernel

/-- A binder type other than the static's is refused, not dropped. -/
def tausch_typ_refused : String :=
  "module m { static Z : u32 in 0 .. 100 = 0; impl fn f() -> u32 in 0 .. 100 effects { reads Z, writes Z } { let alt : u32 = Z exchange update(v) { return v / 2; } publishes nothing; return alt; } }"
theorem tausch_typ_refused_stufe : stufe tausch_typ_refused = "elab: exchange binder typed other than its static" := by decide +kernel

/-- The compare form (`… when … returns …`) has no G form yet. -/
def tausch_cas_refused : String :=
  "module m { static Z : u32 in 0 .. 100 = 0; impl fn f() -> bool effects { reads Z, writes Z } { let ok = Z exchange 1 when old(Z) == 0 returns erfolg publishes nothing; return ok; } }"
theorem tausch_cas_refused_stufe : stufe tausch_cas_refused = "elab: exchange compare form without G form" := by decide +kernel

/-! ## A terminal `if`/`else` -/

/-- Both arms return: no trailing return is needed. -/
def ite_ende_ok : String :=
  "module m { impl fn f(c : bool) -> u32 in 0 .. 5 { if c { return 1; } else { return 2; } } }"
theorem ite_ende_ok_stufe : stufe ite_ende_ok = "OK" := by decide +kernel

/-- An `else if` chain. -/
def ite_kette_ok : String :=
  "module m { impl fn f(c : bool, d : bool) -> u32 in 0 .. 5 { if c { return 1; } else if d { return 2; } else { return 3; } } }"
theorem ite_kette_ok_stufe : stufe ite_kette_ok = "OK" := by decide +kernel

/-- An arm that falls through still falls off the function. -/
def ite_faellt_refused : String :=
  "module m { impl fn f(c : bool) -> u32 in 0 .. 5 { if c { return 1; } else { } } }"
theorem ite_faellt_refused_stufe : stufe ite_faellt_refused = "elab: fn with a result falls off" := by decide +kernel

/-- Each arm's value is checked against the result range. -/
def ite_range_refused : String :=
  "module m { impl fn f(c : bool) -> u32 in 0 .. 1 { if c { return 1; } else { return 2; } } }"
theorem ite_range_refused_stufe : stufe ite_range_refused = "lower: value outside range" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben18
