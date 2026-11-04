/-
  File:      Grammatik/Parser/Elab/UebersetzeProben18.lean
  Subject:   Track P: `narrow x to lo .. hi else { .. }` (`Block.narrow`, the `else` branch an `Endblock` that
             must not fall through; the rest of the block reads `x` at the narrowed range); at the top level of a body
             `Endblock.narrow`. Also `let x = A exchange update(v) { e } …` (`Block.exchange`/`Endblock.exchange`) and
             a terminal `if`/`else` whose arms both end (`Endblock.ite`): the end-block forms of THEOREM-MAP 102.
-/
module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3
public import Grammatik.Parser.Cover.Mitglieder
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

/-- Source text reaches `Block.floatNarrow` in a continuing branch. The fallback
    returns from the function; the success path reads the shadowed float local. -/
def float_narrow_finite : String :=
  "module m { impl fn f(x : f64, c : bool) -> u8 { if c { narrow x to finite else { return 0; } let y = x; } return 1; } }"

theorem float_narrow_finite_zeuge : stufe float_narrow_finite = "OK" := by
  decide +kernel

/-- A fallthrough handler is refused before either integer or float G narrowing. -/
theorem float_narrow_falls_refused_zeuge :
    stufe "module m { impl fn f(x : f64, c : bool) -> u8 { if c { narrow x to finite else { } } return 1; } }" =
      "elab: narrow else falls through" := by
  decide +kernel

/-- Check the actual G constructor after lexing, parsing and both elaboration
    stages, rather than just observing that the source was accepted. -/
private def reachesFloatOf (source : String) : Bool :=
  (do
    let tokens ← (lex source).toOption
    let items ← (parseTopTief tokens).toOption
    let unit ← (elabU (pre108 items)).toOption
    let (program, functions) ← (lowerAllg unit).toOption
    pure ((Cover.Mitglieder.mitglieder unit program functions).contains "Block.floatOf")).getD false

/-- The conversion reads a computed integer local, preserves the declared result
    range, and leaves a usable float local in a continuing branch. -/
def float_of_computed : String :=
  "module m { impl fn f(a : u8 in 0 .. 9, c : bool) -> u8 { if c { let n = a + 1; let y : f64 in 0 .. 10 = f64(n); let z = y; } return 1; } }"

theorem float_of_computed_zeuge : reachesFloatOf float_of_computed = true := by
  decide +kernel

theorem float_of_f32_computed_zeuge :
    reachesFloatOf "module m { impl fn f(a : u8 in 0 .. 9, c : bool) -> u8 { if c { let n = a + 1; let y : f32 in 0 .. 10 = f32(n); let z = y; } return 1; } }" = true := by
  decide +kernel

/-- Float annotations retain exact rational endpoints, including fractions. -/
theorem float_of_rational_target_zeuge :
    uTyp [] [] (.range (.atom "f64") (.float "0.5") (.float "10.5") false) =
      .ok (.fl (5, 10) (105, 10)) := rfl

/-- A float argument fails the integer-operand premise at the dependent exporter. -/
theorem float_of_noninteger_refused_zeuge :
    stufe "module m { impl fn f(a : f64, c : bool) -> u8 { if c { let y : f64 = f64(a); } return 1; } }" =
      "lower: floatOf: operand is not an integer" := by
  decide +kernel

/-- A float introduction in the final part of a function reaches the end-block
    constructor and its bound local is returned directly. -/
def float_of_end : String :=
  "module m { impl fn f(n : u8) -> f64 { let y = f64(n); return y; } }"

private def reachesEndFloatOf (source : String) : Bool :=
  (do
    let tokens ← (lex source).toOption
    let items ← (parseTopTief tokens).toOption
    let unit ← (elabU (pre108 items)).toOption
    let (program, functions) ← (lowerAllg unit).toOption
    pure ((Cover.Mitglieder.mitglieder unit program functions).contains "Endblock.floatOf")).getD false

theorem float_of_end_zeuge : reachesEndFloatOf float_of_end = true := by
  decide +kernel

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

/-- The compare form: the new value where `old(Z)` meets the predicate (`Expr.wenn`), the binder the success. -/
def tausch_cas_ok : String :=
  "module m { atomic Z : u32 in 0 .. 100 relaxed; impl fn f() -> bool effects { reads Z, writes Z } { let ok = Z exchange 7 when old(Z) == 0 returns erfolg publishes nothing; return ok; } }"
theorem tausch_cas_ok_stufe : stufe tausch_cas_ok = "OK" := by decide +kernel

/-- The new value of the compare form is checked against the static's range. -/
def tausch_cas_range_refused : String :=
  "module m { atomic Z : u32 in 0 .. 100 relaxed; impl fn f() -> bool effects { reads Z, writes Z } { let ok = Z exchange 700 when old(Z) == 0 returns erfolg publishes nothing; return ok; } }"
theorem tausch_cas_range_refused_stufe : stufe tausch_cas_range_refused = "lower: value outside range" := by decide +kernel

/-- An `update` body with `if`: each arm reads the binder narrowed by its guard (`Expr.eng`), so `v + 1` under
    `v < 100` fits `0 .. 100`. -/
def tausch_wenn_ok : String :=
  "module m { atomic Z : u32 in 0 .. 100 relaxed; impl fn f() -> u32 in 0 .. 100 effects { reads Z, writes Z } { let alt = Z exchange update(v) bounded 8 ops on_exceeded k { if v < 100 { return v + 1; } else { return v; } } publishes nothing; return alt; } }"
theorem tausch_wenn_ok_stufe : stufe tausch_wenn_ok = "OK" := by decide +kernel

/-- An `else if` chain: the later arms read the binder under the negated guards before them. -/
def tausch_kette_ok : String :=
  "module m { atomic Z : u32 in 0 .. 100 relaxed; impl fn f() -> u32 in 0 .. 100 effects { reads Z, writes Z } { let alt = Z exchange update(v) { if v >= 100 { return v; } else if v > 50 { return v + 1; } else { return v + 2; } } publishes nothing; return alt; } }"
theorem tausch_kette_ok_stufe : stufe tausch_kette_ok = "OK" := by decide +kernel

/-- A guard too weak for the arm is refused: `v < 101` leaves `v + 1` at `101`. -/
def tausch_wenn_refused : String :=
  "module m { atomic Z : u32 in 0 .. 100 relaxed; impl fn f() -> u32 in 0 .. 100 effects { reads Z, writes Z } { let alt = Z exchange update(v) { if v < 101 { return v + 1; } return v; } publishes nothing; return alt; } }"
theorem tausch_wenn_refused_stufe : stufe tausch_wenn_refused = "lower: value outside range" := by decide +kernel

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

/-- The guard may compare with a side of known range: `v < k` for `k : 0 .. 51` gives `v ≤ 50`. -/
def tausch_param_ok : String :=
  "module m { atomic Z : u32 in 0 .. 100 relaxed; impl fn f(k : u32 in 0 .. 51) -> u32 in 0 .. 100 effects { reads Z, writes Z } { let alt = Z exchange update(v) { if v < k { return v + 50; } return v; } publishes nothing; return alt; } }"
theorem tausch_param_ok_stufe : stufe tausch_param_ok = "OK" := by decide +kernel

/-- With `k : 0 .. 52` the arm may reach `101`. -/
def tausch_param_refused : String :=
  "module m { atomic Z : u32 in 0 .. 100 relaxed; impl fn f(k : u32 in 0 .. 52) -> u32 in 0 .. 100 effects { reads Z, writes Z } { let alt = Z exchange update(v) { if v < k { return v + 50; } return v; } publishes nothing; return alt; } }"
theorem tausch_param_refused_stufe : stufe tausch_param_refused = "lower: value outside range" := by decide +kernel

/-! ## A body ending on every path without a trailing return -/

/-- A nested terminal `if`. -/
def ende_verschachtelt_ok : String :=
  "module m { impl fn f(c : bool, d : bool) -> u32 in 0 .. 5 { if c { if d { return 1; } else { return 4; } } else { return 2; } } }"
theorem ende_verschachtelt_ok_stufe : stufe ende_verschachtelt_ok = "OK" := by decide +kernel

/-- A terminal `match` over an option static. -/
def ende_match_ok : String :=
  "module m { table T count 4 { slot { x : u32 in 0 .. 9, } } static mut O : option index into T = None; impl fn f() -> option index into T effects { reads O } { match O { None => { return None; } Some(i) => { return Some(i); } } } }"
theorem ende_match_ok_stufe : stufe ende_match_ok = "OK" := by decide +kernel

/-- An arm that falls through still falls off the function. -/
def ende_match_refused : String :=
  "module m { table T count 4 { slot { x : u32 in 0 .. 9, } } static mut O : option index into T = None; impl fn f() -> option index into T effects { reads O } { match O { None => { return None; } Some(i) => { } } } }"
theorem ende_match_refused_stufe : stufe ende_match_refused = "elab: fn with a result falls off" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben18
