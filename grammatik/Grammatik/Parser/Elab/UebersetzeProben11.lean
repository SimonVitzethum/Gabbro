/-
  File:      Grammatik/Parser/Elab/UebersetzeProben11.lean
  Subject:   Walls 4 and 5: `own`/`~p` and constants (split from `UebersetzeProben`: the kernel probes of one file share one memory budget).
-/
import Grammatik.Parser.Elab.UebersetzeProben

namespace Gabbro.Grammatik.Parser.UebersetzeProben11

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben (stufe)

set_option maxRecDepth 100000

/-! ## Wall 4: `own` pointers and the complement `~p` over the declared storage width -/

/-- WITNESS (`beispiele/15`, shortened): an `own` pointer is a read-write pointer in the model (the
    exporter reads it the same way; ownership is the checker's business). -/
def own1 : String :=
  "module m { table T count 2 { slot { b : bool, } } impl fn u(r : ptr<normal, own> T, i : index into T) -> bool effects { reads r.slots, writes r.slots } { r.slots[i].b = true; return r.slots[i].b; } }"
theorem own1_ok : stufe own1 = "OK" := by decide +kernel

/-- WITNESS (`beispiele/62`, `61`): `~p` is `p ^ (2^w - 1)` over the parameter's declared storage width. -/
def bnot1 : String :=
  "module m { impl fn f(m : u8) -> u8 { return ~m; } impl fn g(w : u8) -> bool { return (w ^ u8::max) == ~w; } }"
theorem bnot1_ok : stufe bnot1 = "OK" := by decide +kernel

/-- WITNESS: the width is the DECLARED word's, not the range's: `u8 in 0 .. 15` is stored in 8 bits, so
    its complement is `255 - x` (`beispiele/61`, `hohes_nibble`), and `u16 in 0 .. 255` in 16. -/
def bnot_schmal : String :=
  "module m { impl fn f(x : u8 in 0 .. 15) -> u8 { return ~x; } impl fn k(w : u16 in 0 .. 255) -> u16 { return ~w; } }"
theorem bnot_schmal_ok : stufe bnot_schmal = "OK" := by decide +kernel

/-- PLANTED DEFECT: the complement of an EXPRESSION has no known width here -- it is refused, not
    guessed from a range (a range would give `15 - x` for `0 .. 15`, where the C says `255 - x`). -/
def bnot_ausdruck : String :=
  "module m { impl fn f(x : u32) -> u32 { return ~(x + 1); } }"
theorem bnot_ausdruck_refused : stufe bnot_ausdruck = "elab: value without G form" := by decide +kernel

/-- PLANTED DEFECT: the complement of a signed parameter (its width has no unsigned reading). -/
def bnot_vorzeichen : String :=
  "module m { impl fn f(x : i32) -> i32 { return ~x; } }"
theorem bnot_vorzeichen_refused :
    stufe bnot_vorzeichen = "elab: complement of unknown width" := by decide +kernel

/-! ## Wall 5: compile-time constants -- expressions and `const fn` calls -/

/-- WITNESS (`beispiele/93`, shortened): a constant computed from earlier constants with `+ - * ^ >>`. -/
def konst_ausdruck : String :=
  "module m { const A : u32 = 6 * 7; const B : u32 = A + 2 * (A ^ 3) - (A >> 1); impl fn f() -> u32 { return B; } }"
theorem konst_ausdruck_ok : stufe konst_ausdruck = "OK" := by decide +kernel

/-- WITNESS: a constant computed by a `const fn` call (arguments checked against the parameter's range). -/
def konst_fn : String :=
  "module m { const fn doppelt(n : u32 in 0 .. 1000) -> u32 in 0 .. 2000 { return n + n; } const C : u32 = doppelt(21); impl fn f() -> u32 { return C; } }"
theorem konst_fn_ok : stufe konst_fn = "OK" := by decide +kernel

/-- PLANTED DEFECT: an intermediate value outside the declared type (`200 + 100` in a `u8`): the emitted C
    would wrap, the exact value would not -- the constant is UNKNOWN, so its use is refused. -/
def konst_ueberlauf : String :=
  "module m { const X : u8 = 200 + 100; impl fn f() -> u8 { return X; } }"
theorem konst_ueberlauf_refused : stufe konst_ueberlauf = "elab: name unknown: X" := by decide +kernel

/-- PLANTED DEFECT: a negative intermediate in an unsigned constant. -/
def konst_negativ : String :=
  "module m { const Y : u32 = 3 - 5; impl fn f() -> u32 { return Y; } }"
theorem konst_negativ_refused : stufe konst_negativ = "elab: name unknown: Y" := by decide +kernel

/-- PLANTED DEFECT: an argument outside the `const fn` parameter's range. -/
def konst_argument : String :=
  "module m { const fn doppelt(n : u32 in 0 .. 1000) -> u32 in 0 .. 2000 { return n + n; } const C : u32 = doppelt(2000); impl fn f() -> u32 { return C; } }"
theorem konst_argument_refused : stufe konst_argument = "elab: name unknown: C" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben11
