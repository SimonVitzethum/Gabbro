/-
  File:      Grammatik/Parser/Elab/UebersetzeProben15.lean
  Subject:   Track P: integer forms of the model that the elaboration lacked, from source text. Division and
             remainder (`Expr.div`/`rem`, the signed `sdiv`/`srem`; a denominator that may be zero has no term),
             shifts (`Expr.shl`/`shr`), the unary minus (`Expr.neg`) and signed range types
             (`in -40 .. 40`). Table-free sources (kernel memory).
-/
import Grammatik.Parser.Elab.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben15

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- `a / b` with the denominator from `1`. -/
def div_ok : String :=
  "module m { impl fn f(a : u32 in 0 .. 100, b : u32 in 1 .. 10) -> u32 in 0 .. 100 { return a / b; } }"
theorem div_ok_stufe : stufe div_ok = "OK" := by decide +kernel

/-- A denominator that may be zero: `M102`, the model has no term. -/
def div_zero_refused : String :=
  "module m { impl fn f(a : u32 in 0 .. 100, b : u32 in 0 .. 10) -> u32 in 0 .. 100 { return a / b; } }"
theorem div_zero_refused_stufe :
    stufe div_zero_refused = "lower: division by a denominator that may be zero" := by decide +kernel

/-- The remainder is below the denominator: `0 .. 9`. -/
def rem_ok : String :=
  "module m { impl fn f(a : u32 in 0 .. 100, b : u32 in 1 .. 10) -> u32 in 0 .. 9 { return a % b; } }"
theorem rem_ok_stufe : stufe rem_ok = "OK" := by decide +kernel

/-- ... and not below a smaller bound. -/
def rem_range_refused : String :=
  "module m { impl fn f(a : u32 in 0 .. 100, b : u32 in 1 .. 10) -> u32 in 0 .. 8 { return a % b; } }"
theorem rem_range_refused_stufe : stufe rem_range_refused = "lower: value outside range" := by decide +kernel

/-- A signed numerator over a denominator that excludes zero: `Expr.sdiv`. -/
def sdiv_ok : String :=
  "module m { impl fn f(a : i32 in -50 .. 50, b : u32 in 1 .. 10) -> i32 in -50 .. 50 { return a / b; } }"
theorem sdiv_ok_stufe : stufe sdiv_ok = "OK" := by decide +kernel

/-- `a << b`: the result range is `hi(a) * 2 ^ hi(b)`. -/
def shl_ok : String :=
  "module m { impl fn f(a : u32 in 0 .. 100, b : u32 in 0 .. 3) -> u32 in 0 .. 800 { return a << b; } }"
theorem shl_ok_stufe : stufe shl_ok = "OK" := by decide +kernel

def shl_range_refused : String :=
  "module m { impl fn f(a : u32 in 0 .. 100, b : u32 in 0 .. 3) -> u32 in 0 .. 799 { return a << b; } }"
theorem shl_range_refused_stufe : stufe shl_range_refused = "lower: value outside range" := by decide +kernel

/-- `a >> b`. -/
def shr_ok : String :=
  "module m { impl fn f(a : u32 in 0 .. 100, b : u32 in 0 .. 3) -> u32 in 0 .. 100 { return a >> b; } }"
theorem shr_ok_stufe : stufe shr_ok = "OK" := by decide +kernel

/-- A signed range, and the minus. -/
def neg_ok : String :=
  "module m { impl fn f(a : i32 in -40 .. 40) -> i32 in -40 .. 40 { return -a; } }"
theorem neg_ok_stufe : stufe neg_ok = "OK" := by decide +kernel

def neg_asym_ok : String :=
  "module m { impl fn f(a : i32 in -40 .. 30) -> i32 in -40 .. 40 { return -a; } }"
theorem neg_asym_ok_stufe : stufe neg_asym_ok = "OK" := by decide +kernel

/-- Minus of a range that reaches below the result's bound. -/
def neg_below_refused : String :=
  "module m { impl fn f(a : i32 in -40 .. 40) -> i32 in -30 .. 40 { return -a; } }"
theorem neg_below_refused_stufe : stufe neg_below_refused = "lower: value outside range" := by
  decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben15
