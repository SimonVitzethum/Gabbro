/-
  File:      Grammatik/Parser/Elab/UebersetzeProben10.lean
  Subject:   Wall 3: `bool` probes (split from `UebersetzeProben`: the kernel probes of one file share one memory budget).
-/
import Grammatik.Parser.Elab.Proben.UebersetzeProben

namespace Gabbro.Grammatik.Parser.UebersetzeProben10

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben (stufe)

set_option maxRecDepth 100000

/-! ## Wall 3: `bool` -- slots, results, truth values in the body, `by ops` -/

/-- WITNESS (`beispiele/16`, `15`, shortened): a `bool` slot written with a literal through a pointer and
    read back as the result. -/
def bool1 : String :=
  "module m { table T count 2 { slot { b : bool, } } impl fn set(t : ptr<normal, rw> T, i : index into T) effects { writes t.slots } { t.slots[i].b = true; } impl fn get(t : ptr<normal, r> T, i : index into T) -> bool effects { reads t.slots } { return t.slots[i].b; } }"
theorem bool1_ok : stufe bool1 = "OK" := by decide +kernel

/-- WITNESS (`beispiele/62`, shortened): a `bool` result computed from a comparison. -/
def bool2 : String :=
  "module m { impl fn le(x : u32 in 0 .. 9) -> bool { return x <= 5; } }"
theorem bool2_ok : stufe bool2 = "OK" := by decide +kernel

/-- WITNESS: `&&`, `||`, `!` and the literals over comparisons. -/
def bool3 : String :=
  "module m { impl fn f(x : u32 in 0 .. 9, y : u32 in 0 .. 9) -> bool { return x <= 5 && !(y == 3) || false; } }"
theorem bool3_ok : stufe bool3 = "OK" := by decide +kernel

/-- WITNESS: `by ops` is a writer discipline the CHECKER holds; the model reads the field as written. -/
def byops1 : String :=
  "module m { table T count 2 { slot { n : u32 in 0 .. 9 by ops, } } impl fn get(t : ptr<normal, r> T, i : index into T) -> u32 effects { reads t.slots } { return t.slots[i].n; } }"
theorem byops1_ok : stufe byops1 = "OK" := by decide +kernel

/-- PLANTED DEFECT: a NUMBER stored into a bool field. -/
def bool_zahl : String :=
  "module m { table T count 2 { slot { b : bool, } } impl fn set(t : ptr<normal, rw> T, i : index into T) effects { writes t.slots } { t.slots[i].b = 1; } }"
theorem bool_zahl_refused : stufe bool_zahl = "elab: ensures clause without G form" := by decide +kernel

/-- PLANTED DEFECT: a bool field read as a NUMBER. -/
def bool_als_zahl : String :=
  "module m { table T count 2 { slot { b : bool, } } impl fn get(t : ptr<normal, r> T, i : index into T) -> u32 effects { reads t.slots } { return t.slots[i].b; } }"
theorem bool_als_zahl_refused : stufe bool_als_zahl = "elab: bool field as a number" := by decide +kernel

/-- PLANTED DEFECT: a truth value stored into a NUMBER field. -/
def zahl_wahr : String :=
  "module m { table T count 2 { slot { n : u32 in 0 .. 9, } } impl fn set(t : ptr<normal, rw> T, i : index into T) effects { writes t.slots } { t.slots[i].n = true; } }"
theorem zahl_wahr_refused : stufe zahl_wahr = "elab: value without G form" := by decide +kernel

/-- PLANTED DEFECT: a number returned where the result is `bool`, and a comparison returned where the
    result is a number. -/
def bool_res_zahl : String :=
  "module m { impl fn f(x : u32 in 0 .. 9) -> bool { return x; } }"
theorem bool_res_zahl_refused : stufe bool_res_zahl = "elab: number as a truth value" := by decide +kernel

def zahl_res_bool : String :=
  "module m { impl fn f(x : u32 in 0 .. 9) -> u32 { return x <= 5; } }"
theorem zahl_res_bool_refused : stufe zahl_res_bool = "elab: value without G form" := by decide +kernel


end Gabbro.Grammatik.Parser.UebersetzeProben10
