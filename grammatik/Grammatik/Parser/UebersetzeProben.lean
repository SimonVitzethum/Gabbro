/-
  File:      Grammatik/Parser/UebersetzeProben.lean
  Subject:   Sieve (a), parser lane: witnesses and planted defects for the widenings of the
             elaborator and the generic lowering.

  Every probe runs the WHOLE pipeline `uebersetzeAllg` on a small source text and names the stage
  where it stops (`stufe`). A WITNESS is a source that reaches `OK`; a PLANTED DEFECT is a source
  one token away that must stop, at the stage and with the message the widening promises. A
  widening whose defect also passes would be a widening that let something through.

  The texts are short on purpose: the kernel decodes a `String` per proof (O13); the proofs are `decide +kernel`, because plain `decide`
  (elaborator `whnf` first) needed ~9.5 GB for ONE probe (measured 2026-09-30) and `+kernel` 1 GB / 2 s; corpus
  programs are pinned as characters in the chain instances, not here.

  WALL 1 (2026-09-30): units WITHOUT a table; integer arithmetic (`+`, `-`, `*`) in values, with
  the range of the result computed like `Expr.add`/`sub`/`mul` carry it; the built-in widths
  `uN`/`iN`; an omitted `effects` (derived by the checker) read as the empty set.
-/
import Grammatik.Schlusssatz

namespace Gabbro.Grammatik.Parser.UebersetzeProben

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

/-- The stage of `uebersetzeAllg` that stops a source (`OK` when none does). -/
def stufe (s : String) : String :=
  match lex s with
  | .error _ => "lex"
  | .ok toks =>
    match parseTopTief toks with
    | .error e => "parse: " ++ e
    | .ok items =>
      match elabU (pre108 items) with
      | .error e => "elab: " ++ e
      | .ok u =>
        match lowerAllg u with
        | .error e => "lower: " ++ e
        | .ok _ => "OK"

/-! ## Wall 1a: a unit with no table, arithmetic in a return -/

/-- WITNESS (`beispiele/130`, shortened): sum of two bounded parameters, result range wide enough. -/
def add1 : String :=
  "module m { impl fn add(a : u32 in 0 .. 1000, b : u32 in 0 .. 1000) -> u32 in 0 .. 2000 { return a + b; } }"
theorem add1_ok : stufe add1 = "OK" := by decide +kernel

/-- PLANTED DEFECT: the same body against a result range one short of the sum's range (0 .. 1998).
    The lowering must refuse it, not widen silently. -/
def add1_eng : String :=
  "module m { impl fn add(a : u32 in 0 .. 1000, b : u32 in 0 .. 1000) -> u32 in 0 .. 1999 { return a + b; } }"
theorem add1_eng_refused : stufe add1_eng = "lower: value outside range" := by decide +kernel

/-- WITNESS: subtraction takes the range `lo1 - hi2 .. hi1 - lo2`, so `a - b` of two `0 .. 10`
    parameters fits `i8` (`-10 .. 10`) and the built-in width name resolves. -/
def sub1 : String :=
  "module m { impl fn d(a : u32 in 0 .. 10, b : u32 in 0 .. 10) -> i8 { return a - b; } }"
theorem sub1_ok : stufe sub1 = "OK" := by decide +kernel

/-- PLANTED DEFECT: the same difference into an UNSIGNED result. The lower end is `-10`. -/
def sub1_vorz : String :=
  "module m { impl fn d(a : u32 in 0 .. 10, b : u32 in 0 .. 10) -> u8 { return a - b; } }"
theorem sub1_vorz_refused : stufe sub1_vorz = "lower: value outside range" := by decide +kernel

/-- WITNESS: a product, and a nested sum of it (`3 * a + b`). -/
def mul1 : String :=
  "module m { impl fn f(a : u32 in 0 .. 5, b : u32 in 0 .. 5) -> u8 in 0 .. 20 { return 3 * a + b; } }"
theorem mul1_ok : stufe mul1 = "OK" := by decide +kernel

/-- PLANTED DEFECT: division is not in the fragment; it must stop where it stopped before. -/
def div1 : String :=
  "module m { impl fn f(a : u32 in 0 .. 5, b : u32 in 1 .. 5) -> u8 in 0 .. 5 { return a / b; } }"
theorem div1_refused : stufe div1 = "elab: Wert ohne G-Form" := by decide +kernel

/-! ## Wall 1b: an omitted `effects` is read as the empty set -/

/-- PLANTED DEFECT (the one that matters for this widening): a function with NO `effects` clause
    that writes a table. The derived effects would name the write; the empty set must not let it
    through, and the lowering is what stops it. -/
def schreibt1 : String :=
  "module m { table T count 2 { slot { v : u32 in 0 .. 9, } } impl fn w(i : index into T) { T.slots[i].v = 1; } }"
theorem schreibt1_refused : stufe schreibt1 = "lower: write without right" := by decide +kernel

/-! ## Wall 2: conversions `T(e)`, limit words `T::max`/`T::min`, named constants, `& | ^` -/

/-- WITNESS (`beispiele/73`, shortened): a conversion whose operand fits the target type. -/
def konv1 : String :=
  "module m { impl fn w(a : u32 in 0 .. 100) -> u16 { return u13(a); } }"
theorem konv1_ok : stufe konv1 = "OK" := by decide +kernel

/-- PLANTED DEFECT: the operand's range (0 .. 9000) does not fit `u13` (0 .. 8191). The conversion
    is a widening and never truncates, so the lowering refuses instead of widening silently. -/
def konv1_eng : String :=
  "module m { impl fn w(a : u32 in 0 .. 9000) -> u16 { return u13(a); } }"
theorem konv1_eng_refused : stufe konv1_eng = "lower: conversion outside target range" := by decide +kernel

/-- WITNESS: a limit word of a sugared width and of a signed built-in width (a negative number). -/
def grenz1 : String :=
  "module m { impl fn g() -> u64 { return u13::max; } impl fn h() -> i8 { return i8::min; } }"
theorem grenz1_ok : stufe grenz1 = "OK" := by decide +kernel

/-- PLANTED DEFECT: `u13::max` is 8191, which does not fit a `u8` result. -/
def grenz1_eng : String :=
  "module m { impl fn g() -> u8 { return u13::max; } }"
theorem grenz1_eng_refused : stufe grenz1_eng = "lower: value outside range" := by decide +kernel

/-- WITNESS: a named constant is inlined at its use. -/
def konst1 : String :=
  "module m { const K : u32 = 7; impl fn f() -> u8 { return K; } }"
theorem konst1_ok : stufe konst1 = "OK" := by decide +kernel

/-- PLANTED DEFECT: a name that is neither a parameter nor a constant. -/
def konst1_fremd : String :=
  "module m { impl fn f() -> u8 { return L; } }"
theorem konst1_fremd_refused : stufe konst1_fremd = "elab: Name unbekannt: L" := by decide +kernel

/-- WITNESS (`beispiele/69`): `|` of two conversions, `^` with a limit word (`beispiele/62`), `&`. -/
def bit1 : String :=
  "module m { impl fn k(a : u32, b : u32) -> u64 { return u64(a) | u64(b); } impl fn i(w : u32) -> u32 { return w ^ u32::max; } impl fn m(a : u8, b : u8) -> u8 { return a & b; } }"
theorem bit1_ok : stufe bit1 = "OK" := by decide +kernel

/-- PLANTED DEFECT: a bit operation over a signed range (M137 allows non-negative ranges only). -/
def bit1_vorz : String :=
  "module m { impl fn m(a : i32, b : i32) -> i32 { return a & b; } }"
theorem bit1_vorz_refused : stufe bit1_vorz = "lower: bit operation over a negative range" := by decide +kernel

/-- PLANTED DEFECT: a call to something that is not a type word keeps its old refusal. -/
def ruf1 : String :=
  "module m { impl fn f(a : u32 in 0 .. 5) -> u8 { return foo(a); } }"
theorem ruf1_refused : stufe ruf1 = "elab: Wert ohne G-Form" := by decide +kernel

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
theorem bool_zahl_refused : stufe bool_zahl = "elab: Ensures-Klausel ohne G-Form" := by decide +kernel

/-- PLANTED DEFECT: a bool field read as a NUMBER. -/
def bool_als_zahl : String :=
  "module m { table T count 2 { slot { b : bool, } } impl fn get(t : ptr<normal, r> T, i : index into T) -> u32 effects { reads t.slots } { return t.slots[i].b; } }"
theorem bool_als_zahl_refused : stufe bool_als_zahl = "elab: Bool-Feld als Zahl ohne G-Form" := by decide +kernel

/-- PLANTED DEFECT: a truth value stored into a NUMBER field. -/
def zahl_wahr : String :=
  "module m { table T count 2 { slot { n : u32 in 0 .. 9, } } impl fn set(t : ptr<normal, rw> T, i : index into T) effects { writes t.slots } { t.slots[i].n = true; } }"
theorem zahl_wahr_refused : stufe zahl_wahr = "elab: Wert ohne G-Form" := by decide +kernel

/-- PLANTED DEFECT: a number returned where the result is `bool`, and a comparison returned where the
    result is a number. -/
def bool_res_zahl : String :=
  "module m { impl fn f(x : u32 in 0 .. 9) -> bool { return x; } }"
theorem bool_res_zahl_refused : stufe bool_res_zahl = "elab: Ensures-Klausel ohne G-Form" := by decide +kernel

def zahl_res_bool : String :=
  "module m { impl fn f(x : u32 in 0 .. 9) -> u32 { return x <= 5; } }"
theorem zahl_res_bool_refused : stufe zahl_res_bool = "elab: Wert ohne G-Form" := by decide +kernel

#print axioms add1_ok
#print axioms schreibt1_refused

end Gabbro.Grammatik.Parser.UebersetzeProben

