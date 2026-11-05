/-
  File:      Grammatik/Parser/UebersetzeProben.lean
  Subject:   Sieve (a), parser lane: witnesses and planted defects for the widenings of the
             elaborator and the generic lowering.

  Every probe runs the WHOLE pipeline `uebersetzeAllg` on a small source text and names the stage
  where it stops (`stufe`). A WITNESS is a source that reaches `OK`; a PLANTED DEFECT is a source
  one token away that must stop, at the stage and with the message the widening promises. A
  widening whose defect also passes would be a widening that let something through.

  The texts are short on purpose: the kernel decodes a `String` per proof (O13).
  Pipeline certificates stop at elaboration and check the actual lowering phases separately.
  The source strings and all expected stage diagnostics stay pinned below.
  Corpus programs are pinned as characters in the chain instances, not here.

  WALL 1 (2026-09-30): units WITHOUT a table; integer arithmetic (`+`, `-`, `*`) in values, with
  the range of the result computed like `Expr.add`/`sub`/`mul` carry it; the built-in widths
  `uN`/`iN`; an omitted `effects` (derived by the checker) read as the empty set.
-/
module
public import Grammatik.Parser.Elab.UebersetzePipeline
-- The shared phase executes these gates even when a source declares no checks or static parameters.
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export
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

-- Use the canonical logarithm equation rather than its large internal recursor fuel.
attribute [local cbv_eval] Nat.log2_def

/-- A proof-only continuation pins every frontend phase without evaluating a lowered program. -/
private def Frontend (source : String) (unit : UProg) : Prop :=
  ∀ after : UProg → String,
    (match lex source with
    | .error _ => "lex"
    | .ok tokens => match parseTopTief tokens with
      | .error error => "parse: " ++ error
      | .ok items => match elabU (pre108 items) with
        | .error error => "elab: " ++ error
        | .ok actual => after actual) = after unit

private theorem stufe_after {source : String} {unit : UProg} {expected : String}
    (front : Frontend source unit)
    (lowered : (match lowerAllg unit with
      | .error error => "lower: " ++ error | .ok _ => "OK") = expected) :
    stufe source = expected :=
  (front (fun actual => match lowerAllg actual with
    | .error error => "lower: " ++ error | .ok _ => "OK")).trans lowered

/-- All absent source measures produce empty tuples, so the actual cycle-length gate passes
    independently of the program bodies. Every function still passes lowerEach and contractGate. -/
private theorem lowering_ok (unit : UProg)
    (invariants : lowerInvs unit (List.finRange unit.invs.length) = .ok ())
    (functions : lowerEach unit (List.finRange unit.fns.length) = .ok ())
    (contracts : contractGate unit = true)
    (measures : (Measures.lowerMeasures unit).toOption.isSome = true)
    (absent : ∀ fn ∈ unit.fns, fn.decreases = none) :
    (lowerAllg unit).toOption.isSome = true := by
  let exported := (Measures.lowerMeasures unit).toOption.get measures
  have measured : Measures.lowerMeasures unit = .ok exported := except_ok_get measures
  have checked (program : Programm (declOf unit)) :
      (Measures.checkedProgram unit program).toOption.isSome = true := by
    have cycles : Measures.cycleLengths unit program exported.mass = true := by
      unfold Measures.cycleLengths
      apply List.all_eq_true.mpr
      intro f _
      apply List.all_eq_true.mpr
      intro g _
      have empty (i : Fin unit.fns.length) : exported.mass i = [] :=
        Measures.lowerMeasures_absent unit exported measured i
          (absent (fnAt unit i) (List.get_mem unit.fns i))
      simp only [empty, List.length_nil]
      simp
    rw [Measures.checkedProgram, measured, if_pos cycles]
    rfl
  unfold lowerAllg
  simp only [invariants, functions]
  rw [dite_eq_left contracts]
  exact checked _

private theorem lowering_error (unit : UProg) (error : String)
    (invariants : lowerInvs unit (List.finRange unit.invs.length) = .ok ())
    (functions : lowerEach unit (List.finRange unit.fns.length) = .error error) :
    lowerAllg unit = .error error := by
  unfold lowerAllg
  simp only [invariants, functions]

private theorem stufe_ok {source : String} {unit : UProg} (front : Frontend source unit)
    (lowered : (lowerAllg unit).toOption.isSome = true) : stufe source = "OK" := by
  apply stufe_after front
  rw [except_ok_get lowered]

private theorem stufe_error {source : String} {unit : UProg} {error : String}
    (front : Frontend source unit) (lowered : lowerAllg unit = .error error) :
    stufe source = "lower: " ++ error := by
  apply stufe_after front
  rw [lowered]

/-- Shared fixture construction only; Frontend certifies equality with the complete actual unit. -/
private def scalarUnit (name : String) (parameters : List (String × Ty))
    (result : Int × Int) (value : USide) : UProg :=
  { tabs := []
    locks := []
    fns := [
      { name := name
        params := parameters
        kinds := parameters.map (fun _ => .int)
        res := some result
        held := []
        puts := []
        gives := []
        body := []
        ret := .val value }] }

/-! ## Wall 1a: a unit with no table, arithmetic in a return -/

/-- WITNESS (`beispiele/130`, shortened): sum of two bounded parameters, result range wide enough. -/
def add1 : String :=
  "module m { impl fn add(a : u32 in 0 .. 1000, b : u32 in 0 .. 1000) -> u32 in 0 .. 2000 { return a + b; } }"
theorem add1_ok : stufe add1 = "OK" := by
  let unit : UProg := scalarUnit "add" [("a", .int 0 1000), ("b", .int 0 1000)] (0, 2000) (.add (.param "a") (.param "b"))
  have front : Frontend add1 unit := by intro after; cbv
  apply stufe_ok front
  exact lowering_ok unit rfl (by cbv) (by cbv) (by cbv)
    (by simp [unit, scalarUnit])

/-- PLANTED DEFECT: the same body against a result range one short of the sum's range (0 .. 1998).
    The lowering must refuse it, not widen silently. -/
def add1_eng : String :=
  "module m { impl fn add(a : u32 in 0 .. 1000, b : u32 in 0 .. 1000) -> u32 in 0 .. 1999 { return a + b; } }"
theorem add1_eng_refused : stufe add1_eng = "lower: value outside range" := by
  let unit : UProg := scalarUnit "add" [("a", .int 0 1000), ("b", .int 0 1000)] (0, 1999) (.add (.param "a") (.param "b"))
  have front : Frontend add1_eng unit := by intro after; cbv
  exact stufe_error front (lowering_error unit "value outside range" rfl (by cbv))

/-- WITNESS: subtraction takes the range `lo1 - hi2 .. hi1 - lo2`, so `a - b` of two `0 .. 10`
    parameters fits `i8` (`-10 .. 10`) and the built-in width name resolves. -/
def sub1 : String :=
  "module m { impl fn d(a : u32 in 0 .. 10, b : u32 in 0 .. 10) -> i8 { return a - b; } }"
theorem sub1_ok : stufe sub1 = "OK" := by
  let unit : UProg := scalarUnit "d" [("a", .int 0 10), ("b", .int 0 10)] (-128, 127) (.sub (.param "a") (.param "b"))
  have front : Frontend sub1 unit := by intro after; cbv
  apply stufe_ok front
  exact lowering_ok unit rfl (by cbv) (by cbv) (by cbv)
    (by simp [unit, scalarUnit])

/-- PLANTED DEFECT: the same difference into an UNSIGNED result. The lower end is `-10`. -/
def sub1_vorz : String :=
  "module m { impl fn d(a : u32 in 0 .. 10, b : u32 in 0 .. 10) -> u8 { return a - b; } }"
theorem sub1_vorz_refused : stufe sub1_vorz = "lower: value outside range" := by
  let unit : UProg := scalarUnit "d" [("a", .int 0 10), ("b", .int 0 10)] (0, 255) (.sub (.param "a") (.param "b"))
  have front : Frontend sub1_vorz unit := by intro after; cbv
  exact stufe_error front (lowering_error unit "value outside range" rfl (by cbv))

/-- WITNESS: a product, and a nested sum of it (`3 * a + b`). -/
def mul1 : String :=
  "module m { impl fn f(a : u32 in 0 .. 5, b : u32 in 0 .. 5) -> u8 in 0 .. 20 { return 3 * a + b; } }"
theorem mul1_ok : stufe mul1 = "OK" := by
  let unit : UProg := scalarUnit "f" [("a", .int 0 5), ("b", .int 0 5)] (0, 20) (.add (.mul (.lit 3) (.param "a")) (.param "b"))
  have front : Frontend mul1 unit := by intro after; cbv
  apply stufe_ok front
  exact lowering_ok unit rfl (by cbv) (by cbv) (by cbv)
    (by simp [unit, scalarUnit])

/-- WITNESS (was a planted defect until division got its G form): `Expr.div` over a denominator from `1`. -/
def div1 : String :=
  "module m { impl fn f(a : u32 in 0 .. 5, b : u32 in 1 .. 5) -> u8 in 0 .. 5 { return a / b; } }"
theorem div1_ok : stufe div1 = "OK" := by
  let unit : UProg := scalarUnit "f" [("a", .int 0 5), ("b", .int 1 5)] (0, 5) (.div (.param "a") (.param "b"))
  have front : Frontend div1 unit := by intro after; cbv
  apply stufe_ok front
  exact lowering_ok unit rfl (by cbv) (by cbv) (by cbv)
    (by simp [unit, scalarUnit])

/-! ## Wall 1b: an omitted `effects` is read as the empty set -/

/-- PLANTED DEFECT (the one that matters for this widening): a function with NO `effects` clause
    that writes a table. The derived effects would name the write; the empty set must not let it
    through, and the lowering is what stops it. -/
def schreibt1 : String :=
  "module m { table T count 2 { slot { v : u32 in 0 .. 9, } } impl fn w(i : index into T) { T.slots[i].v = 1; } }"
theorem schreibt1_refused : stufe schreibt1 = "lower: write without right" := by
  let unit : UProg :=
    { tabs := [{ name := "T", count := 2, cols := [("v", (0, 9))], breiten := [("v", 32)] }]
      locks := []
      fns := [
        { name := "w"
          params := [("i", .int 0 1)]
          kinds := [.index 0]
          res := none
          held := []
          puts := []
          gives := []
          body := [.assignTab "T" "v" (.param "i") (.lit 1)]
          ret := .empty }] }
  have front : Frontend schreibt1 unit := by intro after; cbv
  exact stufe_error front (lowering_error unit "write without right" rfl (by cbv))

/-! ## Wall 2: conversions `T(e)`, limit words `T::max`/`T::min`, named constants, `& | ^` -/

/-- WITNESS (`beispiele/73`, shortened): a conversion whose operand fits the target type. -/
def konv1 : String :=
  "module m { impl fn w(a : u32 in 0 .. 100) -> u16 { return u13(a); } }"
theorem konv1_ok : stufe konv1 = "OK" := by
  let unit : UProg := scalarUnit "w" [("a", .int 0 100)] (0, 65535) (.conv 0 8191 (.param "a"))
  have front : Frontend konv1 unit := by intro after; cbv
  apply stufe_ok front
  exact lowering_ok unit rfl (by cbv) (by cbv) (by cbv)
    (by simp [unit, scalarUnit])

/-- PLANTED DEFECT: the operand's range (0 .. 9000) does not fit `u13` (0 .. 8191). The conversion
    is a widening and never truncates, so the lowering refuses instead of widening silently. -/
def konv1_eng : String :=
  "module m { impl fn w(a : u32 in 0 .. 9000) -> u16 { return u13(a); } }"
theorem konv1_eng_refused : stufe konv1_eng = "lower: conversion outside target range" := by
  let unit : UProg := scalarUnit "w" [("a", .int 0 9000)] (0, 65535) (.conv 0 8191 (.param "a"))
  have front : Frontend konv1_eng unit := by intro after; cbv
  exact stufe_error front (lowering_error unit "conversion outside target range" rfl (by cbv))

/-- WITNESS: a limit word of a sugared width and of a signed built-in width (a negative number). -/
def grenz1 : String :=
  "module m { impl fn g() -> u64 { return u13::max; } impl fn h() -> i8 { return i8::min; } }"
theorem grenz1_ok : stufe grenz1 = "OK" := by
  let unit : UProg :=
    { tabs := []
      locks := []
      fns := (scalarUnit "g" [] (0, 18446744073709551615) (.lit 8191)).fns ++
        (scalarUnit "h" [] (-128, 127) (.lit (-128))).fns }
  have front : Frontend grenz1 unit := by intro after; cbv
  apply stufe_ok front
  exact lowering_ok unit rfl (by cbv) (by cbv) (by cbv)
    (by simp [unit, scalarUnit])

/-- PLANTED DEFECT: `u13::max` is 8191, which does not fit a `u8` result. -/
def grenz1_eng : String :=
  "module m { impl fn g() -> u8 { return u13::max; } }"
theorem grenz1_eng_refused : stufe grenz1_eng = "lower: value outside range" := by
  let unit : UProg := scalarUnit "g" [] (0, 255) (.lit 8191)
  have front : Frontend grenz1_eng unit := by intro after; cbv
  exact stufe_error front (lowering_error unit "value outside range" rfl (by cbv))

/-- WITNESS: a named constant is inlined at its use. -/
def konst1 : String :=
  "module m { const K : u32 = 7; impl fn f() -> u8 { return K; } }"
theorem konst1_ok : stufe konst1 = "OK" := by
  let unit : UProg := scalarUnit "f" [] (0, 255) (.lit 7)
  have front : Frontend konst1 unit := by intro after; cbv
  apply stufe_ok front
  exact lowering_ok unit rfl (by cbv) (by cbv) (by cbv)
    (by simp [unit, scalarUnit])

/-- PLANTED DEFECT: a name that is neither a parameter nor a constant. -/
def konst1_fremd : String :=
  "module m { impl fn f() -> u8 { return L; } }"
theorem konst1_fremd_refused : stufe konst1_fremd = "elab: name unknown: L" := by cbv

/-- WITNESS (`beispiele/69`): `|` of two conversions, `^` with a limit word (`beispiele/62`), `&`. -/
def bit1 : String :=
  "module m { impl fn k(a : u32, b : u32) -> u64 { return u64(a) | u64(b); } impl fn i(w : u32) -> u32 { return w ^ u32::max; } impl fn m(a : u8, b : u8) -> u8 { return a & b; } }"
theorem bit1_ok : stufe bit1 = "OK" := by
  let unit : UProg :=
    { tabs := []
      locks := []
      fns := (scalarUnit "k" [("a", .int 0 4294967295), ("b", .int 0 4294967295)]
          (0, 18446744073709551615)
          (.bor (.conv 0 18446744073709551615 (.param "a"))
            (.conv 0 18446744073709551615 (.param "b")))).fns ++
        (scalarUnit "i" [("w", .int 0 4294967295)] (0, 4294967295)
          (.bxor (.param "w") (.lit 4294967295))).fns ++
        (scalarUnit "m" [("a", .int 0 255), ("b", .int 0 255)] (0, 255)
          (.band (.param "a") (.param "b"))).fns }
  have front : Frontend bit1 unit := by intro after; cbv
  apply stufe_ok front
  exact lowering_ok unit rfl (by cbv) (by cbv) (by cbv)
    (by simp [unit, scalarUnit])

/-- PLANTED DEFECT: a bit operation over a signed range (M137 allows non-negative ranges only). -/
def bit1_vorz : String :=
  "module m { impl fn m(a : i32, b : i32) -> i32 { return a & b; } }"
theorem bit1_vorz_refused : stufe bit1_vorz = "lower: bit operation over a negative range" := by
  let unit : UProg := scalarUnit "m" [("a", .int (-2147483648) 2147483647), ("b", .int (-2147483648) 2147483647)] (-2147483648, 2147483647) (.band (.param "a") (.param "b"))
  have front : Frontend bit1_vorz unit := by intro after; cbv
  exact stufe_error front (lowering_error unit "bit operation over a negative range" rfl (by cbv))

/-- PLANTED DEFECT: an unresolved direct call fails the mandatory closed-reference gate. -/
def ruf1 : String :=
  "module m { impl fn f(a : u32 in 0 .. 5) -> u8 { return foo(a); } }"
theorem ruf1_refused : stufe ruf1 =
    "elab: generic-output: residual syntax, name collision or unresolved direct global reference" := by cbv


#print axioms add1_ok
#print axioms schreibt1_refused

end Gabbro.Grammatik.Parser.UebersetzeProben
