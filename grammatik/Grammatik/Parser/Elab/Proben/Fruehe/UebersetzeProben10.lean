/-
  File:      Grammatik/Parser/Elab/UebersetzeProben10.lean
  Subject:   Wall 3: `bool` probes (split from `UebersetzeProben`: the kernel probes of one file share one memory budget).
-/
module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben
import all Grammatik.Parser.Elab.Proben.RightsConstants.Phases
import Grammatik.Parser.Elab.UebersetzeAllg3.FunctionResults
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
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
section


namespace Gabbro.Grammatik.Parser.UebersetzeProben10

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben (stufe)

set_option maxRecDepth 100000

/-! ## Wall 3: `bool` -- slots, results, truth values in the body, `by ops` -/

/-- WITNESS (`beispiele/16`, `15`, shortened): a `bool` slot written with a literal through a pointer and
    read back as the result. -/
@[expose] public def bool1 : String :=
  "module m { table T count 2 { slot { b : bool, } } impl fn set(t : ptr<normal, rw> T, i : index into T) effects { writes t.slots } { t.slots[i].b = true; } impl fn get(t : ptr<normal, r> T, i : index into T) -> bool effects { reads t.slots } { return t.slots[i].b; } }"

/-- WITNESS (`beispiele/62`, shortened): a `bool` result computed from a comparison. -/
@[expose] public def bool2 : String :=
  "module m { impl fn le(x : u32 in 0 .. 9) -> bool { return x <= 5; } }"

/-- WITNESS: `&&`, `||`, `!` and the literals over comparisons. -/
@[expose] public def bool3 : String :=
  "module m { impl fn f(x : u32 in 0 .. 9, y : u32 in 0 .. 9) -> bool { return x <= 5 && !(y == 3) || false; } }"

/-- WITNESS: `by ops` is a writer discipline the CHECKER holds; the model reads the field as written. -/
@[expose] public def byops1 : String :=
  "module m { table T count 2 { slot { n : u32 in 0 .. 9 by ops, } } impl fn get(t : ptr<normal, r> T, i : index into T) -> u32 effects { reads t.slots } { return t.slots[i].n; } }"

/-- PLANTED DEFECT: a NUMBER stored into a bool field. -/
@[expose] public def bool_zahl : String :=
  "module m { table T count 2 { slot { b : bool, } } impl fn set(t : ptr<normal, rw> T, i : index into T) effects { writes t.slots } { t.slots[i].b = 1; } }"

/-- PLANTED DEFECT: a bool field read as a NUMBER. -/
@[expose] public def bool_als_zahl : String :=
  "module m { table T count 2 { slot { b : bool, } } impl fn get(t : ptr<normal, r> T, i : index into T) -> u32 effects { reads t.slots } { return t.slots[i].b; } }"

/-- PLANTED DEFECT: a truth value stored into a NUMBER field. -/
@[expose] public def zahl_wahr : String :=
  "module m { table T count 2 { slot { n : u32 in 0 .. 9, } } impl fn set(t : ptr<normal, rw> T, i : index into T) effects { writes t.slots } { t.slots[i].n = true; } }"

/-- PLANTED DEFECT: a number returned where the result is `bool`, and a comparison returned where the
    result is a number. -/
@[expose] public def bool_res_zahl : String :=
  "module m { impl fn f(x : u32 in 0 .. 9) -> bool { return x; } }"

@[expose] public def zahl_res_bool : String :=
  "module m { impl fn f(x : u32 in 0 .. 9) -> u32 { return x <= 5; } }"


open scoped Gabbro.Grammatik.Parser.UebersetzeProben11.Phases

-- Each cut is checked by the existing scanner against arbitrary suffix/fuel.
-- The cut factories infer tokens from lexL; no token or AST snapshot is supplied.
namespace Cuts
rights_cut moduleHead as "module m { "
bound_fragment moduleHead as "module m { "
rights_cut tableHead as "module m { table T count 2 { slot { "
bound_fragment tableHead as "module m { table T count 2 { slot { "
rights_cut boolField as "b : bool, } } impl fn "
bound_fragment boolField as "b : bool, } } impl fn "
rights_cut numberField as "n : u32 in 0 .. 9, } } impl fn "
bound_fragment numberField as "n : u32 in 0 .. 9, } } impl fn "
rights_cut opsField as "n : u32 in 0 .. 9 by ops, } } impl fn "
bound_fragment opsField as "n : u32 in 0 .. 9 by ops, } } impl fn "
rights_cut setter as "set(t : ptr<normal, rw> T, i : index into T) effects "
bound_fragment setter as "set(t : ptr<normal, rw> T, i : index into T) effects "
rights_cut boolWrite as "{ writes t.slots } { t.slots[i].b = true; } "
bound_fragment boolWrite as "{ writes t.slots } { t.slots[i].b = true; } "
rights_cut boolGetter as "impl fn get(t : ptr<normal, r> T, i : index into T) -> bool "
bound_fragment boolGetter as "impl fn get(t : ptr<normal, r> T, i : index into T) -> bool "
rights_cut boolRead as "{ reads t.slots } { return t.slots[i].b; } }"
bound_fragment boolRead as "{ reads t.slots } { return t.slots[i].b; } }"
rights_cut numberGetter as "get(t : ptr<normal, r> T, i : index into T) -> u32 "
bound_fragment numberGetter as "get(t : ptr<normal, r> T, i : index into T) -> u32 "
rights_cut numberRead as "{ reads t.slots } { return t.slots[i].n; } }"
bound_fragment numberRead as "{ reads t.slots } { return t.slots[i].n; } }"
rights_cut wrongBoolWrite as "{ writes t.slots } { t.slots[i].b = 1; } }"
bound_fragment wrongBoolWrite as "{ writes t.slots } { t.slots[i].b = 1; } }"
rights_cut wrongNumberWrite as "{ writes t.slots } { t.slots[i].n = true; } }"
bound_fragment wrongNumberWrite as "{ writes t.slots } { t.slots[i].n = true; } }"
rights_cut comparison as "impl fn le(x : u32 in 0 .. 9) -> bool { "
bound_fragment comparison as "impl fn le(x : u32 in 0 .. 9) -> bool { "
rights_cut comparisonReturn as "return x <= 5; } }"
bound_fragment comparisonReturn as "return x <= 5; } }"
rights_cut compound as "impl fn f(x : u32 in 0 .. 9, y : u32 in 0 .. 9) -> bool { "
bound_fragment compound as "impl fn f(x : u32 in 0 .. 9, y : u32 in 0 .. 9) -> bool { "
rights_cut compoundReturn as "return x <= 5 && !(y == 3) || false; } }"
bound_fragment compoundReturn as "return x <= 5 && !(y == 3) || false; } }"
rights_cut boolResult as "impl fn f(x : u32 in 0 .. 9) -> bool { "
bound_fragment boolResult as "impl fn f(x : u32 in 0 .. 9) -> bool { "
rights_cut numberResult as "impl fn f(x : u32 in 0 .. 9) -> u32 { "
bound_fragment numberResult as "impl fn f(x : u32 in 0 .. 9) -> u32 { "
rights_cut parameterReturn as "return x; } }"
bound_fragment parameterReturn as "return x; } }"
end Cuts

-- Compose actual cuts at characters.length + 1, before any parser/elab projection.
namespace Inputs
rights_input bool1 : Gabbro.Grammatik.Parser.UebersetzeProben10.bool1 with_cuts [Cuts.tableHead, Cuts.boolField, Cuts.setter, Cuts.boolWrite,
    Cuts.boolGetter, Cuts.boolRead]
  with_text ["module m { table T count 2 { slot { ", "b : bool, } } impl fn ",
    "set(t : ptr<normal, rw> T, i : index into T) effects ",
    "{ writes t.slots } { t.slots[i].b = true; } ",
    "impl fn get(t : ptr<normal, r> T, i : index into T) -> bool ",
    "{ reads t.slots } { return t.slots[i].b; } }"]
rights_input bool2 : Gabbro.Grammatik.Parser.UebersetzeProben10.bool2 with_cuts [Cuts.moduleHead, Cuts.comparison, Cuts.comparisonReturn]
  with_text ["module m { ", "impl fn le(x : u32 in 0 .. 9) -> bool { ", "return x <= 5; } }"]
rights_input bool3 : Gabbro.Grammatik.Parser.UebersetzeProben10.bool3 with_cuts [Cuts.moduleHead, Cuts.compound, Cuts.compoundReturn]
  with_text ["module m { ", "impl fn f(x : u32 in 0 .. 9, y : u32 in 0 .. 9) -> bool { ",
    "return x <= 5 && !(y == 3) || false; } }"]
rights_input byops1 : Gabbro.Grammatik.Parser.UebersetzeProben10.byops1 with_cuts [Cuts.tableHead, Cuts.opsField, Cuts.numberGetter, Cuts.numberRead]
  with_text ["module m { table T count 2 { slot { ", "n : u32 in 0 .. 9 by ops, } } impl fn ",
    "get(t : ptr<normal, r> T, i : index into T) -> u32 ", "{ reads t.slots } { return t.slots[i].n; } }"]
rights_input bool_zahl : Gabbro.Grammatik.Parser.UebersetzeProben10.bool_zahl with_cuts [Cuts.tableHead, Cuts.boolField, Cuts.setter, Cuts.wrongBoolWrite]
  with_text ["module m { table T count 2 { slot { ", "b : bool, } } impl fn ",
    "set(t : ptr<normal, rw> T, i : index into T) effects ", "{ writes t.slots } { t.slots[i].b = 1; } }"]
rights_input bool_als_zahl : Gabbro.Grammatik.Parser.UebersetzeProben10.bool_als_zahl with_cuts [Cuts.tableHead, Cuts.boolField, Cuts.numberGetter, Cuts.boolRead]
  with_text ["module m { table T count 2 { slot { ", "b : bool, } } impl fn ",
    "get(t : ptr<normal, r> T, i : index into T) -> u32 ", "{ reads t.slots } { return t.slots[i].b; } }"]
rights_input zahl_wahr : Gabbro.Grammatik.Parser.UebersetzeProben10.zahl_wahr with_cuts [Cuts.tableHead, Cuts.numberField, Cuts.setter, Cuts.wrongNumberWrite]
  with_text ["module m { table T count 2 { slot { ", "n : u32 in 0 .. 9, } } impl fn ",
    "set(t : ptr<normal, rw> T, i : index into T) effects ", "{ writes t.slots } { t.slots[i].n = true; } }"]
rights_input bool_res_zahl : Gabbro.Grammatik.Parser.UebersetzeProben10.bool_res_zahl with_cuts [Cuts.moduleHead, Cuts.boolResult, Cuts.parameterReturn]
  with_text ["module m { ", "impl fn f(x : u32 in 0 .. 9) -> bool { ", "return x; } }"]
rights_input zahl_res_bool : Gabbro.Grammatik.Parser.UebersetzeProben10.zahl_res_bool with_cuts [Cuts.moduleHead, Cuts.numberResult, Cuts.comparisonReturn]
  with_text ["module m { ", "impl fn f(x : u32 in 0 .. 9) -> u32 { ", "return x <= 5; } }"]
end Inputs

-- Numeric widths and the actual boolean/comparison/value mutual are used by
-- these four bodies. No large block-fuel reader or unused float branch is forced.
attribute [local cbv_eval] Nat.log2_def lowEns.eq_def lowCmp.eq_def lowWertE.eq_def

-- Infer one complete result from one actual producer equation. Subsequent
-- certificates use its constructor-valued data rather than rerunning getters.
scoped macro "bool_parsed " name:ident " from " supplied:term : command => `(command|
  private def $name : { actual : List SItemTief //
      parseTopTief ($supplied).tokens = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)

scoped macro "bool_elaborated " name:ident " from " parsed:ident : command => `(command|
  private def $name : { actual : UProg // elabU (pre108 ($parsed).val) = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)

scoped macro "bool_function " name:ident " for " unit:ident " at " number:num : command => do
  let index := Lean.mkIdentFrom name (name.getId.appendAfter "_index")
  let header := Lean.mkIdentFrom name (name.getId.appendAfter "_header")
  let body := Lean.mkIdentFrom name (name.getId.appendAfter "_body")
  let ordinal : Lean.TSyntax `term := ⟨number.raw⟩
  let a ← `(command| private def $index : Fin ($unit).val.fns.length := ⟨$ordinal, by decide +kernel⟩)
  let b ← `(command| private theorem $header : PlainFunctionHeader ($unit).val $index := by
    constructor <;> cbv)
  let c ← `(command| private def $body : { actual : PlainFunctionBody ($unit).val $index //
      lowBody ($unit).val $index (fnAt ($unit).val $index).body (fnAt ($unit).val $index).ret = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let d ← `(command| private def $name : { actual :
      EnsTy ($unit).val $index × RumpTy ($unit).val $index × ReqTy ($unit).val $index //
      lowerFnAt ($unit).val $index = .ok actual } := lowerFnAt_from_body $header $body)
  return ⟨Lean.mkNullNode #[a, b, c, d]⟩

open scoped Gabbro.Grammatik.Parser.UebersetzeProben10

bool_parsed bool1_items from Inputs.bool1
bool_elaborated bool1_unit from bool1_items
bool_function bool1_set for bool1_unit at 0
bool_function bool1_get for bool1_unit at 1
bool_parsed bool2_items from Inputs.bool2
bool_elaborated bool2_unit from bool2_items
bool_function bool2_function for bool2_unit at 0
bool_parsed bool3_items from Inputs.bool3
bool_elaborated bool3_unit from bool3_items
bool_function bool3_function for bool3_unit at 0
bool_parsed byops1_items from Inputs.byops1
bool_elaborated byops1_unit from byops1_items
bool_function byops1_function for byops1_unit at 0
bool_parsed bool_zahl_items from Inputs.bool_zahl
bool_parsed bool_als_zahl_items from Inputs.bool_als_zahl
bool_parsed zahl_wahr_items from Inputs.zahl_wahr
bool_parsed bool_res_zahl_items from Inputs.bool_res_zahl
bool_parsed zahl_res_bool_items from Inputs.zahl_res_bool

private theorem function_ok {unit : UProg} {f : Fin unit.fns.length}
    (result : { actual : EnsTy unit f × RumpTy unit f × ReqTy unit f //
      lowerFnAt unit f = .ok actual }) : (lowerFnAt unit f).toOption.isSome = true := by
  rw [result.property]
  rfl

private theorem bool1_count : bool1_unit.val.fns.length = 2 := by cbv
private theorem bool1_functions : ∀ f : Fin bool1_unit.val.fns.length,
    (lowerFnAt bool1_unit.val f).toOption.isSome = true ∧ (fnAt bool1_unit.val f).decreases = none := by
  rintro ⟨index, bound⟩
  have actualBound := bound
  rw [bool1_count] at actualBound
  have alternatives : index = 0 ∨ index = 1 := by omega
  rcases alternatives with rfl | rfl
  · exact ⟨function_ok bool1_set, by cbv⟩
  · exact ⟨function_ok bool1_get, by cbv⟩

scoped macro "bool_single " name:ident " for " unit:ident " using " result:ident : command => do
  let count := Lean.mkIdentFrom name (name.getId.appendAfter "_count")
  let a ← `(command| private theorem $count : ($unit).val.fns.length = 1 := by cbv)
  let b ← `(command| private theorem $name : ∀ f : Fin ($unit).val.fns.length,
      (lowerFnAt ($unit).val f).toOption.isSome = true ∧ (fnAt ($unit).val f).decreases = none := by
    rintro ⟨index, bound⟩
    have actualBound := bound
    rw [$count:ident] at actualBound
    have zero : index = 0 := by omega
    subst index
    exact ⟨function_ok $result, by cbv⟩)
  return ⟨Lean.mkNullNode #[a, b]⟩

bool_single bool2_functions for bool2_unit using bool2_function
bool_single bool3_functions for bool3_unit using bool3_function
bool_single byops1_functions for byops1_unit using byops1_function

private theorem bool_zahl_error : elabU (pre108 bool_zahl_items.val) =
    .error "ensures clause without G form" := by cbv
private theorem bool_als_zahl_error : elabU (pre108 bool_als_zahl_items.val) =
    .error "bool field as a number" := by cbv
private theorem zahl_wahr_error : elabU (pre108 zahl_wahr_items.val) =
    .error "value without G form" := by cbv
private theorem bool_res_zahl_error : elabU (pre108 bool_res_zahl_items.val) =
    .error "number as a truth value" := by cbv
private theorem zahl_res_bool_error : elabU (pre108 zahl_res_bool_items.val) =
    .error "value without G form" := by cbv

public theorem bool1_ok : stufe bool1 = "OK" :=
  UebersetzeProben11.Phases.lower_ok Inputs.bool1 bool1_items.property bool1_unit.property
    (by cbv) (by cbv) bool1_functions

public theorem bool2_ok : stufe bool2 = "OK" :=
  UebersetzeProben11.Phases.lower_ok Inputs.bool2 bool2_items.property bool2_unit.property
    (by cbv) (by cbv) bool2_functions

public theorem bool3_ok : stufe bool3 = "OK" :=
  UebersetzeProben11.Phases.lower_ok Inputs.bool3 bool3_items.property bool3_unit.property
    (by cbv) (by cbv) bool3_functions

public theorem byops1_ok : stufe byops1 = "OK" :=
  UebersetzeProben11.Phases.lower_ok Inputs.byops1 byops1_items.property byops1_unit.property
    (by cbv) (by cbv) byops1_functions

public theorem bool_zahl_refused : stufe bool_zahl = "elab: ensures clause without G form" :=
  UebersetzeProben11.Phases.elab_error Inputs.bool_zahl bool_zahl_items.property bool_zahl_error

public theorem bool_als_zahl_refused : stufe bool_als_zahl = "elab: bool field as a number" :=
  UebersetzeProben11.Phases.elab_error Inputs.bool_als_zahl bool_als_zahl_items.property bool_als_zahl_error

public theorem zahl_wahr_refused : stufe zahl_wahr = "elab: value without G form" :=
  UebersetzeProben11.Phases.elab_error Inputs.zahl_wahr zahl_wahr_items.property zahl_wahr_error

public theorem bool_res_zahl_refused : stufe bool_res_zahl = "elab: number as a truth value" :=
  UebersetzeProben11.Phases.elab_error Inputs.bool_res_zahl bool_res_zahl_items.property bool_res_zahl_error

public theorem zahl_res_bool_refused : stufe zahl_res_bool = "elab: value without G form" :=
  UebersetzeProben11.Phases.elab_error Inputs.zahl_res_bool zahl_res_bool_items.property zahl_res_bool_error

end Gabbro.Grammatik.Parser.UebersetzeProben10
