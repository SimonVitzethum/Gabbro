/-
  File:      Grammatik/Parser/Elab/Proben/Spaet/UebersetzeProben34.lean
  Subject:   Track P: `state` stages (Simon, 2026-10-21). The stages of `state S { transition t { f : A -> B } .. }`
             are 0, 1, 2, .. in the order they are first written; the allowed pairs are the `transition` lines;
             the field a `transition T.slots[i].f : A -> B;` statement is applied to is the governed field
             (`D.erlaubt`), and the statement is `Stmt.shift` with the stage numbers.
-/
module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3
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


namespace Gabbro.Grammatik.Parser.UebersetzeProben34

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- `D.erlaubt` at the first field of the first table, for the stage pairs (0,0), (0,1), (1,0), (1,1). -/
def erlaubt01 (s : String) : Option (List Bool) :=
  match lex s with
  | .error _ => none
  | .ok toks =>
    match parseTopTief toks with
    | .error _ => none
    | .ok items =>
      match elabU (pre108 items) with
      | .error _ => none
      | .ok u =>
        if ht : 0 < u.tabs.length then
          if hf : 0 < fieldCount u ⟨0, ht⟩ then
            some ([(0, 0), (0, 1), (1, 0), (1, 1)].map fun (a, c) => erlaubtAt u ⟨0, ht⟩ ⟨0, hf⟩ a c)
          else none
        else none

/-- A declared transition applied to the field `s`: `Idle` is stage 0, `Busy` stage 1. -/
def state_ok : String :=
  "module m { table T count 2 { slot { s : u32 in 0 .. 2, } } state S { transition a { s : Idle -> Busy } } impl fn f(i : index into T) effects { writes T.slots } { transition T.slots[i].s : Idle -> Busy; } }"
theorem state_ok_stufe : stufe state_ok = "OK" := by decide +kernel
theorem state_ok_erlaubt : erlaubt01 state_ok = some [false, true, false, false] := by decide +kernel

/-- Planted defect: the reverse transition is not declared. -/
def state_refused : String :=
  "module m { table T count 2 { slot { s : u32 in 0 .. 2, } } state S { transition a { s : Idle -> Busy } } impl fn f(i : index into T) effects { writes T.slots } { transition T.slots[i].s : Busy -> Idle; } }"
theorem state_refused_stufe : stufe state_refused = "elab: transition not declared by a state" := by decide +kernel

/-- Planted defect: the target stage lies outside the field's range. -/
def state_range_refused : String :=
  "module m { table T count 2 { slot { s : u32 in 0 .. 0, } } state S { transition a { s : Idle -> Busy } } impl fn f(i : index into T) effects { writes T.slots } { transition T.slots[i].s : Idle -> Busy; } }"
theorem state_range_refused_stufe : stufe state_range_refused = "lower: stage outside the field's range" := by
  decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben34
