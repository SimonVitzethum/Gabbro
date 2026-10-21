/-
  File:      Grammatik/Parser/Elab/Proben/Formen/UebersetzeProben32.lean
  Subject:   Track P: invariants (`D.Inv`). A table's `invariant I cost .. runs .. : p;` and a
             `group G over { T, U } { invariant I .. }` elaborate to `UProg.invs` (carrier tables, the predicate
             over no parameter); `declOf` reads them (`Inv := Fin u.invs.length`, `traeger`, `invs`) and
             `Programm.invariante` is the lowered predicate under the guards of its carriers (`invSicht`). A
             writer of a carrier holds every lock guarding a carrier (`U003`, `invarianten_gehalten`); the
             elaborator refuses a unit where it does not.
-/
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben32

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- The carrier numbers of the invariants, read through the declaration. -/
def traeger (s : String) : Option (List (List Nat)) :=
  match lex s with
  | .error _ => none
  | .ok toks =>
    match parseTopTief toks with
    | .error _ => none
    | .ok items =>
      match elabU (pre108 items) with
      | .error _ => none
      | .ok u => some ((List.finRange u.invs.length).map fun (i : Fin u.invs.length) =>
          ((declOf u).traeger i).map (fun (t : Fin u.tabs.length) => t.val))

/-- A table invariant; its writer holds the guard by signature. -/
def inv_ok : String :=
  "module m { table T count 2 { slot { v : u32, } invariant I cost O(1) runs offline : forall k in slots of T : T.slots[k].v < 9; } lock L protects { T } rank 0; impl fn f(i : index into T) requires Held(L) effects { writes T.slots } { T.slots[i].v = 1; } }"
theorem inv_ok_stufe : stufe inv_ok = "OK" := by decide +kernel
theorem inv_ok_traeger : traeger inv_ok = some [[0]] := by decide +kernel

/-- Planted defect (`U003`): the writer takes the guard only in a block. -/
def inv_u003_refused : String :=
  "module m { table T count 2 { slot { v : u32, } invariant I cost O(1) runs offline : T.slots[0].v < 9; } lock L protects { T } rank 0; impl fn f(i : index into T) effects { writes T.slots, locks L } { locks L { T.slots[i].v = 1; } } }"
theorem inv_u003_refused_stufe :
    stufe inv_u003_refused = "elab: a writer of an invariant's carrier does not hold all its locks" := by
  decide +kernel

/-- A group invariant over two tables. -/
def gruppe_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } table U count 2 { slot { w : u32, } } group G over { T, U } { invariant J cost O(1) runs offline : T.slots[0].v <= U.slots[0].w; } impl fn f() { } }"
theorem gruppe_ok_stufe : stufe gruppe_ok = "OK" := by decide +kernel
theorem gruppe_ok_traeger : traeger gruppe_ok = some [[0, 1]] := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben32
