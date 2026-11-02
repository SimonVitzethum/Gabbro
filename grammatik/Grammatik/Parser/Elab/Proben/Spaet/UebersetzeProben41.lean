/-
  File:      Grammatik/Parser/Elab/Proben/Spaet/UebersetzeProben41.lean
  Subject:   C05: an invariant's carriers are tables AND statics (`D.traeger : Inv -> List (Tab ⊕ Glob)`).
             A `group G over { A, B }` of statics, and a group of a table and a static under one lock,
             elaborate and lower; `declOf` carries the whole carrier list (`lowerAllg_traeger`). `U003`
             covers a writer of a static (`gputs`); refused: a static writer without the group's lock, a
             predicate reading a static the group does not declare (`lowerInvAt`), an unknown carrier.
             The sources are SHORT on purpose (the kernel lexes them).
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



namespace Gabbro.Grammatik.Parser.UebersetzeProben41

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- The carriers of the invariants, read through the declaration: `.inl` a table number, `.inr` a static
    number. -/
def traeger (s : String) : Option (List (List (Nat ⊕ Nat))) :=
  match lex s with
  | .error _ => none
  | .ok toks =>
    match parseTopTief toks with
    | .error _ => none
    | .ok items =>
      match elabU (pre108 items) with
      | .error _ => none
      | .ok u => some ((List.finRange u.invs.length).map fun (i : Fin u.invs.length) =>
          ((declOf u).traeger i).map (Sum.map (fun (t : Fin u.tabs.length) => t.val)
            (fun (g : Fin u.globs.length) => g.val)))

/-- A global-only group; its writer holds the guard by signature. -/
def glob_gruppe_ok : String :=
  "module m { static mut A : u32 = 0 shared; static mut B : u32 = 0 shared; lock L protects { A, B } rank 0; group G over { A, B } { invariant J cost O(1) runs offline : A <= B; } impl fn f() requires Held(L) effects { writes A } { A = 1; } }"
theorem glob_gruppe_ok_stufe : stufe glob_gruppe_ok = "OK" := by decide +kernel
theorem glob_gruppe_ok_traeger : traeger glob_gruppe_ok = some [[.inr 0, .inr 1]] := by decide +kernel

/-- A mixed group of a table and a static under one lock; the writer touches only the static. -/
def gemischt_ok : String :=
  "module m { table T count 2 shared { slot { v : u32, } } static mut N : u32 = 0 shared; lock L protects { T, N } rank 0; group G over { T, N } { invariant J cost O(1) runs offline : T.slots[0].v <= N; } impl fn f() requires Held(L) effects { writes N } { N = 1; } }"
theorem gemischt_ok_stufe : stufe gemischt_ok = "OK" := by decide +kernel
theorem gemischt_ok_traeger : traeger gemischt_ok = some [[.inl 0, .inr 0]] := by decide +kernel

/-- Planted defect (`U003`): the writer of the static takes the group's guard only in a block. -/
def glob_u003_refused : String :=
  "module m { static mut A : u32 = 0 shared; static mut B : u32 = 0 shared; lock L protects { A, B } rank 0; group G over { A, B } { invariant J cost O(1) runs offline : A <= B; } impl fn f() effects { writes A, locks L } { locks L { A = 1; } } }"
theorem glob_u003_refused_stufe :
    stufe glob_u003_refused = "elab: a writer of an invariant's carrier does not hold all its locks" := by
  decide +kernel

/-- Planted defect: the predicate reads a static (`N`) under the same lock that the group does not declare. -/
def undeklariert_refused : String :=
  "module m { table T count 2 shared { slot { v : u32, } } static mut N : u32 = 0 shared; lock L protects { T, N } rank 0; group G over { T } { invariant J cost O(1) runs offline : T.slots[0].v <= N; } impl fn f(i : index into T) requires Held(L) effects { writes T.slots } { T.slots[i].v = 1; } }"
theorem undeklariert_refused_stufe :
    stufe undeklariert_refused = "lower: an invariant reads a carrier it does not declare" := by
  decide +kernel

/-- Planted defect: a carrier that names no table and no static. -/
def traeger_unbekannt_refused : String :=
  "module m { static mut A : u32 = 0 shared; lock L protects { A } rank 0; group G over { A, Z } { invariant J cost O(1) runs offline : A <= 9; } impl fn f() { } }"
theorem traeger_unbekannt_refused_stufe :
    stufe traeger_unbekannt_refused = "elab: invariant carrier without G form, or ambiguous" := by
  decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben41
