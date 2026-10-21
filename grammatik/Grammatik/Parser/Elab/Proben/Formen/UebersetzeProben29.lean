/-
  File:      Grammatik/Parser/Elab/Proben/Formen/UebersetzeProben29.lean
  Subject:   Track P: sharing and atomic payloads. `table T .. shared` and `static .. shared;` set the flag the
             declaration reads with the meaning of the generator's specification: a table is shared
             (`D.geteilt`) iff it is marked AND guarded; a static (`D.ggeteilt`) iff it is marked AND (guarded or
             `atomic`); every `atomic` is marked. A marked carrier without a guard is refused (SYNTAX.md 9: a
             shared carrier without one is not declarable). `atomic A : T publishes { p, q }` gives `D.nutzlast`
             (statics only); `A = v publishes { p, q };` (`Stmt.publish`) and `let x = A awaits { p, q };`
             (`Block.awaits`, a `Block` form only) must name exactly the declared payload.
-/
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben29

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- The elaborated program of a source (`none` if it does not elaborate). -/
def prog (s : String) : Option UProg :=
  match lex s with
  | .error _ => none
  | .ok toks =>
    match parseTopTief toks with
    | .error _ => none
    | .ok items =>
      match elabU (pre108 items) with
      | .error _ => none
      | .ok u => some u

/-- The sharing flags of the declaration built from the source: tables, then statics. -/
def geteilt (s : String) : Option (List Bool × List Bool) :=
  (prog s).map fun (u : UProg) =>
    ((List.finRange u.tabs.length).map (fun (t : Fin u.tabs.length) => (declOf u).geteilt t),
     (List.finRange u.globs.length).map (fun (g : Fin u.globs.length) => (declOf u).ggeteilt g))

/-- A shared table under its lock, an unshared guarded table, a shared static under the lock. -/
def shared_ok : String :=
  "module m { table T count 2 shared { slot { v : u32, } } table U count 2 { slot { v : u32, } } static mut N : u32 = 0 shared; lock L protects { T, U, N } rank 0; impl fn f() { } }"
theorem shared_ok_stufe : stufe shared_ok = "OK" := by decide +kernel
theorem shared_ok_geteilt : geteilt shared_ok = some ([true, false], [true]) := by decide +kernel

/-- Planted defect: a shared table without a guard. -/
def shared_tab_refused : String :=
  "module m { table T count 2 shared { slot { v : u32, } } impl fn f() { } }"
theorem shared_tab_refused_stufe : stufe shared_tab_refused = "elab: shared table without a guard" := by
  decide +kernel

/-- Planted defect: a shared static without a guard. -/
def shared_static_refused : String :=
  "module m { static mut N : u32 = 0 shared; impl fn f() { } }"
theorem shared_static_refused_stufe : stufe shared_static_refused = "elab: shared static without a guard" := by
  decide +kernel

/-- An atomic with a payload: the store names it. -/
def payload_ok : String :=
  "module m { static mut P : u8 = 0; atomic A : u8 publishes { P }; impl fn w() effects { writes A } { A = 1 publishes { P }; } }"
theorem payload_ok_stufe : stufe payload_ok = "OK" := by decide +kernel

/-- The payload through the declaration (`D.nutzlast`), and the atomic is shared. -/
theorem payload_ok_daten :
    (prog payload_ok).map (fun (u : UProg) => (List.finRange u.globs.length).map fun g =>
      (((declOf u).nutzlast g).map (·.val), (declOf u).ggeteilt g)) =
    some [([], false), ([0], true)] := by decide +kernel

/-- The load names it (`Block.awaits`, in a nested block). -/
def await_ok : String :=
  "module m { static mut P : u8 = 0; atomic A : u8 publishes { P }; impl fn r(c : bool) { if c { let x = A awaits { P }; } } }"
theorem await_ok_stufe : stufe await_ok = "OK" := by decide +kernel

/-- Planted defect: the store names another payload. -/
def payload_store_refused : String :=
  "module m { static mut P : u8 = 0; atomic A : u8 publishes { P }; impl fn w() effects { writes A } { A = 1 publishes nothing; } }"
theorem payload_store_refused_stufe :
    stufe payload_store_refused = "elab: publishes a payload other than the declared one" := by decide +kernel

/-- Planted defect: the load names another payload. -/
def payload_load_refused : String :=
  "module m { static mut P : u8 = 0; atomic A : u8 publishes { P }; impl fn r(c : bool) { if c { let x = A awaits { }; } } }"
theorem payload_load_refused_stufe :
    stufe payload_load_refused = "elab: awaits a payload other than the declared one" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben29
