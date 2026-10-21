/-
  File:      Grammatik/Parser/Elab/Proben/Spaet/UebersetzeProben35.lean
  Subject:   Track P: truth-valued registers and predicate `traverse` invariants (Simon, 2026-10-21; the model
             already has both: `D.rtyp : Reg → Ty`, `Stmt.traverse t (inv : Expr .bool) body`).
             * `reg S : bool @k class c` is a register with `D.rtyp S = Ty.bool`; `let x = d.S;` binds a truth value
               and `d.S = p;` writes one. A number written to it, and a truth value written to a numeric register,
               are refused.
             * `traverse k over slots of T by unvisited invariant forall j in slots of U : p { .. }` reads a
               predicate as the invariant (`Expr.forallSlots`); the quantified table is read under its guards like
               in a `requires`.
-/
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben35

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- The register types of the declaration a source builds. -/
def regTypen (s : String) : Option (List Ty) :=
  match lex s with
  | .error _ => none
  | .ok toks =>
    match parseTopTief toks with
    | .error _ => none
    | .ok items =>
      match elabU (pre108 items) with
      | .error _ => none
      | .ok u => some ((List.finRange u.regs.length).map fun r => (declOf u).rtyp r)

/-- A truth-valued register, read and written in a nested block. -/
def bool_ok : String :=
  "module m { device D(b : u64) at mmio { reg S : bool @0 class rw } impl fn f(d : D, c : bool) { if c { let x = d.S; d.S = !x; } } }"
theorem bool_ok_stufe : stufe bool_ok = "OK" := by decide +kernel
theorem bool_ok_typ : regTypen bool_ok = some [.bool] := by decide +kernel

/-- Negative twin: a number written to a truth-valued register. -/
def bool_zahl_refused : String :=
  "module m { device D(b : u64) at mmio { reg S : bool @0 class rw } impl fn f(d : D, c : bool) { if c { d.S = 1; } } }"
theorem bool_zahl_refused_stufe : stufe bool_zahl_refused = "elab: ensures clause without G form" := by decide +kernel

/-- Negative twin: a truth value written to a numeric register. -/
def zahl_bool_refused : String :=
  "module m { device D(b : u64) at mmio { reg S : u32 in 0 .. 9 @0 class rw } impl fn f(d : D, c : bool) { if c { d.S = true; } } }"
theorem zahl_bool_refused_stufe : stufe zahl_bool_refused = "elab: value without G form" := by decide +kernel

/-- A quantified `traverse` invariant. -/
def trav_ok : String :=
  "module m { table T count 2 { slot { v : bool, } } impl fn f() { traverse k over slots of T by unvisited invariant forall j in slots of T : T.slots[j].v { } } }"
theorem trav_ok_stufe : stufe trav_ok = "OK" := by decide +kernel

/-- Negative twin: the quantified table is guarded and its lock is not held. -/
def trav_guard_refused : String :=
  "module m { table T count 2 { slot { v : bool, } } lock L protects { T } rank 0; impl fn f() { traverse k over slots of T by unvisited invariant forall j in slots of T : T.slots[j].v { } } }"
theorem trav_guard_refused_stufe : stufe trav_guard_refused = "elab: access without held guard" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben35
