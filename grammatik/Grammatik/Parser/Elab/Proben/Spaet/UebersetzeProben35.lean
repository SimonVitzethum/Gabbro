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

/-- Source-to-G witness for consuming: the current tree domain supplies membership,
    its declared self edge supplies ordering, and the state-reading count is the measure.
    This witnesses elaboration, not discharge of the writer's removal/decrease duty. -/
def consuming_ok : String :=
  "module m { table T count 2 { tree { child next } slot { next : option index into Self, live : bool, } } impl fn f(root : index into T) effects { writes T.slots } { traverse k over descendants of T.slots[root] by consuming decreases count j in slots of T : T.slots[j].live touches consumes T.slots invariant true { T.slots[k].live = false; T.slots[k].next = None; } } }"

theorem consuming_traversal_source_zeuge : stufe consuming_ok = "OK" := by decide +kernel

/-- Negative twin: the quantified table is guarded and its lock is not held. -/
def trav_guard_refused : String :=
  "module m { table T count 2 { slot { v : bool, } } lock L protects { T } rank 0; impl fn f() { traverse k over slots of T by unvisited invariant forall j in slots of T : T.slots[j].v { } } }"
theorem trav_guard_refused_stufe : stufe trav_guard_refused = "elab: access without held guard" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben35
