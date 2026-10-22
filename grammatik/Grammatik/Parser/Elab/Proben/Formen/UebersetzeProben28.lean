/-
  File:      Grammatik/Parser/Elab/Proben/Formen/UebersetzeProben28.lean
  Subject:   Track P: device registers (`D.Reg`). A `device` item elaborates to `UProg.regs` (type range, class,
             mirror, `depends` carriers, the device's promise); `declOf` reads them (`Reg := Fin u.regs.length`).
             A device handle `d : D` is no value of the model (a register is outside the world): it is erased
             from the parameters and names the device of `d.R`. `let x = d.R;` is `Block.regRead`,
             `let x = d.R else (e) { .. }` at a register with `requires p else A::B` is `Block.regReadElse`,
             `d.R = v;` is `Stmt.regWrite`. Both reads are `Block` forms only: `Endblock` has no register read,
             so a read at the top level of a body is refused by name (a model gap, reported).
-/
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben28

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

/-- A read and a write in a nested block. -/
def reg_ok : String :=
  "module m { device D(b : u64) at mmio { reg S : u32 in 0 .. 9 @0 class r reg C : u32 in 0 .. 9 @4 class w } impl fn f(d : D, c : bool) -> u32 in 0 .. 9 { if c { let x = d.S; d.C = x; return x; } return 0; } }"
theorem reg_ok_stufe : stufe reg_ok = "OK" := by decide +kernel

/-- The registers as data, and the handle erased from the parameters (`f` has the one parameter `c`). -/
theorem reg_ok_daten :
    (prog reg_ok).map (fun u => (u.regs.map fun g => (g.name, g.lo, g.hi, g.klasse),
      u.fns.map fun f => f.params.length)) =
    some ([("S", 0, 9, Regklasse.r), ("C", 0, 9, Regklasse.w)], [1]) := by decide +kernel

/-- Planted defect: a write to a register of class `r`. -/
def reg_class_refused : String :=
  "module m { device D(b : u64) at mmio { reg S : u32 in 0 .. 9 @0 class r } impl fn f(d : D, c : bool) { if c { d.S = 1; } } }"
theorem reg_class_refused_stufe : stufe reg_class_refused = "lower: register written against its class" := by
  decide +kernel

/-- A read at the top level of a body: `Endblock.regRead`. -/
def reg_top_ok : String :=
  "module m { device D(b : u64) at mmio { reg S : u32 in 0 .. 9 @0 class r } impl fn f(d : D) -> u32 in 0 .. 9 { let x = d.S; return x; } }"
theorem reg_top_ok_stufe : stufe reg_top_ok = "OK" := by decide +kernel

/-- A fallible read (`requires p else A::B`) in a `let .. else`. -/
def reg_else_ok : String :=
  "module m { reason G { Z = 1 \"z\" exhaustive } device D(b : u64) at mmio { reg T : u32 in 0 .. 9 @8 class r requires T <= 8 else G::Z } impl fn f(d : D, c : bool) -> u32 in 0 .. 9 or G { if c { let t = d.T else (e) { return G::Z; } return t; } return 0; } }"
theorem reg_else_ok_stufe : stufe reg_else_ok = "OK" := by decide +kernel

/-- ... and its bare read is refused. -/
def reg_else_refused : String :=
  "module m { reason G { Z = 1 \"z\" exhaustive } device D(b : u64) at mmio { reg T : u32 in 0 .. 9 @8 class r requires T <= 8 else G::Z } impl fn f(d : D, c : bool) -> u32 in 0 .. 9 or G { if c { let t = d.T; return t; } return 0; } }"
theorem reg_else_refused_stufe : stufe reg_else_refused = "elab: fallible register read needs `let .. else`" := by
  decide +kernel

/-- The device's promise (`requires p` without `else`), the mirror and the `depends` carriers. -/
def reg_decl_ok : String :=
  "module m { table Z count 2 { slot { v : u32, } } device D(b : u64) at mmio { mirrors W from R; reg W : u32 in 0 .. 9 @0 class w reg R : u32 in 0 .. 9 @4 class r requires R <= 8 depends { Z } } impl fn f() { } }"
theorem reg_decl_ok_stufe : stufe reg_decl_ok = "OK" := by decide +kernel

/-- The promise at a value (`D.rzusage` reads it), the mirror through `declOf` (`D.spiegel`), the carriers. -/
theorem reg_decl_ok_daten :
    (prog reg_decl_ok).map (fun u =>
      (u.regs.map fun g => (g.zusageBei 8, g.zusageBei 9, g.traeger),
       (List.finRange u.regs.length).map fun r => (spiegelAt u r).map (·.val))) =
    some ([(true, true, []), (true, false, ["Z"])], [some 1, none]) := by decide +kernel

/-- A register of an EMPTY range is declarable (a read answers nothing; the checker refuses it, `N314`). -/
def reg_leer_ok : String :=
  "module m { device D(b : u64) at mmio { reg E : u32 in 1 .. 0 @0 class rw } impl fn f() { } }"
theorem reg_leer_ok_stufe : stufe reg_leer_ok = "OK" := by decide +kernel

theorem reg_leer_ok_daten :
    (prog reg_leer_ok).map (fun u => u.regs.map fun g => (g.lo, g.hi)) = some [(1, 0)] := by decide +kernel

/-- ... and no value can be written to it. -/
def reg_leer_refused : String :=
  "module m { device D(b : u64) at mmio { reg E : u32 in 1 .. 0 @0 class rw } impl fn f(d : D, c : bool) { if c { d.E = 1; } } }"
theorem reg_leer_refused_stufe : stufe reg_leer_refused = "lower: value outside range" := by decide +kernel

/-- A device `transition` has no statement that invokes it: refused by name. -/
def reg_trans_refused : String :=
  "module m { device D(b : u64) at mmio { mirrors W from R; reg W : u32 @0 class w reg R : u32 @4 class r transition t { W.b : 0 -> 1 } } impl fn f() { } }"
theorem reg_trans_refused_stufe : stufe reg_trans_refused = "elab: device transition without G form" := by
  decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben28
