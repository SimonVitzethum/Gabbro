/-
  File:      Grammatik/Parser/Elab/UebersetzeProben3.lean
  Subject:   Sieve (a), parser lane: witnesses and planted defects of wall 7 (`entry` roots), split from
             `UebersetzeProben2` so that each file stays small. Kernel probes of one file share one memory budget (measured 2026-09-30:
             the first file alone passed 7 GB).
-/
import Grammatik.Parser.Elab.UebersetzePipeline

namespace Gabbro.Grammatik.Parser.UebersetzeProben3

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

/-! WALL 7 (2026-09-30): `entry ... dispatch f;` -- the dispatch target is a THREAD ROOT of the unit
    (`UProg.wurzeln`, `Einheit.starts` in the bridge). An entry with a handler word (`via`) is a root AND a
    handler (`UProg.handler`, `Programm.unterbricht`); one that dispatches to a function with parameters, and
    one that names no function of the unit, are refused. `concurrent` members are roots too (first).
    The sources are SHORT on purpose: the kernel lexes them (2.7 GB for a 300-character text). -/

def entry1_ok : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } }"
theorem entry1_ok_stufe : stufe entry1_ok = "OK" := by decide +kernel

def entry_two_ok : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } entry f vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } }"
theorem entry_two_ok_stufe : stufe entry_two_ok = "OK" := by decide +kernel

def entry_via_ok : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 via idt arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } }"
theorem entry_via_ok_stufe : stufe entry_via_ok = "OK" := by decide +kernel

def entry_params_refused : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::p; } }"
theorem entry_params_refused_stufe : stufe entry_params_refused = "elab: dispatch names a function with parameters: no start-argument form: p" := by decide +kernel

def entry_unknown_refused : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::nix; } }"
theorem entry_unknown_refused_stufe : stufe entry_unknown_refused = "elab: dispatch names an unknown function: nix" := by decide +kernel

/-- The elaborated roots and handlers of a source (`none` when a stage stops it). -/
def roots (s : String) : Option (List String × List String) :=
  match lex s with
  | .error _ => none
  | .ok toks =>
    match parseTopTief toks with
    | .error _ => none
    | .ok items =>
      match elabU (pre108 items) with
      | .error _ => none
      | .ok u => some (u.roots, u.hands)

theorem via_is_root_and_handler : roots entry_via_ok = some (["w"], ["w"]) := by decide +kernel
theorem plain_entry_is_no_handler : roots entry1_ok = some (["w"], []) := by decide +kernel

def locks_plain : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; impl fn w() { } }"

def conc_ok : String := "module m { impl fn w() { } impl fn v() { } concurrent { w, v }; }"
theorem conc_ok_roots : roots conc_ok = some (["w", "v"], []) := by decide +kernel

def conc_first : String :=
  "module m { impl fn w() { } impl fn v() { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::v; } concurrent { w }; }"
theorem concurrent_roots_come_first : roots conc_first = some (["w", "v"], []) := by decide +kernel

/-- A start with its arguments (`concurrent { m::f(a, b) }`): one value per parameter. -/
def conc_args_ok : String :=
  "module m { impl fn p(i : u32 in 0 .. 1, b : bool) { } concurrent { p(1, true) }; }"
theorem conc_args_ok_roots : roots conc_args_ok = some (["p"], []) := by decide +kernel

/-- A start without the arguments its function needs. -/
def conc_params_refused : String := "module m { impl fn p(i : u32 in 0 .. 1) { } concurrent { p }; }"
theorem conc_params_refused_stufe :
    stufe conc_params_refused = "elab: concurrent member with 0 arguments for 1 parameters: p" := by
  decide +kernel

/-- A start argument outside its parameter's range. -/
def conc_arg_range_refused : String := "module m { impl fn p(i : u32 in 0 .. 1) { } concurrent { p(2) }; }"
theorem conc_arg_range_refused_stufe :
    stufe conc_arg_range_refused = "elab: concurrent member with an argument outside its parameter's type: p" := by
  decide +kernel

/-- A pointer parameter is started with `&T`, the one pointer to the carrier its type names. -/
def conc_ptr_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } impl fn p(k : ptr<normal, r> T) { } concurrent { p(&T) }; }"
theorem conc_ptr_ok_roots : roots conc_ptr_ok = some (["p"], []) := by decide +kernel

/-- Twin: `&U` for a pointer into `T` is refused. -/
def conc_ptr_refused : String :=
  "module m { table T count 2 { slot { v : u32, } } table U count 2 { slot { v : u32, } } impl fn p(k : ptr<normal, r> T) { } concurrent { p(&U) }; }"
theorem conc_ptr_refused_stufe :
    stufe conc_ptr_refused = "elab: concurrent member with an argument outside its parameter's type: p" := by
  decide +kernel

def conc_unknown_refused : String := "module m { impl fn w() { } concurrent { nix }; }"
theorem conc_unknown_refused_stufe :
    stufe conc_unknown_refused = "elab: concurrent member names an unknown function: nix" := by decide +kernel

/-! `masks irqs` on a lock is `D.maskiert`: the lock of the elaborated program says so, and any other mask
    word is refused. -/

def mask_src : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0 masks irqs; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { k.slots[i].v = 1; } } }"

def maskFlags (s : String) : Option (List Bool) :=
  match lex s with
  | .error _ => none
  | .ok toks =>
    match parseTopTief toks with
    | .error _ => none
    | .ok items =>
      match elabU (pre108 items) with
      | .error _ => none
      | .ok u => some (u.locks.map (·.masks))

theorem mask_irqs_is_read : maskFlags mask_src = some [true] := by decide +kernel
theorem mask_irqs_lowers : stufe mask_src = "OK" := by decide +kernel
theorem lock_without_mask : maskFlags locks_plain = some [false] := by decide +kernel
theorem other_mask_refused :
    stufe "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0 masks nmi; }"
      = "elab: lock masks something but irqs: no G form" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben3
