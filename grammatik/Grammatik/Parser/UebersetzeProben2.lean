/-
  File:      Grammatik/Parser/UebersetzeProben2.lean
  Subject:   Sieve (a), parser lane: witnesses and planted defects of walls 6 (`locks` blocks) and 7
             (`entry` roots). A second file because the kernel probes of one file share one memory
             budget (measured 2026-09-30: the first file alone passes 7 GB with these twelve added).
-/
import Grammatik.Schlusssatz

namespace Gabbro.Grammatik.Parser.UebersetzeProben2

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

/-! WALL 6 (2026-09-30): `locks L { ... }` -- read as flat markers, lowered to `Stmt.locks` with the rank
    rule (`H006`) as a Bool the kernel decides; a nested take of the same lock and a rank that does not
    grow are refused by the lowering, a call that needs the held lock's set is refused by the elaborator. -/

def locks1_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { k.slots[i].v = 1; } } }"
theorem locks1_ok_stufe : stufe locks1_ok = "OK" := by decide +kernel

def locks2_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { k.slots[i].v = 1; k.slots[i].v = 2; } locks L { k.slots[i].v = 3; } } }"
theorem locks2_ok_stufe : stufe locks2_ok = "OK" := by decide +kernel

def locks_nested_same : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { locks L { k.slots[i].v = 1; } } } }"
theorem locks_nested_same_stufe : stufe locks_nested_same = "lower: lower: locks against a held lock of higher or equal rank" := by decide +kernel

def locks_rank_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; lock M protects { } rank 1; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L, locks M } { locks L { locks M { k.slots[i].v = 1; } } } }"
theorem locks_rank_ok_stufe : stufe locks_rank_ok = "OK" := by decide +kernel

def locks_rank_down : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; lock M protects { } rank 1; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L, locks M } { locks M { locks L { k.slots[i].v = 1; } } } }"
theorem locks_rank_down_stufe : stufe locks_rank_down = "lower: lower: locks against a held lock of higher or equal rank" := by decide +kernel

def locks_call_needing_it : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; impl fn g(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { k.slots[i].v = 1; } } impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { g(k, i); } } }"
theorem locks_call_needing_it_stufe : stufe locks_call_needing_it = "elab: Ruf ueber fremde Sperrmenge ohne G-Form" := by decide +kernel


/-! WALL 7 (2026-09-30): `entry ... dispatch f;` -- the dispatch target is a THREAD ROOT of the unit
    (`UProg.wurzeln`, `Einheit.starts` in the bridge). An entry with a handler word (`via`), one that
    dispatches to a function with parameters, and one that names no function of the unit are refused.
    The sources are SHORT on purpose: the kernel lexes them (2.7 GB for a 300-character text). -/

def entry1_ok : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } }"
theorem entry1_ok_stufe : stufe entry1_ok = "OK" := by decide +kernel

def entry_two_ok : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } entry f vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } }"
theorem entry_two_ok_stufe : stufe entry_two_ok = "OK" := by decide +kernel

def entry_via_refused : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 via idt arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } }"
theorem entry_via_refused_stufe : stufe entry_via_refused = "elab: Eingang mit Handler ohne G-Form" := by decide +kernel

def entry_params_refused : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::p; } }"
theorem entry_params_refused_stufe : stufe entry_params_refused = "elab: Eingang auf Funktion mit Parametern ohne G-Form" := by decide +kernel

def entry_unknown_refused : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::nix; } }"
theorem entry_unknown_refused_stufe : stufe entry_unknown_refused = "elab: Eingang: Funktion unbekannt: nix" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben2
