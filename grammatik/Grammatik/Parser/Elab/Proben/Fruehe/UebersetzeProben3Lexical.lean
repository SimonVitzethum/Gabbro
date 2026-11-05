module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3Basis
@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeProben3

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

def entry1_ok : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } }"

def entry_two_ok : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } entry f vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } }"

def entry_via_ok : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 via idt arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } }"

def entry_params_refused : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::p; } }"

def entry_unknown_refused : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::nix; } }"

def locks_plain : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; impl fn w() { } }"

def conc_ok : String :=
  "module m { impl fn w() { } impl fn v() { } concurrent { w, v }; }"

def conc_first : String :=
  "module m { impl fn w() { } impl fn v() { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::v; } concurrent { w }; }"

def conc_args_ok : String :=
  "module m { impl fn p(i : u32 in 0 .. 1, b : bool) { } concurrent { p(1, true) }; }"

def conc_params_refused : String :=
  "module m { impl fn p(i : u32 in 0 .. 1) { } concurrent { p }; }"

def conc_arg_range_refused : String :=
  "module m { impl fn p(i : u32 in 0 .. 1) { } concurrent { p(2) }; }"

def conc_ptr_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } impl fn p(k : ptr<normal, r> T) { } concurrent { p(&T) }; }"

def conc_ptr_refused : String :=
  "module m { table T count 2 { slot { v : u32, } } table U count 2 { slot { v : u32, } } impl fn p(k : ptr<normal, r> T) { } concurrent { p(&U) }; }"

def conc_unknown_refused : String :=
  "module m { impl fn w() { } concurrent { nix }; }"

def mask_src : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0 masks irqs; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { k.slots[i].v = 1; } } }"

end Gabbro.Grammatik.Parser.UebersetzeProben3
