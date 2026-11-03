/-
  File:      Grammatik/Parser/Elab/Proben/UebersetzeProben26.lean
  Subject:   Track P: `syscall` gates as foreign bodies (`D.Ax`), the ABI half (`abi`, `number`, registers,
             `clobbers`, `errors`) being the stub's. A gate with an answer is bound at the top of a body
             (`Endblock.bindAxiom`); a gate with a reason channel (`or R`, `D.agruende`) is handled by
             `let y = g(..) else (e) { .. }` (`Endblock.bindAxiomElse`: the end-block form exists, so the
             handling stands at the top of a body, unlike `bindCallElse`).
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


namespace Gabbro.Grammatik.Parser.UebersetzeProben26

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- A gate with an integer answer. -/
def gate_ok : String :=
  "module m { assume linux_getpid \"getpid answers a pid\" falsifier sonde_getpid; syscall getpid() -> u64 in 1 .. 4194304 abi linux arch x86_64 number 39 regs in { } regs out { rax } clobbers { rcx, r11 } errors { } effects { pure } costs <= 8 ops assume linux_getpid falsifier sonde_getpid; impl fn f() -> u64 in 1 .. 4194304 { let p = getpid(); return p; } }"
theorem gate_ok_stufe : stufe gate_ok = "OK" := by decide +kernel

/-- A fallible gate, its reason matched at the top of a body. -/
def fallible_ok : String :=
  "module m { reason G { Weg = 1 \"weg\" exhaustive } syscall rd() -> u32 in 0 .. 9 or G via sys_rd effects { pure } costs <= 8 ops; syscall sys_rd; impl fn f() -> u32 in 0 .. 9 { let y = rd() else (e) { match e { Weg => { return 0; } } return 0; } return y; } }"
theorem fallible_ok_stufe : stufe fallible_ok = "OK" := by decide +kernel

/-- A bare call of a fallible gate has no form. -/
def fallible_bare_refused : String :=
  "module m { reason G { Weg = 1 \"weg\" exhaustive } syscall rd() -> u32 in 0 .. 9 or G via sys_rd effects { pure } costs <= 8 ops; syscall sys_rd; impl fn f() -> u32 in 0 .. 9 { let y = rd(); return y; } }"
theorem fallible_bare_refused_stufe : stufe fallible_bare_refused = "elab: call of a function with a reason channel needs `let .. else`" := by decide +kernel

/-- A foreign fallible binder in a continuing block uses `Block.bindAxiomElse`. -/
def foreign_else_block_src : String :=
  "module m { reason G { Weg = 1 \"weg\" exhaustive } extern fn rd() -> u32 in 0 .. 9 or G effects { pure } costs <= 1 ops; impl fn f(c : bool) -> u32 in 0 .. 9 { if c { let y = rd() else (e) { return 0; } return y; } return 1; } }"

theorem bindAxiomElse_block_zeuge : stufe foreign_else_block_src = "OK" := by decide +kernel

/-- A named foreign answer inside an explicit ending branch. -/
def foreign_bind_end_src : String :=
  "module m { extern fn rd() -> u32 in 0 .. 9 effects { pure } costs <= 1 ops; impl fn f(x : u32 in 0 .. 9) -> u32 in 0 .. 9 { narrow x to 0 .. 1 else { let y = rd(); return y; } return x; } }"

theorem bindAxiom_end_zeuge : stufe foreign_bind_end_src = "OK" := by decide +kernel

/-- The discarded value and void-call siblings use the same end-block dispatcher. -/
def foreign_discard_end_src : String :=
  "module m { extern fn rd() -> u32 in 0 .. 9 effects { pure } costs <= 1 ops; extern fn tick() effects { pure } costs <= 1 ops; impl fn f(x : u32 in 0 .. 9) -> u32 in 0 .. 9 { narrow x to 0 .. 1 else { rd(); tick(); return 2; } return x; } }"

theorem axCall_end_zeuge : stufe foreign_discard_end_src = "OK" := by decide +kernel

/-- A foreign binder's own error branch can stand inside another ending branch. -/
def foreign_else_end_src : String :=
  "module m { reason G { Weg = 1 \"weg\" exhaustive } extern fn rd() -> u32 in 0 .. 9 or G effects { pure } costs <= 1 ops; impl fn f(x : u32 in 0 .. 9) -> u32 in 0 .. 9 { narrow x to 0 .. 1 else { let y = rd() else (e) { return 0; } return y; } return x; } }"

theorem bindAxiomElse_end_zeuge : stufe foreign_else_end_src = "OK" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben26
