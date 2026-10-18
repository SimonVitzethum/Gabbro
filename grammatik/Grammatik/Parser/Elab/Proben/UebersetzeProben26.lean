/-
  File:      Grammatik/Parser/Elab/Proben/UebersetzeProben26.lean
  Subject:   Track P: `syscall` gates as foreign bodies (`D.Ax`), the ABI half (`abi`, `number`, registers,
             `clobbers`, `errors`) being the stub's. A gate with an answer is bound at the top of a body
             (`Endblock.bindAxiom`); a gate with a reason channel (`or R`, `D.agruende`) is handled by
             `let y = g(..) else (e) { .. }` (`Endblock.bindAxiomElse`: the end-block form exists, so the
             handling stands at the top of a body, unlike `bindCallElse`).
-/
import Grammatik.Parser.Elab.Proben.UebersetzeProben3

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

end Gabbro.Grammatik.Parser.UebersetzeProben26
