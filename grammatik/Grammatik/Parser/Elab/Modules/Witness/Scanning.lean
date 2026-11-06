module
public import Grammatik.Parser.Elab.Modules.Witness.Data
import Grammatik.Parser.Stmt.LibraryFixtureScanning
import all Grammatik.Parser.Elab.Proben.RightsConstants.Scanning

namespace Gabbro.Grammatik.Parser.Modules.WitnessPhases
open scoped Gabbro.Grammatik.Parser.UebersetzeProben11.Phases

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- The existing scanner macros infer tokens and steps from the actual lexer.
-- All cuts end at their original whitespace or punctuation boundary.
rights_cut template0 as "module stack[T, N: const u32 in 1 .. 65536] { "
bound_fragment template0 as "module stack[T, N: const u32 in 1 .. 65536] { "
rights_cut template1 as "table Items count N { slot { v: T, } } "
bound_fragment template1 as "table Items count N { slot { v: T, } } "
rights_cut template2 as "static mut top: u32 in 0 .. N = 0; "
bound_fragment template2 as "static mut top: u32 in 0 .. N = 0; "
rights_cut template3 as "pub fn push(x: T) or Full effects { "
bound_fragment template3 as "pub fn push(x: T) or Full effects { "
rights_cut template4 as "writes Items, writes top } costs <= 12 ops "
bound_fragment template4 as "writes Items, writes top } costs <= 12 ops "
rights_cut template5 as "{ Items[0].v = x; top = 1; return; } "
bound_fragment template5 as "{ Items[0].v = x; top = 1; return; } "
rights_cut template6 as "pub fn pop() -> T or Empty effects { "
bound_fragment template6 as "pub fn pop() -> T or Empty effects { "
rights_cut template7 as "reads Items, writes top } costs <= 10 ops "
bound_fragment template7 as "reads Items, writes top } costs <= 10 ops "
rights_cut template8 as "{ top = 0; return Items[0].v; } } "
bound_fragment template8 as "{ top = 0; return Items[0].v; } } "
rights_cut preamble0 as "table Tasks count 128 { slot { v: u8, } } "
bound_fragment preamble0 as "table Tasks count 128 { slot { v: u8, } } "
rights_cut preamble1 as "reason Full { full = 1 \"full\" exhaustive } "
bound_fragment preamble1 as "reason Full { full = 1 \"full\" exhaustive } "
rights_cut preamble2 as "reason Empty { empty = 1 \"empty\" exhaustive } "
bound_fragment preamble2 as "reason Empty { empty = 1 \"empty\" exhaustive } "
rights_cut jobs as "use Jobs = stack::[index into Tasks, 64];"
bound_fragment jobs as "use Jobs = stack::[index into Tasks, 64];"
rights_cut other as " use Other = stack::[index into Tasks, 64];"
bound_fragment other as " use Other = stack::[index into Tasks, 64];"
rights_cut publicUse as "pub use Jobs = stack::[index into Tasks, 64];"
bound_fragment publicUse as "pub use Jobs = stack::[index into Tasks, 64];"
rights_cut recursive0 as "module loop[T] { use Again = loop::[T]; } "
bound_fragment recursive0 as "module loop[T] { use Again = loop::[T]; } "
rights_cut recursive1 as "use Start = loop::[u8];"
bound_fragment recursive1 as "use Start = loop::[u8];"
rights_cut collision0 as "module empty[T] { } "
bound_fragment collision0 as "module empty[T] { } "
rights_cut collision1 as "use A = empty::[u8]; "
bound_fragment collision1 as "use A = empty::[u8]; "
rights_cut collision2 as "use A = empty::[u8];"
bound_fragment collision2 as "use A = empty::[u8];"
rights_cut bad as "use Bad = stack::[index into Tasks, 0];"
bound_fragment bad as "use Bad = stack::[index into Tasks, 0];"

rights_input templateInput : stackTemplateSource
  with_cuts [template0, template1, template2, template3, template4, template5, template6, template7, template8]
  with_text ["module stack[T, N: const u32 in 1 .. 65536] { ", "table Items count N { slot { v: T, } } ", "static mut top: u32 in 0 .. N = 0; ", "pub fn push(x: T) or Full effects { ", "writes Items, writes top } costs <= 12 ops ", "{ Items[0].v = x; top = 1; return; } ", "pub fn pop() -> T or Empty effects { ", "reads Items, writes top } costs <= 10 ops ", "{ top = 0; return Items[0].v; } } "]

rights_input publicUseInput : "pub use Jobs = stack::[index into Tasks, 64];"
  with_cuts [publicUse]
  with_text ["pub use Jobs = stack::[index into Tasks, 64];"]

rights_input stackInput : stackSource
  with_cuts [preamble0, preamble1, preamble2, template0, template1, template2, template3, template4, template5, template6, template7, template8, jobs]
  with_text ["table Tasks count 128 { slot { v: u8, } } ", "reason Full { full = 1 \"full\" exhaustive } ", "reason Empty { empty = 1 \"empty\" exhaustive } ", "module stack[T, N: const u32 in 1 .. 65536] { ", "table Items count N { slot { v: T, } } ", "static mut top: u32 in 0 .. N = 0; ", "pub fn push(x: T) or Full effects { ", "writes Items, writes top } costs <= 12 ops ", "{ Items[0].v = x; top = 1; return; } ", "pub fn pop() -> T or Empty effects { ", "reads Items, writes top } costs <= 10 ops ", "{ top = 0; return Items[0].v; } } ", "use Jobs = stack::[index into Tasks, 64];"]

rights_input twoUsesInput : twoUsesSource
  with_cuts [preamble0, preamble1, preamble2, template0, template1, template2, template3, template4, template5, template6, template7, template8, jobs, other]
  with_text ["table Tasks count 128 { slot { v: u8, } } ", "reason Full { full = 1 \"full\" exhaustive } ", "reason Empty { empty = 1 \"empty\" exhaustive } ", "module stack[T, N: const u32 in 1 .. 65536] { ", "table Items count N { slot { v: T, } } ", "static mut top: u32 in 0 .. N = 0; ", "pub fn push(x: T) or Full effects { ", "writes Items, writes top } costs <= 12 ops ", "{ Items[0].v = x; top = 1; return; } ", "pub fn pop() -> T or Empty effects { ", "reads Items, writes top } costs <= 10 ops ", "{ top = 0; return Items[0].v; } } ", "use Jobs = stack::[index into Tasks, 64];", " use Other = stack::[index into Tasks, 64];"]

rights_input recursiveInput : ("module loop[T] { use Again = loop::[T]; } " ++ "use Start = loop::[u8];")
  with_cuts [recursive0, recursive1]
  with_text ["module loop[T] { use Again = loop::[T]; } ", "use Start = loop::[u8];"]

rights_input collisionInput : "module empty[T] { } use A = empty::[u8]; use A = empty::[u8];"
  with_cuts [collision0, collision1, collision2]
  with_text ["module empty[T] { } ", "use A = empty::[u8]; ", "use A = empty::[u8];"]

rights_input badInput : (stackPreamble ++ stackTemplateSource ++ "use Bad = stack::[index into Tasks, 0];")
  with_cuts [preamble0, preamble1, preamble2, template0, template1, template2, template3, template4, template5, template6, template7, template8, bad]
  with_text ["table Tasks count 128 { slot { v: u8, } } ", "reason Full { full = 1 \"full\" exhaustive } ", "reason Empty { empty = 1 \"empty\" exhaustive } ", "module stack[T, N: const u32 in 1 .. 65536] { ", "table Items count N { slot { v: T, } } ", "static mut top: u32 in 0 .. N = 0; ", "pub fn push(x: T) or Full effects { ", "writes Items, writes top } costs <= 12 ops ", "{ Items[0].v = x; top = 1; return; } ", "pub fn pop() -> T or Empty effects { ", "reads Items, writes top } costs <= 10 ops ", "{ top = 0; return Items[0].v; } } ", "use Bad = stack::[index into Tasks, 0];"]

end Gabbro.Grammatik.Parser.Modules.WitnessPhases
