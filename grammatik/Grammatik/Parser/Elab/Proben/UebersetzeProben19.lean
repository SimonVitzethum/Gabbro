/-
  File:      Grammatik/Parser/Elab/UebersetzeProben19.lean
  Subject:   Track P: arenas as the pair the specification names (`ArenaZucker`): `arena A capacity lo .. hi of T;`
             is a table `A` of `hi` slots with the one field `wert` and the counter static `A#used` over
             `0 .. hi`; `reset A;` is the store of zero into the counter (`Stmt.assignGlob`), `A[i]` the slot
             read of `wert`. `alloc` (`Block.arenaAlloc`, a nested block with an `else`) is not elaborated yet.
-/
import Grammatik.Parser.Elab.Proben.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben19

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- The declaration and a `reset`. -/
def reset_ok : String :=
  "module m { arena R capacity 2 .. 8 of u32; impl fn f() effects { writes R } { reset R; } }"
theorem reset_ok_stufe : stufe reset_ok = "OK" := by decide +kernel

/-- `reset` needs the write right on the arena. -/
def reset_norecht_refused : String :=
  "module m { arena R capacity 2 .. 8 of u32; impl fn f() { reset R; } }"
theorem reset_norecht_refused_stufe : stufe reset_norecht_refused = "lower: write without right" := by decide +kernel

/-- A store into and a read of an element by a literal index. -/
def element_ok : String :=
  "module m { arena R capacity 2 .. 8 of u16; impl fn f() -> u16 effects { reads R, writes R } { R[1] = 5; return R[1]; } }"
theorem element_ok_stufe : stufe element_ok = "OK" := by decide +kernel

/-- An index past the hard bound. -/
def element_count_refused : String :=
  "module m { arena R capacity 2 .. 8 of u16; impl fn f() -> u16 effects { reads R } { return R[8]; } }"
theorem element_count_refused_stufe : stufe element_count_refused = "elab: index outside count" := by decide +kernel

/-- A dynamic ceiling has no G form. -/
def dynamic_refused : String :=
  "module m { arena R capacity 2 .. 8 max 16 of u32; impl fn f() effects { writes R } { reset R; } }"
theorem dynamic_refused_stufe : stufe dynamic_refused = "elab: arena with a dynamic ceiling without G form" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben19
