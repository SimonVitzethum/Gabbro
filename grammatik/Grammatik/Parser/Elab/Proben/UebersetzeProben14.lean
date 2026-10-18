/-
  File:      Grammatik/Parser/Elab/UebersetzeProben14.lean
  Subject:   Track P: statics under a lock (`gbraucht`, `ggeteilt`), from source text. `lock L protects { s }` names
             a static as a carrier; a read or a write of `s` needs `Held(L)` (`Expr.glob`/`Stmt.assignGlob` carry
             `gdarf`), and the lowering refuses an access without it. Table-free sources (kernel memory).
-/
import Grammatik.Parser.Elab.Proben.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben14

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- A write and a read of a guarded static inside the lock. -/
def locked_ok : String :=
  "module m { static mut s : u32 in 0 .. 100 = 7; lock L protects { s } rank 0 held <= 100 ops; impl fn f() effects { reads s, writes s, locks L } { locks L { s = 3; let x : u32 = s; } } }"
theorem locked_ok_stufe : stufe locked_ok = "OK" := by decide +kernel

/-- The same write outside the lock: the model has no `gdarf` proof for it. -/
def unlocked_refused : String :=
  "module m { static mut s : u32 in 0 .. 100 = 7; lock L protects { s } rank 0 held <= 100 ops; impl fn f() effects { writes s } { s = 3; } }"
theorem unlocked_refused_stufe : stufe unlocked_refused = "lower: access without held guard" := by
  decide +kernel

/-- A read outside the lock. -/
def read_refused : String :=
  "module m { static mut s : u32 in 0 .. 100 = 7; lock L protects { s } rank 0 held <= 100 ops; impl fn f() effects { reads s } { let x : u32 = s; } }"
theorem read_refused_stufe : stufe read_refused = "lower: access without held guard" := by
  decide +kernel

/-- A guard that names neither a table, a field nor a static. -/
def unknown_refused : String :=
  "module m { static mut s : u32 = 7; lock L protects { t } rank 0 held <= 100 ops; impl fn f() { } }"
theorem unknown_refused_stufe : stufe unknown_refused = "elab: guard unknown: t" := by decide +kernel

/-- A static no lock names stays free (the declaration of before). -/
def free_ok : String :=
  "module m { static mut s : u32 in 0 .. 100 = 7; static mut r : u32 in 0 .. 100 = 7; lock L protects { s } rank 0 held <= 100 ops; impl fn f() effects { writes r } { r = 3; } }"
theorem free_ok_stufe : stufe free_ok = "OK" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben14
