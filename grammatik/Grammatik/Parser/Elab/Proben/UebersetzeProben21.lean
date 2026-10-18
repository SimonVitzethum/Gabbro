/-
  File:      Grammatik/Parser/Elab/Proben/UebersetzeProben21.lean
  Subject:   Track P: the loops with a progress assumption. `assume a "..." falsifier s;` is a `D.Annahme` beside the
             memory model's `a10`; `retry L until p bounded n ops progress a on_exceeded h { .. }` is
             `Stmt.retry n p body overflow` (the overflow block is the call of the foreign body `h`), and
             `forever L per_pass bounded n ops on_exceeded h effects { .. } progress a { .. }` is `Stmt.forever`
             at the assumption `a`. The header rides raw in the surface tree and is read again by the lexer.
-/
import Grammatik.Parser.Elab.Proben.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben21

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- A bounded wait on a slot, the overflow named by a `-> never` handler. -/
def retry_ok : String :=
  "module m { table T count 4 { slot { v : u32 in 0 .. 100, } } extern fn zeit() -> never effects { diverges } costs <= 1 ops; assume ok_ \"the cell changes\" falsifier sonde_ok; impl fn f(t0 : ptr<normal, r> T) effects { reads t0.slots } { retry warten0 until t0.slots[0].v == 1 bounded 8 ops progress ok_ on_exceeded zeit effects { reads t0.slots } { } } }"
theorem retry_ok_stufe : stufe retry_ok = "OK" := by decide +kernel

/-- `progress` must name an `assume` item. -/
def retry_unknown_refused : String :=
  "module m { table T count 4 { slot { v : u32 in 0 .. 100, } } extern fn zeit() -> never effects { diverges } costs <= 1 ops; impl fn f(t0 : ptr<normal, r> T) effects { reads t0.slots } { retry warten0 until t0.slots[0].v == 1 bounded 8 ops progress ok_ on_exceeded zeit effects { reads t0.slots } { } } }"
theorem retry_unknown_refused_stufe : stufe retry_unknown_refused = "elab: assumption unknown: ok_" := by decide +kernel

/-- The overflow handler must be a foreign body. -/
def retry_handler_refused : String :=
  "module m { table T count 4 { slot { v : u32 in 0 .. 100, } } assume ok_ \"the cell changes\" falsifier sonde_ok; impl fn zeit() { } impl fn f(t0 : ptr<normal, r> T) effects { reads t0.slots } { retry warten0 until t0.slots[0].v == 1 bounded 8 ops progress ok_ on_exceeded zeit effects { reads t0.slots } { } } }"
theorem retry_handler_refused_stufe : stufe retry_handler_refused = "elab: on_exceeded names no foreign body" := by decide +kernel

/-- The service loop at its assumption. -/
def forever_ok : String :=
  "module m { extern fn zeit() -> never effects { diverges } costs <= 1 ops; extern fn tick() effects { pure } costs <= 1 ops; assume tickt \"the timer ticks\" falsifier sonde_tickt; impl fn f() effects { diverges } { forever dienst per_pass bounded 64 ops on_exceeded zeit effects { pure } progress tickt { tick(); } } }"
theorem forever_ok_stufe : stufe forever_ok = "OK" := by decide +kernel

def forever_unknown_refused : String :=
  "module m { extern fn zeit() -> never effects { diverges } costs <= 1 ops; extern fn tick() effects { pure } costs <= 1 ops; impl fn f() effects { diverges } { forever dienst per_pass bounded 64 ops on_exceeded zeit effects { pure } progress tickt { tick(); } } }"
theorem forever_unknown_refused_stufe : stufe forever_unknown_refused = "elab: assumption unknown: tickt" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben21
