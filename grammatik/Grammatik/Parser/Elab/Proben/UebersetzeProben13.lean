/-
  File:      Grammatik/Parser/Elab/UebersetzeProben13.lean
  Subject:   Track P: payload-free atomics (`UGlob.atomic`, `Deklaration.atomar`, `Stmt.publish` with the
             empty payload), from source text. Table-free sources (kernel memory). An atomic is read
             without a lock and stored by `A = v publishes nothing;` only where the function declares
             `writes A`; a payload, an `observed by` word and a plain store have no G form.
-/
import Grammatik.Parser.Elab.Proben.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben13

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-- `beispiele/162`: the shared flag, a store and a load on two roots. -/
def flag_ok : String :=
  "module m { atomic S : u32 relaxed; impl fn w() effects { writes S } { S = 7 publishes nothing; } impl fn r() -> u32 effects { reads S } { let n : u32 = S; return n; } concurrent { w, r }; }"
theorem flag_ok_stufe : stufe flag_ok = "OK" := by decide +kernel

/-- A `bool` atomic. -/
def bool_ok : String :=
  "module m { atomic B : bool; impl fn w() effects { writes B } { B = true publishes nothing; } }"
theorem bool_ok_stufe : stufe bool_ok = "OK" := by decide +kernel

/-- The store needs the declared effect. -/
def undeclared_refused : String :=
  "module m { atomic S : u32 relaxed; impl fn w() { S = 7 publishes nothing; } }"
theorem undeclared_refused_stufe : stufe undeclared_refused = "lower: write without right" := by
  decide +kernel

/-- A plain store to an atomic is no store of the model. -/
def plain_refused : String :=
  "module m { atomic S : u32 relaxed; impl fn w() effects { writes S } { S = 7; } }"
theorem plain_refused_stufe : stufe plain_refused = "elab: plain write to an atomic without G form" := by
  decide +kernel

/-- A payload is the publish/await hand-off, which the goal theorem does not cover. -/
def payload_refused : String :=
  "module m { table T count 1 { slot { v : u32, } } atomic S : u32 publishes { T.slots }; impl fn w() { } }"
theorem payload_refused_stufe : stufe payload_refused = "elab: atomic with a payload without G form" := by
  decide +kernel

/-- `publishes` at a plain static is refused. -/
def static_refused : String :=
  "module m { static mut N : u32 = 0; impl fn w() effects { writes N } { N = 7 publishes nothing; } }"
theorem static_refused_stufe : stufe static_refused = "elab: publishes without an atomic without G form" := by
  decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben13
