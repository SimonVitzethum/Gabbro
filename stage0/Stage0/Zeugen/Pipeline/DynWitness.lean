module
public import Stage0.IRBild
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


namespace Gabbro.Stage0.Pipeline.DynWitness
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A `dyn S` call with two linked implementations. The implementations
    close to a tagged sum before elaboration; the gate accepts the
    expanded unit. -/
def text : String :=
  "table Circles count 4 { slot { r: u64, } } " ++
  "table Rects count 4 { slot { r: u64, } } " ++
  "spec Shape[T; effects E] { fn area(s: T) -> u64 " ++
  "ensures result >= 1 effects { E } costs <= 50 ops; } " ++
  "impl Shape[index into Circles; effects { reads Circles }] { " ++
  "fn area(s: index into Circles) -> u64 ensures result >= 1 " ++
  "effects { reads Circles } costs <= 20 ops { return 1; } } " ++
  "impl Shape[index into Rects; effects { reads Rects }] { " ++
  "fn area(s: index into Rects) -> u64 ensures result >= 1 " ++
  "effects { reads Rects } costs <= 20 ops { return 1; } } " ++
  "table Scene count 256 { slot { s: dyn Shape effects { reads Circles, reads Rects }, } } " ++
  "impl fn main() -> u64 effects { reads Circles, reads Rects, reads Scene, writes Scene } { " ++
  "traverse k over slots of Circles by unvisited touches reads Circles, reads Scene, writes Scene { " ++
  "Scene[0].s = dyn Shape(k); } " ++
  "traverse j over slots of Rects by unvisited touches reads Rects, reads Scene, writes Scene { " ++
  "Scene[1].s = dyn Shape(j); } " ++
  "let a = Shape::area(Scene[0].s); let b = Shape::area(Scene[1].s); return a + b; }"

def candidate : Except String (Emitted text 256) := emit text 256

theorem candidate_present : candidate.toOption.isSome = true := by
  decide +kernel

def output : Emitted text 256 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 256 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

theorem canonical_source : CanonicalSourceProgram output.compiled :=
  compile_source_program text output.compiled

theorem image_correct [Runner.IR.Kern] [Senke.CloneOK] : output.Correct := output.correct

/-- The stored gate certificate for this unit. -/
theorem gate_checked := output.compiled.gateChecked

/-- Gate acceptance ties the source to the expanded unit lowering compiles. -/
theorem gate_ties := output.compiled.expansion_gate

end Gabbro.Stage0.Pipeline.DynWitness
