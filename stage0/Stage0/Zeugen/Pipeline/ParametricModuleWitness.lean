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


namespace Gabbro.Stage0.Pipeline.ParametricModuleWitness
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- One parametric module instantiated twice. The module-template and use
    headers fail the original metadata gate; the expansion gate accepts the
    two expanded instances. -/
def text : String :=
  "module consts[T, N: const u32 in 1 .. 65536] { " ++
  "pub fn get(x: T) -> T effects { pure } { return x; } " ++
  "pub fn cap(x: u32 in 0 .. 100) -> u32 in 0 .. N effects { pure } { return x + x; } } " ++
  "use A = consts::[u8, 400]; use B = consts::[u16, 300]; " ++
  "impl fn main() -> u32 in 0 .. 800 effects { pure } { " ++
  "let a = A::cap(20); let b = B::cap(1); let c = A::get(7); let d = B::get(9); " ++
  "if c == 7 { if d == 9 { return a + b; } return 1; } return 0; }"

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

end Gabbro.Stage0.Pipeline.ParametricModuleWitness
