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


namespace Gabbro.Stage0.Pipeline.GenericWitness
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- One generic function used at two instantiations. The residual generic
    calls fail the original metadata gate; the expansion gate accepts the
    expanded ordinary callers and instances. -/
def text : String :=
  "module generic_probe { fn identity[T](x: T) -> T effects { pure } { let copy: T = x; return copy; } " ++
  "fn byte_use(x: u8) -> u8 effects { pure } { let value = identity::[u8](x); return value; } " ++
  "fn word_use(x: u16) -> u16 effects { pure } { let value = identity::[u16](x); return value; } " ++
  "impl fn main() -> u8 effects { pure } { let a = byte_use(7); let b = word_use(9); if b == 9 { return a; } return 0; } }"

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

end Gabbro.Stage0.Pipeline.GenericWitness
