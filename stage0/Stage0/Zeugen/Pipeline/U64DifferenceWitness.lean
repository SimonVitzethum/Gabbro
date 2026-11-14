module
public import Stage0.IRBild
import Grammatik.Kern.Taktik.KernelRfl
import all Init.Data.Repr
import all Init.Data.ToString.Basic
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


namespace Gabbro.Stage0.Pipeline.U64DifferenceWitness
open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000


/-- Full-width inputs require an exact 65-bit signed intermediate before total `eng`.
    The entry calls exercise both sides of bit 63 and subtraction near the unsigned limit. -/
def text : String :=
  "module u64_difference { impl fn difference(a : u64, b : u64) -> u64 { if a >= b { return a - b; } return 0; } impl fn main() -> u64 { let low = difference(18446744073709551615, 9223372036854775808); let high = difference(18446744073709551615, 1); if low == 9223372036854775807 { return high; } return 0; } }"

def candidate : Except String (Emitted text 256) := emit text 256

theorem candidate_present : candidate.toOption.isSome = true := by
  kernel_rfl

def output : Emitted text 256 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 256 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

theorem canonical_source : CanonicalSourceProgram output.compiled :=
  compile_source_program text output.compiled

theorem image_correct [Runner.IR.Kern] [Senke.CloneOK] : output.Correct := output.correct

/-- The actual frontend emits the existing exact subtraction inside total `eng`,
    narrowed to the complete unsigned range rather than a signed-word subset. -/
theorem total_eng_zeuge :
    output.compiled.unit.fns.any (fun fn => fn.body.any (fun
      | .bind "#rel:a:b" (some (0, 18446744073709551615))
          (.eng (.sub (.param "a") (.param "b")) 0 18446744073709551615) => true
      | _ => false)) = true := by
  kernel_rfl

/-- The reversed difference is not justified by the guard. -/
def reversed : String :=
  "module u64_difference { impl fn difference(a : u64, b : u64) -> u64 { if a >= b { return b - a; } return 0; } impl fn main() -> u64 { let answer = difference(7, 3); return answer; } }"

theorem reversed_difference_refused_zeuge : (emit reversed 256).toOption.isSome = false := by
  kernel_rfl

/-- Without a guard, u64 subtraction keeps its potentially negative range. -/
def unguarded : String :=
  "module u64_difference { impl fn difference(a : u64, b : u64) -> u64 { return a - b; } impl fn main() -> u64 { let answer = difference(3, 7); return answer; } }"

theorem unguarded_difference_refused_zeuge : (emit unguarded 256).toOption.isSome = false := by
  kernel_rfl

end Gabbro.Stage0.Pipeline.U64DifferenceWitness
