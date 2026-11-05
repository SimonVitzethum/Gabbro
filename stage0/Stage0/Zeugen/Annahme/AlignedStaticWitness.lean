module
public import Stage0.SourceWitness
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
import all Init.Data.String.Intercalate
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

namespace Gabbro.Stage0.AlignedStaticWitness

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

variable [RootNativeFloat.Hardware]

local instance kernel : Runner.IR.Kern := { toHardware := inferInstance, ans := fun _ _ _ _ => True }

def text : String :=
  "module aligned16_probe { static VALUE : u32 = 1 aligned 16; impl fn main() -> u64 in 0 .. 100 { return 23; } }"

def candidate : Except String (Emitted text 64) := emit text 64

/-- An aligned static elaborates to an image: alignment without a section is
    laid out on the common grid, not refused. -/
theorem candidate_present : candidate.toOption.isSome = true := by decide +kernel

def output : Emitted text 64 := candidate.toOption.get candidate_present

theorem globs_one : output.compiled.unit.globs.length = 1 := by decide +kernel

def g0 : Fin output.compiled.unit.globs.length := ⟨0, by rw [globs_one]; decide⟩

/-- The elaborated static keeps its declared alignment of sixteen. -/
theorem align_sixteen : Senke.globAlign output.compiled.unit g0 = 16 := by decide +kernel

/-- The built image base lies on the combined sixteen-grid: the builder aligned it
    up to the required base alignment, which the sixteen-grid divides. -/
theorem base_grid : Nat.lcm 8 16 ∣ output.image.Y.lo := by decide +kernel

/-- The aligned global's absolute address is divisible by sixteen (and eight):
    `placed` holds unconditionally for every successfully built image. -/
theorem addr_aligned : 16 ∣ output.image.Y.ga g0 ∧ 8 ∣ output.image.Y.ga g0 := by
  have hpos : 0 < Senke.globAlign output.compiled.unit g0 := by
    rw [align_sixteen]; decide
  have h := output.placed g0 hpos
  rw [align_sixteen] at h
  exact h

/-- The same image satisfies the inherited execution correctness. -/
theorem image_correct [Senke.CloneOK] : output.Correct := output.correct

end Gabbro.Stage0.AlignedStaticWitness
