module
public import Stage0.IRBild
import Grammatik.Kern.Taktik.KernelRfl
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

namespace Gabbro.Stage0.AlignedStaticWitness

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

def text : String :=
  "module aligned16_probe { static VALUE : u32 = 1 aligned 16; impl fn main() -> u64 in 0 .. 100 { return 23; } }"

-- Geometry comes from the accepted canonical builder, independently of
-- native arithmetic, concrete emitted bytes or the selected function body.
private theorem emitted_base_grid {src : String} {K : Nat}
    (emitted : Emitted src K) (grid : Nat)
    (divides : grid ∣ Senke.bodenAusrichtung emitted.compiled.unit) :
    grid ∣ emitted.image.Y.lo := by
  have builder := emitted.emission
  generalize chosen : emitted.image = image at builder ⊢
  simp only [Senke.bild] at builder
  split at builder
  · cases builder
  · next preliminary preliminaryEq =>
    split at builder
    · cases builder
    · next actual actualEq =>
      split at builder
      · next accepted =>
        simp only [Except.ok.injEq] at builder
        rw [← builder]
        exact Nat.dvd_trans divides (Senke.alignUp_dvd _ _ (Senke.boden_pos _))
      · exfalso
        revert builder
        repeat' split
        all_goals intro builder; cases builder


def candidate : Except String (Emitted text 64) := emit text 64

/-- An aligned static elaborates to an image: alignment without a section is
    laid out on the common grid, not refused. -/
theorem candidate_present : candidate.toOption.isSome = true := by
  kernel_rfl

def output : Emitted text 64 := candidate.toOption.get candidate_present

theorem globs_one : output.compiled.unit.globs.length = 1 := by
  kernel_rfl

def g0 : Fin output.compiled.unit.globs.length := ⟨0, by rw [globs_one]; decide⟩

/-- The elaborated static keeps its declared alignment of sixteen. -/
theorem align_sixteen : Senke.globAlign output.compiled.unit g0 = 16 := by
  kernel_rfl

/-- The built image base lies on the combined sixteen-grid: the builder aligned it
    up to the required base alignment, which the sixteen-grid divides. -/
theorem base_grid : Nat.lcm 8 16 ∣ output.image.Y.lo := by
  have positive : 0 < Senke.globAlign output.compiled.unit g0 := by
    rw [align_sixteen]
    decide
  have divides := Senke.boden_teilt output.compiled.unit g0 positive
  rw [align_sixteen] at divides
  exact emitted_base_grid output (Nat.lcm 8 16) divides

/-- The aligned global's absolute address is divisible by sixteen (and eight):
    `placed` holds unconditionally for every successfully built image. -/
theorem addr_aligned : 16 ∣ output.image.Y.ga g0 ∧ 8 ∣ output.image.Y.ga g0 := by
  have hpos : 0 < Senke.globAlign output.compiled.unit g0 := by
    rw [align_sixteen]; decide
  have h := output.placed g0 hpos
  rw [align_sixteen] at h
  exact h

/-- The same image satisfies the inherited execution correctness. -/
theorem image_correct [Runner.IR.Kern] [Senke.CloneOK] : output.Correct := output.correct

end Gabbro.Stage0.AlignedStaticWitness
