module
public import Stage0.SourceWitness
public import Stage0.Zeugen.Annahme.NarrowRequiredWitness
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

namespace Gabbro.Stage0.CapacityRequiredWitness

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

/- Allocation has no separate Stage-0 constructor: the exporter produces
   `narrowRequired`, followed by `assignSlot` and `assignGlob`. `lowB_ok` and
   `lowEnd_ok` dispatch to `blockNarrowRequired_case` and `endNarrowRequired_case`;
   the normal statement proofs cover the two stores. -/

/-- A required end-block allocation, with `stopC 107` on capacity exhaustion
    (the Stage-0 shape of `narrowRequired`, which `Endblock.arenaAllocRequired`
    unfolds to). A full arena is `Logik.kapazitaet`,
    excluded by the caller's `KoerperGutS/SA` duty; the static arena commits
    all its slots. -/
def text : String :=
  "module capacity_probe { arena A capacity 1 .. 2 of u32; impl fn main() -> u64 in 0 .. 100 effects { writes A } { let i = alloc A (0); return 23; } }"

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_present : candidate.toOption.isSome = true := by decide +kernel

def output : Emitted text 64 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 64 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

/-- A required allocation inside an ordinary block, using its bound index. -/
def blockText : String :=
  "module capacity_block { arena A capacity 1 .. 2 of u32; impl fn main() -> u64 in 0 .. 100 effects { writes A } { if true { let i = alloc A (10); return i; } return 23; } }"

/-- Filling the last slot is success, even though the updated counter is the ceiling. -/
def lastText : String :=
  "module capacity_last { arena A capacity 1 .. 2 of u32; impl fn main() -> u64 in 0 .. 100 effects { writes A } { let i = alloc A (10); let j = alloc A (20); return j; } }"

/-- The same last-slot boundary inside an ordinary block. -/
def blockLastText : String :=
  "module capacity_block_last { arena A capacity 1 .. 2 of u32; impl fn main() -> u64 in 0 .. 100 effects { writes A } { if true { let i = alloc A (10); let j = alloc A (20); return j; } return 23; } }"

theorem block_image_zeuge : (emit blockText 64).isOk = true := by decide +kernel

theorem last_image_zeuge : (emit lastText 64).isOk = true := by decide +kernel

theorem block_last_image_zeuge : (emit blockLastText 64).isOk = true := by decide +kernel

/-- Instantiating the source-image theorem keeps the required stop and the
    successful store-and-bump path under the actual compiler's correctness proof. -/
theorem image_correct_zeuge [Runner.IR.Kern] [Senke.CloneOK] : output.Correct :=
  output.correct

/-- The capacity outcome uses the same runtime stop at either nesting level. -/
theorem stop_code_zeuge :
    Senke.logikCode (D := Senke.ControlProbe.D) .kapazitaet = 107 := rfl

/-- The imported range fixtures cover success and capacity failure for both
    generic narrowing arms; allocation reuses those arms after source expansion. -/
theorem narrowing_images_zeuge :
    [2, 3, 7, 8].all (fun n =>
      (Senke.ControlProbe.imageOf (NarrowRequiredWitness.body n)).isOk) = true ∧
    [2, 3, 7, 8].all (fun n =>
      (Senke.ControlProbe.blockImageOf (NarrowRequiredWitness.block n)).isOk) = true :=
  ⟨NarrowRequiredWitness.accepted_end_zeuge, NarrowRequiredWitness.accepted_block_zeuge⟩

end Gabbro.Stage0.CapacityRequiredWitness
